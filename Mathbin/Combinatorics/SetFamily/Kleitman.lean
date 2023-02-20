/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.set_family.kleitman
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SetFamily.HarrisKleitman
import Mathbin.Combinatorics.SetFamily.Intersecting

/-!
# Kleitman's bound on the size of intersecting families

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An intersecting family on `n` elements has size at most `2ⁿ⁻¹`, so we could naïvely think that two
intersecting families could cover all `2ⁿ` sets. But actually that's not case because for example
none of them can contain the empty set. Intersecting families are in some sense correlated.
Kleitman's bound stipulates that `k` intersecting families cover at most `2ⁿ - 2ⁿ⁻ᵏ` sets.

## Main declarations

* `finset.card_bUnion_le_of_intersecting`: Kleitman's theorem.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open Finset

open Fintype (card)

variable {ι α : Type _} [Fintype α] [DecidableEq α] [Nonempty α]

/- warning: finset.card_bUnion_le_of_intersecting -> Finset.card_bunionᵢ_le_of_intersecting is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Nonempty.{succ u2} α] (s : Finset.{u1} ι) (f : ι -> (Finset.{u2} (Finset.{u2} α))), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Set.Intersecting.{u2} (Finset.{u2} α) (Lattice.toSemilatticeInf.{u2} (Finset.{u2} α) (Finset.lattice.{u2} α (fun (a : α) (b : α) => _inst_2 a b))) (Finset.orderBot.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} (Finset.{u2} α)) (Set.{u2} (Finset.{u2} α)) (Finset.Set.hasCoeT.{u2} (Finset.{u2} α)))) (f i)))) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u2} (Finset.{u2} α) (Finset.bunionᵢ.{u1, u2} ι (Finset.{u2} α) (fun (a : Finset.{u2} α) (b : Finset.{u2} α) => Finset.decidableEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a b) s f)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fintype.card.{u2} α _inst_1)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u2} α _inst_1) (Finset.card.{u1} ι s)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : Nonempty.{succ u1} α] (s : Finset.{u2} ι) (f : ι -> (Finset.{u1} (Finset.{u1} α))), (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Set.Intersecting.{u1} (Finset.{u1} α) (Lattice.toSemilatticeInf.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.toSet.{u1} (Finset.{u1} α) (f i)))) -> (LE.le.{0} Nat instLENat (Finset.card.{u1} (Finset.{u1} α) (Finset.bunionᵢ.{u2, u1} ι (Finset.{u1} α) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a b) s f)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Fintype.card.{u1} α _inst_1)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u1} α _inst_1) (Finset.card.{u2} ι s)))))
Case conversion may be inaccurate. Consider using '#align finset.card_bUnion_le_of_intersecting Finset.card_bunionᵢ_le_of_intersectingₓ'. -/
/-- **Kleitman's theorem**. An intersecting family on `n` elements contains at most `2ⁿ⁻¹` sets, and
each further intersecting family takes at most half of the sets that are in no previous family. -/
theorem Finset.card_bunionᵢ_le_of_intersecting (s : Finset ι) (f : ι → Finset (Finset α))
    (hf : ∀ i ∈ s, (f i : Set (Finset α)).Intersecting) :
    (s.bunionᵢ f).card ≤ 2 ^ card α - 2 ^ (card α - s.card) :=
  by
  obtain hs | hs := le_total (card α) s.card
  · rw [tsub_eq_zero_of_le hs, pow_zero]
    refine'
      (card_le_of_subset <|
            bUnion_subset.2 fun i hi a ha =>
              mem_compl.2 <| not_mem_singleton.2 <| (hf _ hi).ne_bot ha).trans_eq
        _
    rw [card_compl, Fintype.card_finset, card_singleton]
  induction' s using Finset.cons_induction with i s hi ih generalizing f
  · simp
  classical
    set f' : ι → Finset (Finset α) := fun j =>
      if hj : j ∈ cons i s hi then (hf j hj).exists_card_eq.some else ∅ with hf'
    have hf₁ :
      ∀ j,
        j ∈ cons i s hi →
          f j ⊆ f' j ∧ 2 * (f' j).card = 2 ^ card α ∧ (f' j : Set (Finset α)).Intersecting :=
      by
      rintro j hj
      simp_rw [hf', dif_pos hj, ← Fintype.card_finset]
      exact Classical.choose_spec (hf j hj).exists_card_eq
    have hf₂ : ∀ j, j ∈ cons i s hi → IsUpperSet (f' j : Set (Finset α)) :=
      by
      refine' fun j hj => (hf₁ _ hj).2.2.isUpperSet' ((hf₁ _ hj).2.2.is_max_iff_card_eq.2 _)
      rw [Fintype.card_finset]
      exact (hf₁ _ hj).2.1
    refine' (card_le_of_subset <| bUnion_mono fun j hj => (hf₁ _ hj).1).trans _
    nth_rw 1 [cons_eq_insert i]
    rw [bUnion_insert]
    refine' (card_mono <| @le_sup_sdiff _ _ _ <| f' i).trans ((card_union_le _ _).trans _)
    rw [union_sdiff_left, sdiff_eq_inter_compl]
    refine' le_of_mul_le_mul_left _ (pow_pos zero_lt_two <| card α + 1)
    rw [pow_succ', mul_add, mul_assoc, mul_comm _ 2, mul_assoc]
    refine'
      (add_le_add
              ((mul_le_mul_left <| pow_pos (zero_lt_two' ℕ) _).2
                (hf₁ _ <| mem_cons_self _ _).2.2.card_le) <|
            (mul_le_mul_left <| zero_lt_two' ℕ).2 <| IsUpperSet.card_inter_le_finset _ _).trans
        _
    · rw [coe_bUnion]
      exact isUpperSet_unionᵢ₂ fun i hi => hf₂ _ <| subset_cons _ hi
    · rw [coe_compl]
      exact (hf₂ _ <| mem_cons_self _ _).compl
    rw [mul_tsub, card_compl, Fintype.card_finset, mul_left_comm, mul_tsub,
      (hf₁ _ <| mem_cons_self _ _).2.1, two_mul, add_tsub_cancel_left, ← mul_tsub, ← mul_two,
      mul_assoc, ← add_mul, mul_comm]
    refine' mul_le_mul_left' _ _
    refine'
      (add_le_add_left
            (ih ((card_le_of_subset <| subset_cons _).trans hs) _ fun i hi =>
              (hf₁ _ <| subset_cons _ hi).2.2)
            _).trans
        _
    rw [mul_tsub, two_mul, ← pow_succ, ←
      add_tsub_assoc_of_le (pow_le_pow' (one_le_two : (1 : ℕ) ≤ 2) tsub_le_self),
      tsub_add_eq_add_tsub hs, card_cons, add_tsub_add_eq_tsub_right]
#align finset.card_bUnion_le_of_intersecting Finset.card_bunionᵢ_le_of_intersecting

