/-
Copyright (c) 2022 Bhavik Mehta, YaÃ«l Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, YaÃ«l Dillies
-/
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Combinatorics.DoubleCounting
import Mathbin.Combinatorics.SetFamily.Shadow
import Mathbin.Data.Rat.Order
import Mathbin.Tactic.Linarith.Default

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `finset.card_div_choose_le_card_shadow_div_choose`: Local Lubell-Yamamoto-Meshalkin inequality.
  The shadow of a set `ð` in a layer takes a greater proportion of its layer than `ð` does.
* `finset.sum_card_slice_div_choose_le_one`: Lubell-Yamamoto-Meshalkin inequality. The sum of
  densities of `ð` in each layer is at most `1` for any antichain `ð`.
* `is_antichain.sperner`: Sperner's theorem. The size of any antichain in `finset Î±` is at most the
  size of the maximal layer of `finset Î±`. It is a corollary of `sum_card_slice_div_choose_le_one`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`ð` is a middle layer.

`falling` could be useful more generally in grade orders.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/


open Finset Nat

open BigOperators FinsetFamily

variable {ð Î± : Type _} [LinearOrderedField ð]

namespace Finset

/-! ### Local LYM inequality -/


section LocalLym

variable [DecidableEq Î±] [Fintype Î±] {ð : Finset (Finset Î±)} {r : â}

/-- The downward **local LYM inequality**, with cancelled denominators. `ð` takes up less of `Î±^(r)`
(the finsets of card `r`) than `âð` takes up of `Î±^(r - 1)`. -/
theorem card_mul_le_card_shadow_mul (hð : (ð : Set (Finset Î±)).Sized r) :
    ð.card * r â¤ ((â ) ð).card * (Fintype.card Î± - r + 1) := by
  refine' card_mul_le_card_mul' (Â· â Â·) (fun s hs => _) fun s hs => _
  Â· rw [â hð hs, â card_image_of_inj_on s.erase_inj_on]
    refine' card_le_of_subset _
    simp_rw [image_subset_iff, mem_bipartite_below]
    exact fun a ha => â¨erase_mem_shadow hs ha, erase_subset _ _â©
    
  refine' le_transâ _ tsub_tsub_le_tsub_add
  rw [â hð.shadow hs, â card_compl, â card_image_of_inj_on (insert_inj_on' _)]
  refine' card_le_of_subset fun t ht => _
  infer_instance
  rw [mem_bipartite_above] at ht
  have : â â ð := by
    rw [â mem_coe, hð.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rwa [shadow_singleton_empty] at hs
  obtain â¨a, ha, rflâ© :=
    exists_eq_insert_iff.2
      â¨ht.2, by
        rw [(sized_shadow_iff this).1 hð.shadow ht.1, hð.shadow hs]â©
  exact mem_image_of_mem _ (mem_compl.2 ha)

/-- The downward **local LYM inequality**. `ð` takes up less of `Î±^(r)` (the finsets of card `r`)
than `âð` takes up of `Î±^(r - 1)`. -/
theorem card_div_choose_le_card_shadow_div_choose (hr : r â  0) (hð : (ð : Set (Finset Î±)).Sized r) :
    (ð.card : ð) / (Fintype.card Î±).choose r â¤ ((â ) ð).card / (Fintype.card Î±).choose (r - 1) := by
  obtain hr' | hr' := lt_or_leâ (Fintype.card Î±) r
  Â· rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
    
  replace hð := card_mul_le_card_shadow_mul hð
  rw [div_le_div_iff] <;> norm_cast
  Â· cases r
    Â· exact (hr rfl).elim
      
    rw [Nat.succ_eq_add_one] at *
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at hð
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert Nat.mul_le_mul_rightâ ((Fintype.card Î±).choose r) hð using 1
    Â· simp [â mul_assoc, â Nat.choose_succ_right_eq]
      exact Or.inl (mul_comm _ _)
      
    Â· simp only [â mul_assoc, â choose_succ_right_eq, â mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
      
    
  Â· exact Nat.choose_pos hr'
    
  Â· exact Nat.choose_pos (r.pred_le.trans hr')
    

end LocalLym

/-! ### LYM inequality -/


section Lym

section Falling

variable [DecidableEq Î±] (k : â) (ð : Finset (Finset Î±))

/-- `falling k ð` is all the finsets of cardinality `k` which are a subset of something in `ð`. -/
def falling : Finset (Finset Î±) :=
  ð.sup <| powersetLen k

variable {ð k} {s : Finset Î±}

theorem mem_falling : s â falling k ð â (â t â ð, s â t) â§ s.card = k := by
  simp_rw [falling, mem_sup, mem_powerset_len, exists_and_distrib_right]

variable (ð k)

theorem sized_falling : (falling k ð : Set (Finset Î±)).Sized k := fun s hs => (mem_falling.1 hs).2

theorem slice_subset_falling : ð # k â falling k ð := fun s hs =>
  mem_falling.2 <| (mem_slice.1 hs).imp_left fun h => â¨s, h, Subset.refl _â©

theorem falling_zero_subset : falling 0 ð â {â} :=
  subset_singleton_iff'.2 fun t ht => card_eq_zero.1 <| sized_falling _ _ ht

theorem slice_union_shadow_falling_succ : ð # k âª (â ) (falling (k + 1) ð) = falling k ð := by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, exists_prop, mem_falling]
  constructor
  Â· rintro (h | â¨s, â¨â¨t, ht, hstâ©, hsâ©, a, ha, rflâ©)
    Â· exact â¨â¨s, h.1, subset.refl _â©, h.2â©
      
    refine' â¨â¨t, ht, (erase_subset _ _).trans hstâ©, _â©
    rw [card_erase_of_mem ha, hs]
    rfl
    
  Â· rintro â¨â¨t, ht, hstâ©, hsâ©
    by_cases' s â ð
    Â· exact Or.inl â¨h, hsâ©
      
    obtain â¨a, ha, hstâ© := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_not_mem h).symm)
    refine' Or.inr â¨insert a s, â¨â¨t, ht, hstâ©, _â©, a, mem_insert_self _ _, erase_insert haâ©
    rw [card_insert_of_not_mem ha, hs]
    

variable {ð k}

/-- The shadow of `falling m ð` is disjoint from the `n`-sized elements of `ð`, thanks to the
antichain property. -/
theorem _root_.is_antichain.disjoint_slice_shadow_falling {m n : â} (hð : IsAntichain (Â· â Â·) (ð : Set (Finset Î±))) :
    Disjoint (ð # m) ((â ) (falling n ð)) :=
  disjoint_right.2 fun s hâ hâ => by
    simp_rw [mem_shadow_iff, exists_prop, mem_falling] at hâ
    obtain â¨s, â¨â¨t, ht, hstâ©, hsâ©, a, ha, rflâ© := hâ
    refine' hð (slice_subset hâ) ht _ ((erase_subset _ _).trans hst)
    rintro rfl
    exact not_mem_erase _ _ (hst ha)

/-- A bound on any top part of the sum in LYM in terms of the size of `falling k ð`. -/
theorem le_card_falling_div_choose [Fintype Î±] (hk : k â¤ Fintype.card Î±)
    (hð : IsAntichain (Â· â Â·) (ð : Set (Finset Î±))) :
    (â r in range (k + 1), ((ð # (Fintype.card Î± - r)).card : ð) / (Fintype.card Î±).choose (Fintype.card Î± - r)) â¤
      (falling (Fintype.card Î± - k) ð).card / (Fintype.card Î±).choose (Fintype.card Î± - k) :=
  by
  induction' k with k ih
  Â· simp only [â tsub_zero, â cast_one, â cast_le, â sum_singleton, â div_one, â choose_self, â range_one]
    exact card_le_of_subset (slice_subset_falling _ _)
    
  rw [succ_eq_add_one] at *
  rw [sum_range_succ, â slice_union_shadow_falling_succ, card_disjoint_union hð.disjoint_slice_shadow_falling, cast_add,
    _root_.add_div, add_commâ]
  rw [â tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
  exact
    add_le_add_left
      ((ih <| le_of_succ_le hk).trans <|
        card_div_choose_le_card_shadow_div_choose (tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' <| sized_falling _ _)
      _

end Falling

variable {ð : Finset (Finset Î±)} {s : Finset Î±} {k : â}

/-- The **Lubell-Yamamoto-Meshalkin inequality**. If `ð` is an antichain, then the sum of the
proportion of elements it takes from each layer is less than `1`. -/
theorem sum_card_slice_div_choose_le_one [Fintype Î±] (hð : IsAntichain (Â· â Â·) (ð : Set (Finset Î±))) :
    (â r in range (Fintype.card Î± + 1), ((ð # r).card : ð) / (Fintype.card Î±).choose r) â¤ 1 := by
  classical
  rw [â sum_flip]
  refine' (le_card_falling_div_choose le_rfl hð).trans _
  rw [div_le_iff] <;> norm_cast
  Â· simpa only [â Nat.sub_self, â one_mulâ, â Nat.choose_zero_right, â falling] using (sized_falling 0 ð).card_le
    
  Â· rw [tsub_self, choose_zero_right]
    exact zero_lt_one
    

end Lym

/-! ### Sperner's theorem -/


/-- **Sperner's theorem**. The size of an antichain in `finset Î±` is bounded by the size of the
maximal layer in `finset Î±`. This precisely means that `finset Î±` is a Sperner order. -/
theorem _root_.is_antichain.sperner [Fintype Î±] {ð : Finset (Finset Î±)}
    (hð : IsAntichain (Â· â Â·) (ð : Set (Finset Î±))) : ð.card â¤ (Fintype.card Î±).choose (Fintype.card Î± / 2) := by
  classical
  suffices (â r in Iic (Fintype.card Î±), ((ð # r).card : â) / (Fintype.card Î±).choose (Fintype.card Î± / 2)) â¤ 1 by
    rwa [â sum_div, â Nat.cast_sum, div_le_one, cast_le, sum_card_slice] at this
    norm_cast
    exact choose_pos (Nat.div_le_selfâ _ _)
  rw [Iic_eq_Icc, â Ico_succ_right, bot_eq_zero, Ico_zero_eq_range]
  refine' (sum_le_sum fun r hr => _).trans (sum_card_slice_div_choose_le_one hð)
  rw [mem_range] at hr
  refine' div_le_div_of_le_left _ _ _ <;> norm_cast
  Â· exact Nat.zero_leâ _
    
  Â· exact choose_pos (lt_succ_iff.1 hr)
    
  Â· exact choose_le_middle _ _
    

end Finset

