/-
Copyright (c) 2022 YaΓ«l Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YaΓ«l Dillies
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Order.UpperLower

/-!
# Harris-Kleitman inequality

This file proves the Harris-Kleitman inequality. This relates `π.card * β¬.card` and
`2 ^ card Ξ± * (π β© β¬).card` where `π` and `β¬` are upward- or downcard-closed finite families of
finsets. This can be interpreted as saying that any two lower sets (resp. any two upper sets)
correlate in the uniform measure.

## Main declarations

* `finset.non_member_subfamily`: `π.non_member_subfamily a` is the subfamily of sets not containing
  `a`.
* `finset.member_subfamily`: `π.member_subfamily a` is the image of the subfamily of sets
  containing `a` under removing `a`.
* `is_lower_set.le_card_inter_finset`: One form of the Harris-Kleitman inequality.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open BigOperators

variable {Ξ± : Type _} [DecidableEq Ξ±] {π β¬ : Finset (Finset Ξ±)} {s : Finset Ξ±} {a : Ξ±}

namespace Finset

/-- ELements of `π` that do not contain `a`. -/
def nonMemberSubfamily (π : Finset (Finset Ξ±)) (a : Ξ±) : Finset (Finset Ξ±) :=
  π.filter fun s => a β s

/-- Image of the elements of `π` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s β π`. -/
def memberSubfamily (π : Finset (Finset Ξ±)) (a : Ξ±) : Finset (Finset Ξ±) :=
  (π.filter fun s => a β s).Image fun s => erase s a

@[simp]
theorem mem_non_member_subfamily : s β π.nonMemberSubfamily a β s β π β§ a β s :=
  mem_filter

@[simp]
theorem mem_member_subfamily : s β π.memberSubfamily a β insert a s β π β§ a β s := by
  simp_rw [member_subfamily, mem_image, mem_filter]
  refine' β¨_, fun h => β¨insert a s, β¨h.1, mem_insert_self _ _β©, erase_insert h.2β©β©
  rintro β¨s, hs, rflβ©
  rw [insert_erase hs.2]
  exact β¨hs.1, not_mem_erase _ _β©

theorem non_member_subfamily_inter (π β¬ : Finset (Finset Ξ±)) (a : Ξ±) :
    (π β© β¬).nonMemberSubfamily a = π.nonMemberSubfamily a β© β¬.nonMemberSubfamily a :=
  filter_inter_distrib _ _ _

theorem member_subfamily_inter (π β¬ : Finset (Finset Ξ±)) (a : Ξ±) :
    (π β© β¬).memberSubfamily a = π.memberSubfamily a β© β¬.memberSubfamily a := by
  unfold member_subfamily
  rw [filter_inter_distrib, image_inter_of_inj_on _ _ ((erase_inj_on' _).mono _)]
  rw [β coe_union, β filter_union, coe_filter]
  exact Set.inter_subset_right _ _

theorem card_member_subfamily_add_card_non_member_subfamily (π : Finset (Finset Ξ±)) (a : Ξ±) :
    (π.memberSubfamily a).card + (π.nonMemberSubfamily a).card = π.card := by
  rw [member_subfamily, non_member_subfamily, card_image_of_inj_on, filter_card_add_filter_neg_card_eq_card]
  exact (erase_inj_on' _).mono fun s hs => (mem_filter.1 hs).2

end Finset

open Finset

theorem IsLowerSet.non_member_subfamily (h : IsLowerSet (π : Set (Finset Ξ±))) :
    IsLowerSet (π.nonMemberSubfamily a : Set (Finset Ξ±)) := fun s t hts => by
  simp_rw [mem_coe, mem_non_member_subfamily]
  exact And.imp (h hts) (mt <| @hts _)

theorem IsLowerSet.member_subfamily (h : IsLowerSet (π : Set (Finset Ξ±))) :
    IsLowerSet (π.memberSubfamily a : Set (Finset Ξ±)) := by
  rintro s t hts
  simp_rw [mem_coe, mem_member_subfamily]
  exact And.imp (h <| insert_subset_insert _ hts) (mt <| @hts _)

theorem IsLowerSet.member_subfamily_subset_non_member_subfamily (h : IsLowerSet (π : Set (Finset Ξ±))) :
    π.memberSubfamily a β π.nonMemberSubfamily a := fun s => by
  rw [mem_member_subfamily, mem_non_member_subfamily]
  exact And.imp_left (h <| subset_insert _ _)

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
theorem IsLowerSet.le_card_inter_finset' (hπ : IsLowerSet (π : Set (Finset Ξ±))) (hβ¬ : IsLowerSet (β¬ : Set (Finset Ξ±)))
    (hπs : β, β t β π, β, t β s) (hβ¬s : β, β t β β¬, β, t β s) : π.card * β¬.card β€ 2 ^ s.card * (π β© β¬).card := by
  induction' s using Finset.induction with a s hs ih generalizing π β¬
  Β· simp_rw [subset_empty, β subset_singleton_iff', subset_singleton_iff] at hπs hβ¬s
    obtain rfl | rfl := hπs
    Β· simp only [β card_empty, β empty_inter, β mul_zero, β zero_mul]
      
    obtain rfl | rfl := hβ¬s
    Β· simp only [β card_empty, β inter_empty, β mul_zero, β zero_mul]
      
    Β· simp only [β card_empty, β pow_zeroβ, β inter_singleton_of_mem, β mem_singleton, β card_singleton]
      
    
  rw [card_insert_of_not_mem hs, β card_member_subfamily_add_card_non_member_subfamily π a, β
    card_member_subfamily_add_card_non_member_subfamily β¬ a, add_mulβ, mul_addβ, mul_addβ, add_commβ (_ * _),
    add_add_add_commβ]
  refine'
    (add_le_add_right
          (mul_add_mul_le_mul_add_mul (card_le_of_subset hπ.member_subfamily_subset_non_member_subfamily) <|
            card_le_of_subset hβ¬.member_subfamily_subset_non_member_subfamily)
          _).trans
      _
  rw [β two_mul, pow_succβ, mul_assoc]
  have hβ : β π : Finset (Finset Ξ±), (β, β t β π, β, t β insert a s) β β, β t β π.nonMemberSubfamily a, β, t β s := by
    rintro π hπ t ht
    rw [mem_non_member_subfamily] at ht
    exact (subset_insert_iff_of_not_mem ht.2).1 (hπ _ ht.1)
  have hβ : β π : Finset (Finset Ξ±), (β, β t β π, β, t β insert a s) β β, β t β π.memberSubfamily a, β, t β s := by
    rintro π hπ t ht
    rw [mem_member_subfamily] at ht
    exact (subset_insert_iff_of_not_mem ht.2).1 ((subset_insert _ _).trans <| hπ _ ht.1)
  refine' mul_le_mul_left' _ _
  refine'
    (add_le_add (ih hπ.member_subfamily hβ¬.member_subfamily (hβ _ hπs) <| hβ _ hβ¬s) <|
          ih hπ.non_member_subfamily hβ¬.non_member_subfamily (hβ _ hπs) <| hβ _ hβ¬s).trans_eq
      _
  rw [β mul_addβ, β member_subfamily_inter, β non_member_subfamily_inter,
    card_member_subfamily_add_card_non_member_subfamily]

variable [Fintype Ξ±]

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
theorem IsLowerSet.le_card_inter_finset (hπ : IsLowerSet (π : Set (Finset Ξ±))) (hβ¬ : IsLowerSet (β¬ : Set (Finset Ξ±))) :
    π.card * β¬.card β€ 2 ^ Fintype.card Ξ± * (π β© β¬).card :=
  (hπ.le_card_inter_finset' hβ¬ fun _ _ => subset_univ _) fun _ _ => subset_univ _

/-- **Harris-Kleitman inequality**: Upper sets and lower sets of finsets anticorrelate. -/
theorem IsUpperSet.card_inter_le_finset (hπ : IsUpperSet (π : Set (Finset Ξ±))) (hβ¬ : IsLowerSet (β¬ : Set (Finset Ξ±))) :
    2 ^ Fintype.card Ξ± * (π β© β¬).card β€ π.card * β¬.card := by
  rw [β is_lower_set_compl, β coe_compl] at hπ
  have := hπ.le_card_inter_finset hβ¬
  rwa [card_compl, Fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, β mul_tsub, β
    card_sdiff (inter_subset_right _ _), sdiff_inter_self_right, sdiff_compl, _root_.inf_comm] at this

/-- **Harris-Kleitman inequality**: Lower sets and upper sets of finsets anticorrelate. -/
theorem IsLowerSet.card_inter_le_finset (hπ : IsLowerSet (π : Set (Finset Ξ±))) (hβ¬ : IsUpperSet (β¬ : Set (Finset Ξ±))) :
    2 ^ Fintype.card Ξ± * (π β© β¬).card β€ π.card * β¬.card := by
  rw [inter_comm, mul_comm π.card]
  exact hβ¬.card_inter_le_finset hπ

/-- **Harris-Kleitman inequality**: Any two upper sets of finsets correlate. -/
theorem IsUpperSet.le_card_inter_finset (hπ : IsUpperSet (π : Set (Finset Ξ±))) (hβ¬ : IsUpperSet (β¬ : Set (Finset Ξ±))) :
    π.card * β¬.card β€ 2 ^ Fintype.card Ξ± * (π β© β¬).card := by
  rw [β is_lower_set_compl, β coe_compl] at hπ
  have := hπ.card_inter_le_finset hβ¬
  rwa [card_compl, Fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, β mul_tsub, β
    card_sdiff (inter_subset_right _ _), sdiff_inter_self_right, sdiff_compl, _root_.inf_comm] at this
  Β· exact mul_le_mul_left' (card_le_of_subset <| inter_subset_right _ _) _
    
  Β· rw [β Fintype.card_finset]
    exact mul_le_mul_right' (card_le_univ _) _
    

