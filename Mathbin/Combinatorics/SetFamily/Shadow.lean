/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaรซl Dillies
-/
import Mathbin.Data.Finset.Slice
import Mathbin.Logic.Function.Iterate

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `finset ฮฑ` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

* `finset.shadow`: The shadow of a set family. Everything we can get by removing a new element from
  some set.
* `finset.up_shadow`: The upper shadow of a set family. Everything we can get by adding an element
  to some set.

## Notation

We define notation in locale `finset_family`:
* `โ ๐`: Shadow of `๐`.
* `โโบ ๐`: Upper shadow of `๐`.

We also maintain the convention that `a, b : ฮฑ` are elements of the ground type, `s, t : finset ฮฑ`
are finsets, and `๐, โฌ : finset (finset ฮฑ)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/


open Finset Nat

variable {ฮฑ : Type _}

namespace Finset

section Shadow

variable [DecidableEq ฮฑ] {๐ : Finset (Finset ฮฑ)} {s t : Finset ฮฑ} {a : ฮฑ} {k r : โ}

/-- The shadow of a set family `๐` is all sets we can get by removing one element from any set in
`๐`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get by removing `k`
elements from any set in `๐`. -/
def shadow (๐ : Finset (Finset ฮฑ)) : Finset (Finset ฮฑ) :=
  ๐.sup fun s => s.Image (erase s)

-- mathport name: ยซexprโยป
localized [FinsetFamily] notation:90 "โ " => Finset.shadow

/-- The shadow of the empty set is empty. -/
@[simp]
theorem shadow_empty : (โ ) (โ : Finset (Finset ฮฑ)) = โ :=
  rfl

@[simp]
theorem shadow_singleton_empty : (โ ) ({โ} : Finset (Finset ฮฑ)) = โ :=
  rfl

/-- The shadow is monotone. -/
--TODO: Prove `โ {{a}} = {โ}` quickly using `covers` and `grade_order`
@[mono]
theorem shadow_monotone : Monotone (shadow : Finset (Finset ฮฑ) โ Finset (Finset ฮฑ)) := fun ๐ โฌ => sup_mono

/-- `s` is in the shadow of `๐` iff there is an `t โ ๐` from which we can remove one element to
get `s`. -/
theorem mem_shadow_iff : s โ (โ ) ๐ โ โ t โ ๐, โ a โ t, erase t a = s := by
  simp only [โ shadow, โ mem_sup, โ mem_image]

theorem erase_mem_shadow (hs : s โ ๐) (ha : a โ s) : erase s a โ (โ ) ๐ :=
  mem_shadow_iff.2 โจs, hs, a, ha, rflโฉ

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a ยซexpr โ ยป s)
/-- `t` is in the shadow of `๐` iff we can add an element to it so that the resulting finset is in
`๐`. -/
theorem mem_shadow_iff_insert_mem : s โ (โ ) ๐ โ โ (a : _)(_ : a โ s), insert a s โ ๐ := by
  refine' mem_shadow_iff.trans โจ_, _โฉ
  ยท rintro โจs, hs, a, ha, rflโฉ
    refine' โจa, not_mem_erase a s, _โฉ
    rwa [insert_erase ha]
    
  ยท rintro โจa, ha, hsโฉ
    exact โจinsert a s, hs, a, mem_insert_self _ _, erase_insert haโฉ
    

/-- The shadow of a family of `r`-sets is a family of `r - 1`-sets. -/
protected theorem _root_.set.sized.shadow (h๐ : (๐ : Set (Finset ฮฑ)).Sized r) :
    ((โ ) ๐ : Set (Finset ฮฑ)).Sized (r - 1) := by
  intro A h
  obtain โจA, hA, i, hi, rflโฉ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi, h๐ hA]

theorem sized_shadow_iff (h : โ โ ๐) : ((โ ) ๐ : Set (Finset ฮฑ)).Sized r โ (๐ : Set (Finset ฮฑ)).Sized (r + 1) := by
  refine' โจfun h๐ s hs => _, Set.Sized.shadowโฉ
  obtain โจa, haโฉ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [โ h๐ (erase_mem_shadow hs ha), card_erase_add_one ha]

/-- `s โ โ ๐` iff `s` is exactly one element less than something from `๐` -/
theorem mem_shadow_iff_exists_mem_card_add_one : s โ (โ ) ๐ โ โ t โ ๐, s โ t โง t.card = s.card + 1 := by
  refine' mem_shadow_iff_insert_mem.trans โจ_, _โฉ
  ยท rintro โจa, ha, hsโฉ
    exact โจinsert a s, hs, subset_insert _ _, card_insert_of_not_mem haโฉ
    
  ยท rintro โจt, ht, hst, hโฉ
    obtain โจa, haโฉ : โ a, t \ s = {a} :=
      card_eq_one.1
        (by
          rw [card_sdiff hst, h, add_tsub_cancel_left])
    exact
      โจa, fun hat => not_mem_sdiff_of_mem_right hat ((ha.ge : _ โ _) <| mem_singleton_self a), by
        rwa [insert_eq a s, โ ha, sdiff_union_of_subset hst]โฉ
    

/-- Being in the shadow of `๐` means we have a superset in `๐`. -/
theorem exists_subset_of_mem_shadow (hs : s โ (โ ) ๐) : โ t โ ๐, s โ t :=
  let โจt, ht, hstโฉ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  โจt, ht, hst.1โฉ

/-- `t โ โ^k ๐` iff `t` is exactly `k` elements less than something in `๐`. -/
theorem mem_shadow_iff_exists_mem_card_add : s โ (โ ^[k]) ๐ โ โ t โ ๐, s โ t โง t.card = s.card + k := by
  induction' k with k ih generalizing ๐ s
  ยท refine' โจfun hs => โจs, hs, subset.refl _, rflโฉ, _โฉ
    rintro โจt, ht, hst, hcardโฉ
    rwa [eq_of_subset_of_card_le hst hcard.le]
    
  simp only [โ exists_prop, โ Function.comp_app, โ Function.iterate_succ]
  refine' ih.trans _
  clear ih
  constructor
  ยท rintro โจt, ht, hst, hcardstโฉ
    obtain โจu, hu, htu, hcardtuโฉ := mem_shadow_iff_exists_mem_card_add_one.1 ht
    refine' โจu, hu, hst.trans htu, _โฉ
    rw [hcardtu, hcardst]
    rfl
    
  ยท rintro โจt, ht, hst, hcardโฉ
    obtain โจu, hsu, hut, huโฉ :=
      Finset.exists_intermediate_set k
        (by
          rw [add_commโ, hcard]
          exact le_succ _)
        hst
    rw [add_commโ] at hu
    refine' โจu, mem_shadow_iff_exists_mem_card_add_one.2 โจt, ht, hut, _โฉ, hsu, huโฉ
    rw [hcard, hu]
    rfl
    

end Shadow

open FinsetFamily

section UpShadow

variable [DecidableEq ฮฑ] [Fintype ฮฑ] {๐ : Finset (Finset ฮฑ)} {s t : Finset ฮฑ} {a : ฮฑ} {k r : โ}

/-- The upper shadow of a set family `๐` is all sets we can get by adding one element to any set in
`๐`, and the (`k` times) iterated upper shadow (`up_shadow^[k]`) is all sets we can get by adding
`k` elements from any set in `๐`. -/
def upShadow (๐ : Finset (Finset ฮฑ)) : Finset (Finset ฮฑ) :=
  ๐.sup fun s => sแถ.Image fun a => insert a s

-- mathport name: ยซexprโโบยป
localized [FinsetFamily] notation:90 "โโบ " => Finset.upShadow

/-- The upper shadow of the empty set is empty. -/
@[simp]
theorem up_shadow_empty : (โโบ ) (โ : Finset (Finset ฮฑ)) = โ :=
  rfl

/-- The upper shadow is monotone. -/
@[mono]
theorem up_shadow_monotone : Monotone (upShadow : Finset (Finset ฮฑ) โ Finset (Finset ฮฑ)) := fun ๐ โฌ => sup_mono

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a ยซexpr โ ยป t)
/-- `s` is in the upper shadow of `๐` iff there is an `t โ ๐` from which we can remove one element
to get `s`. -/
theorem mem_up_shadow_iff : s โ (โโบ ) ๐ โ โ t โ ๐, โ (a : _)(_ : a โ t), insert a t = s := by
  simp_rw [up_shadow, mem_sup, mem_image, exists_prop, mem_compl]

theorem insert_mem_up_shadow (hs : s โ ๐) (ha : a โ s) : insert a s โ (โโบ ) ๐ :=
  mem_up_shadow_iff.2 โจs, hs, a, ha, rflโฉ

/-- The upper shadow of a family of `r`-sets is a family of `r + 1`-sets. -/
protected theorem _root_.set.sized.up_shadow (h๐ : (๐ : Set (Finset ฮฑ)).Sized r) :
    ((โโบ ) ๐ : Set (Finset ฮฑ)).Sized (r + 1) := by
  intro A h
  obtain โจA, hA, i, hi, rflโฉ := mem_up_shadow_iff.1 h
  rw [card_insert_of_not_mem hi, h๐ hA]

/-- `t` is in the upper shadow of `๐` iff we can remove an element from it so that the resulting
finset is in `๐`. -/
theorem mem_up_shadow_iff_erase_mem : s โ (โโบ ) ๐ โ โ a โ s, s.erase a โ ๐ := by
  refine' mem_up_shadow_iff.trans โจ_, _โฉ
  ยท rintro โจs, hs, a, ha, rflโฉ
    refine' โจa, mem_insert_self a s, _โฉ
    rwa [erase_insert ha]
    
  ยท rintro โจa, ha, hsโฉ
    exact โจs.erase a, hs, a, not_mem_erase _ _, insert_erase haโฉ
    

/-- `s โ โโบ ๐` iff `s` is exactly one element less than something from `๐`. -/
theorem mem_up_shadow_iff_exists_mem_card_add_one : s โ (โโบ ) ๐ โ โ t โ ๐, t โ s โง t.card + 1 = s.card := by
  refine' mem_up_shadow_iff_erase_mem.trans โจ_, _โฉ
  ยท rintro โจa, ha, hsโฉ
    exact โจs.erase a, hs, erase_subset _ _, card_erase_add_one haโฉ
    
  ยท rintro โจt, ht, hts, hโฉ
    obtain โจa, haโฉ : โ a, s \ t = {a} :=
      card_eq_one.1
        (by
          rw [card_sdiff hts, โ h, add_tsub_cancel_left])
    refine' โจa, sdiff_subset _ _ ((ha.ge : _ โ _) <| mem_singleton_self a), _โฉ
    rwa [โ sdiff_singleton_eq_erase, โ ha, sdiff_sdiff_eq_self hts]
    

/-- Being in the upper shadow of `๐` means we have a superset in `๐`. -/
theorem exists_subset_of_mem_up_shadow (hs : s โ (โโบ ) ๐) : โ t โ ๐, t โ s :=
  let โจt, ht, hts, _โฉ := mem_up_shadow_iff_exists_mem_card_add_one.1 hs
  โจt, ht, htsโฉ

/-- `t โ โ^k ๐` iff `t` is exactly `k` elements more than something in `๐`. -/
theorem mem_up_shadow_iff_exists_mem_card_add : s โ (โโบ ^[k]) ๐ โ โ t โ ๐, t โ s โง t.card + k = s.card := by
  induction' k with k ih generalizing ๐ s
  ยท refine' โจfun hs => โจs, hs, subset.refl _, rflโฉ, _โฉ
    rintro โจt, ht, hst, hcardโฉ
    rwa [โ eq_of_subset_of_card_le hst hcard.ge]
    
  simp only [โ exists_prop, โ Function.comp_app, โ Function.iterate_succ]
  refine' ih.trans _
  clear ih
  constructor
  ยท rintro โจt, ht, hts, hcardstโฉ
    obtain โจu, hu, hut, hcardtuโฉ := mem_up_shadow_iff_exists_mem_card_add_one.1 ht
    refine' โจu, hu, hut.trans hts, _โฉ
    rw [โ hcardst, โ hcardtu, add_right_commโ]
    rfl
    
  ยท rintro โจt, ht, hts, hcardโฉ
    obtain โจu, htu, hus, huโฉ :=
      Finset.exists_intermediate_set 1
        (by
          rw [add_commโ, โ hcard]
          exact add_le_add_left (zero_lt_succ _) _)
        hts
    rw [add_commโ] at hu
    refine' โจu, mem_up_shadow_iff_exists_mem_card_add_one.2 โจt, ht, htu, hu.symmโฉ, hus, _โฉ
    rw [hu, โ hcard, add_right_commโ]
    rfl
    

@[simp]
theorem shadow_image_compl : ((โ ) ๐).Image compl = (โโบ ) (๐.Image compl) := by
  ext s
  simp only [โ mem_image, โ exists_prop, โ mem_shadow_iff, โ mem_up_shadow_iff]
  constructor
  ยท rintro โจ_, โจs, hs, a, ha, rflโฉ, rflโฉ
    exact โจsแถ, โจs, hs, rflโฉ, a, not_mem_compl.2 ha, compl_erase.symmโฉ
    
  ยท rintro โจ_, โจs, hs, rflโฉ, a, ha, rflโฉ
    exact โจs.erase a, โจs, hs, a, not_mem_compl.1 ha, rflโฉ, compl_eraseโฉ
    

@[simp]
theorem up_shadow_image_compl : ((โโบ ) ๐).Image compl = (โ ) (๐.Image compl) := by
  ext s
  simp only [โ mem_image, โ exists_prop, โ mem_shadow_iff, โ mem_up_shadow_iff]
  constructor
  ยท rintro โจ_, โจs, hs, a, ha, rflโฉ, rflโฉ
    exact โจsแถ, โจs, hs, rflโฉ, a, mem_compl.2 ha, compl_insert.symmโฉ
    
  ยท rintro โจ_, โจs, hs, rflโฉ, a, ha, rflโฉ
    exact โจinsert a s, โจs, hs, a, mem_compl.1 ha, rflโฉ, compl_insertโฉ
    

end UpShadow

end Finset

