/-
Copyright (c) 2021 Yaรซl Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaรซl Dillies
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Topology.Algebra.Order.Basic

/-!
# Strictly convex sets

This file defines strictly convex sets.

A set is strictly convex if the open segment between any two distinct points lies in its interior.
-/


open Set

open Convex Pointwise

variable {๐ ๐ E F ฮฒ : Type _}

open Function Set

open Convex

section OrderedSemiring

variable [OrderedSemiring ๐] [TopologicalSpace E] [TopologicalSpace F]

section AddCommMonoidโ

variable [AddCommMonoidโ E] [AddCommMonoidโ F]

section HasSmul

variable (๐) [HasSmul ๐ E] [HasSmul ๐ F] (s : Set E)

/-- A set is strictly convex if the open segment between any two distinct points lies is in its
interior. This basically means "convex and not flat on the boundary". -/
def StrictConvex : Prop :=
  s.Pairwise fun x y => โ โฆa b : ๐โฆ, 0 < a โ 0 < b โ a + b = 1 โ a โข x + b โข y โ Interior s

variable {๐ s} {x y : E} {a b : ๐}

theorem strict_convex_iff_open_segment_subset :
    StrictConvex ๐ s โ s.Pairwise fun x y => OpenSegment ๐ x y โ Interior s :=
  forallโ_congr fun x hx y hy hxy => (open_segment_subset_iff ๐).symm

theorem StrictConvex.open_segment_subset (hs : StrictConvex ๐ s) (hx : x โ s) (hy : y โ s) (h : x โ  y) :
    OpenSegment ๐ x y โ Interior s :=
  strict_convex_iff_open_segment_subset.1 hs hx hy h

theorem strict_convex_empty : StrictConvex ๐ (โ : Set E) :=
  pairwise_empty _

theorem strict_convex_univ : StrictConvex ๐ (Univ : Set E) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_univ]
  exact mem_univ _

protected theorem StrictConvex.eq (hs : StrictConvex ๐ s) (hx : x โ s) (hy : y โ s) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (h : a โข x + b โข y โ Interior s) : x = y :=
  (hs.Eq hx hy) fun H => h <| H ha hb hab

protected theorem StrictConvex.inter {t : Set E} (hs : StrictConvex ๐ s) (ht : StrictConvex ๐ t) :
    StrictConvex ๐ (s โฉ t) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact โจhs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb habโฉ

theorem Directed.strict_convex_Union {ฮน : Sort _} {s : ฮน โ Set E} (hdir : Directed (ยท โ ยท) s)
    (hs : โ โฆi : ฮนโฆ, StrictConvex ๐ (s i)) : StrictConvex ๐ (โ i, s i) := by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_Union] at hx hy
  obtain โจi, hxโฉ := hx
  obtain โจj, hyโฉ := hy
  obtain โจk, hik, hjkโฉ := hdir i j
  exact interior_mono (subset_Union s k) (hs (hik hx) (hjk hy) hxy ha hb hab)

theorem DirectedOn.strict_convex_sUnion {S : Set (Set E)} (hdir : DirectedOn (ยท โ ยท) S)
    (hS : โ, โ s โ S, โ, StrictConvex ๐ s) : StrictConvex ๐ (โโS) := by
  rw [sUnion_eq_Union]
  exact (directed_on_iff_directed.1 hdir).strict_convex_Union fun s => hS _ s.2

end HasSmul

section Module

variable [Module ๐ E] [Module ๐ F] {s : Set E}

protected theorem StrictConvex.convex (hs : StrictConvex ๐ s) : Convex ๐ s :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab => interior_subset <| hs hx hy hxy ha hb hab

/-- An open convex set is strictly convex. -/
protected theorem Convex.strict_convex (h : IsOpen s) (hs : Convex ๐ s) : StrictConvex ๐ s :=
  fun x hx y hy _ a b ha hb hab => h.interior_eq.symm โธ hs hx hy ha.le hb.le hab

theorem IsOpen.strict_convex_iff (h : IsOpen s) : StrictConvex ๐ s โ Convex ๐ s :=
  โจStrictConvex.convex, Convex.strict_convex hโฉ

theorem strict_convex_singleton (c : E) : StrictConvex ๐ ({c} : Set E) :=
  pairwise_singleton _ _

theorem Set.Subsingleton.strict_convex (hs : s.Subsingleton) : StrictConvex ๐ s :=
  hs.Pairwise _

theorem StrictConvex.linear_image [Semiringโ ๐] [Module ๐ E] [Module ๐ F] [LinearMap.CompatibleSmul E F ๐ ๐]
    (hs : StrictConvex ๐ s) (f : E โโ[๐] F) (hf : IsOpenMap f) : StrictConvex ๐ (f '' s) := by
  rintro _ โจx, hx, rflโฉ _ โจy, hy, rflโฉ hxy a b ha hb hab
  refine' hf.image_interior_subset _ โจa โข x + b โข y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, _โฉ
  rw [map_add, f.map_smul_of_tower a, f.map_smul_of_tower b]

theorem StrictConvex.is_linear_image (hs : StrictConvex ๐ s) {f : E โ F} (h : IsLinearMap ๐ f) (hf : IsOpenMap f) :
    StrictConvex ๐ (f '' s) :=
  hs.linear_image (h.mk' f) hf

theorem StrictConvex.linear_preimage {s : Set F} (hs : StrictConvex ๐ s) (f : E โโ[๐] F) (hf : Continuous f)
    (hfinj : Injective f) : StrictConvex ๐ (s.Preimage f) := by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage hf _
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

theorem StrictConvex.is_linear_preimage {s : Set F} (hs : StrictConvex ๐ s) {f : E โ F} (h : IsLinearMap ๐ f)
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex ๐ (s.Preimage f) :=
  hs.linear_preimage (h.mk' f) hf hfinj

section LinearOrderedCancelAddCommMonoid

variable [TopologicalSpace ฮฒ] [LinearOrderedCancelAddCommMonoid ฮฒ] [OrderTopology ฮฒ] [Module ๐ ฮฒ] [OrderedSmul ๐ ฮฒ]

theorem strict_convex_Iic (r : ฮฒ) : StrictConvex ๐ (Iic r) := by
  rintro x (hx : x โค r) y (hy : y โค r) hxy a b ha hb hab
  refine' (subset_interior_iff_subset_of_open is_open_Iio).2 Iio_subset_Iic_self _
  rw [โ Convex.combo_self hab r]
  obtain rfl | hx := hx.eq_or_lt
  ยท exact add_lt_add_left (smul_lt_smul_of_pos (hy.lt_of_ne hxy.symm) hb) _
    
  obtain rfl | hy := hy.eq_or_lt
  ยท exact add_lt_add_right (smul_lt_smul_of_pos hx ha) _
    
  ยท exact add_lt_add (smul_lt_smul_of_pos hx ha) (smul_lt_smul_of_pos hy hb)
    

theorem strict_convex_Ici (r : ฮฒ) : StrictConvex ๐ (Ici r) :=
  @strict_convex_Iic ๐ ฮฒแตแต _ _ _ _ _ _ r

theorem strict_convex_Icc (r s : ฮฒ) : StrictConvex ๐ (Icc r s) :=
  (strict_convex_Ici r).inter <| strict_convex_Iic s

theorem strict_convex_Iio (r : ฮฒ) : StrictConvex ๐ (Iio r) :=
  (convex_Iio r).StrictConvex is_open_Iio

theorem strict_convex_Ioi (r : ฮฒ) : StrictConvex ๐ (Ioi r) :=
  (convex_Ioi r).StrictConvex is_open_Ioi

theorem strict_convex_Ioo (r s : ฮฒ) : StrictConvex ๐ (Ioo r s) :=
  (strict_convex_Ioi r).inter <| strict_convex_Iio s

theorem strict_convex_Ico (r s : ฮฒ) : StrictConvex ๐ (Ico r s) :=
  (strict_convex_Ici r).inter <| strict_convex_Iio s

theorem strict_convex_Ioc (r s : ฮฒ) : StrictConvex ๐ (Ioc r s) :=
  (strict_convex_Ioi r).inter <| strict_convex_Iic s

theorem strict_convex_interval (r s : ฮฒ) : StrictConvex ๐ (Interval r s) :=
  strict_convex_Icc _ _

end LinearOrderedCancelAddCommMonoid

end Module

end AddCommMonoidโ

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [HasContinuousAdd E] [Module ๐ E] {s : Set E}

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.preimage_add_right (hs : StrictConvex ๐ s) (z : E) : StrictConvex ๐ ((fun x => z + x) โปยน' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage (continuous_add_left _) _
  have h := hs hx hy ((add_right_injective _).Ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_commโ, โ add_smul, hab, one_smul] at h

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.preimage_add_left (hs : StrictConvex ๐ s) (z : E) : StrictConvex ๐ ((fun x => x + z) โปยน' s) := by
  simpa only [โ add_commโ] using hs.preimage_add_right z

end AddCancelCommMonoid

section AddCommGroupโ

variable [AddCommGroupโ E] [AddCommGroupโ F] [Module ๐ E] [Module ๐ F]

section continuous_add

variable [HasContinuousAdd E] {s t : Set E}

theorem StrictConvex.add (hs : StrictConvex ๐ s) (ht : StrictConvex ๐ t) : StrictConvex ๐ (s + t) := by
  rintro _ โจv, w, hv, hw, rflโฉ _ โจx, y, hx, hy, rflโฉ h a b ha hb hab
  rw [smul_add, smul_add, add_add_add_commโ]
  obtain rfl | hvx := eq_or_ne v x
  ยท refine' interior_mono (add_subset_add (singleton_subset_iff.2 hv) subset.rfl) _
    rw [Convex.combo_self hab, singleton_add]
    exact
      (is_open_map_add_left _).image_interior_subset _ (mem_image_of_mem _ <| ht hw hy (ne_of_apply_ne _ h) ha hb hab)
    
  exact subset_interior_add_left (add_mem_add (hs hv hx hvx ha hb hab) <| ht.convex hw hy ha.le hb.le hab)

theorem StrictConvex.add_left (hs : StrictConvex ๐ s) (z : E) : StrictConvex ๐ ((fun x => z + x) '' s) := by
  simpa only [โ singleton_add] using (strict_convex_singleton z).add hs

theorem StrictConvex.add_right (hs : StrictConvex ๐ s) (z : E) : StrictConvex ๐ ((fun x => x + z) '' s) := by
  simpa only [โ add_commโ] using hs.add_left z

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.vadd (hs : StrictConvex ๐ s) (x : E) : StrictConvex ๐ (x +แตฅ s) :=
  hs.add_left x

end continuous_add

section ContinuousSmul

variable [LinearOrderedField ๐] [Module ๐ E] [HasContinuousConstSmul ๐ E] [LinearMap.CompatibleSmul E E ๐ ๐] {s : Set E}
  {x : E}

theorem StrictConvex.smul (hs : StrictConvex ๐ s) (c : ๐) : StrictConvex ๐ (c โข s) := by
  obtain rfl | hc := eq_or_ne c 0
  ยท exact (subsingleton_zero_smul_set _).StrictConvex
    
  ยท exact hs.linear_image (LinearMap.lsmul _ _ c) (is_open_map_smulโ hc)
    

theorem StrictConvex.affinity [HasContinuousAdd E] (hs : StrictConvex ๐ s) (z : E) (c : ๐) :
    StrictConvex ๐ (z +แตฅ c โข s) :=
  (hs.smul c).vadd z

end ContinuousSmul

end AddCommGroupโ

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring ๐] [TopologicalSpace E]

section AddCommGroupโ

variable [AddCommGroupโ E] [Module ๐ E] [NoZeroSmulDivisors ๐ E] [HasContinuousConstSmul ๐ E] {s : Set E}

theorem StrictConvex.preimage_smul (hs : StrictConvex ๐ s) (c : ๐) : StrictConvex ๐ ((fun z => c โข z) โปยน' s) := by
  classical
  obtain rfl | hc := eq_or_ne c 0
  ยท simp_rw [zero_smul, preimage_const]
    split_ifs
    ยท exact strict_convex_univ
      
    ยท exact strict_convex_empty
      
    
  refine' hs.linear_preimage (LinearMap.lsmul _ _ c) _ (smul_right_injective E hc)
  unfold LinearMap.lsmul LinearMap.mkโ LinearMap.mkโ' LinearMap.mkโ'โโ
  exact continuous_const_smul _

end AddCommGroupโ

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing ๐] [TopologicalSpace E] [TopologicalSpace F]

section AddCommGroupโ

variable [AddCommGroupโ E] [AddCommGroupโ F] [Module ๐ E] [Module ๐ F] {s t : Set E} {x y : E}

theorem StrictConvex.eq_of_open_segment_subset_frontier [Nontrivial ๐] [DenselyOrdered ๐] (hs : StrictConvex ๐ s)
    (hx : x โ s) (hy : y โ s) (h : OpenSegment ๐ x y โ Frontier s) : x = y := by
  obtain โจa, haโ, haโโฉ := DenselyOrdered.dense (0 : ๐) 1 zero_lt_one
  classical
  by_contra hxy
  exact
    (h โจa, 1 - a, haโ, sub_pos_of_lt haโ, add_sub_cancel'_right _ _, rflโฉ).2
      (hs hx hy hxy haโ (sub_pos_of_lt haโ) <| add_sub_cancel'_right _ _)

theorem StrictConvex.add_smul_mem (hs : StrictConvex ๐ s) (hx : x โ s) (hxy : x + y โ s) (hy : y โ  0) {t : ๐}
    (htโ : 0 < t) (htโ : t < 1) : x + t โข y โ Interior s := by
  have h : x + t โข y = (1 - t) โข x + t โข (x + y) := by
    rw [smul_add, โ add_assocโ, โ add_smul, sub_add_cancel, one_smul]
  rw [h]
  refine' hs hx hxy (fun h => hy <| add_left_cancelโ _) (sub_pos_of_lt htโ) htโ (sub_add_cancel _ _)
  exact x
  rw [โ h, add_zeroโ]

theorem StrictConvex.smul_mem_of_zero_mem (hs : StrictConvex ๐ s) (zero_mem : (0 : E) โ s) (hx : x โ s) (hxโ : x โ  0)
    {t : ๐} (htโ : 0 < t) (htโ : t < 1) : t โข x โ Interior s := by
  simpa using
    hs.add_smul_mem zero_mem
      (by
        simpa using hx)
      hxโ htโ htโ

theorem StrictConvex.add_smul_sub_mem (h : StrictConvex ๐ s) (hx : x โ s) (hy : y โ s) (hxy : x โ  y) {t : ๐}
    (htโ : 0 < t) (htโ : t < 1) : x + t โข (y - x) โ Interior s := by
  apply h.open_segment_subset hx hy hxy
  rw [open_segment_eq_image']
  exact mem_image_of_mem _ โจhtโ, htโโฉ

/-- The preimage of a strictly convex set under an affine map is strictly convex. -/
theorem StrictConvex.affine_preimage {s : Set F} (hs : StrictConvex ๐ s) {f : E โแต[๐] F} (hf : Continuous f)
    (hfinj : Injective f) : StrictConvex ๐ (f โปยน' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage hf _
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

/-- The image of a strictly convex set under an affine map is strictly convex. -/
theorem StrictConvex.affine_image (hs : StrictConvex ๐ s) {f : E โแต[๐] F} (hf : IsOpenMap f) :
    StrictConvex ๐ (f '' s) := by
  rintro _ โจx, hx, rflโฉ _ โจy, hy, rflโฉ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      โจa โข x + b โข y, โจhs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply habโฉโฉ

variable [TopologicalAddGroup E]

theorem StrictConvex.neg (hs : StrictConvex ๐ s) : StrictConvex ๐ (-s) :=
  hs.is_linear_preimage IsLinearMap.is_linear_map_neg continuous_id.neg neg_injective

theorem StrictConvex.sub (hs : StrictConvex ๐ s) (ht : StrictConvex ๐ t) : StrictConvex ๐ (s - t) :=
  (sub_eq_add_neg s t).symm โธ hs.add ht.neg

end AddCommGroupโ

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField ๐] [TopologicalSpace E]

section AddCommGroupโ

variable [AddCommGroupโ E] [AddCommGroupโ F] [Module ๐ E] [Module ๐ F] {s : Set E} {x : E}

/-- Alternative definition of set strict convexity, using division. -/
theorem strict_convex_iff_div :
    StrictConvex ๐ s โ
      s.Pairwise fun x y => โ โฆa b : ๐โฆ, 0 < a โ 0 < b โ (a / (a + b)) โข x + (b / (a + b)) โข y โ Interior s :=
  โจfun h x hx y hy hxy a b ha hb => by
    apply h hx hy hxy (div_pos ha <| add_pos ha hb) (div_pos hb <| add_pos ha hb)
    rw [โ add_div]
    exact div_self (add_pos ha hb).ne', fun h x hx y hy hxy a b ha hb hab => by
    convert h hx hy hxy ha hb <;> rw [hab, div_one]โฉ

theorem StrictConvex.mem_smul_of_zero_mem (hs : StrictConvex ๐ s) (zero_mem : (0 : E) โ s) (hx : x โ s) (hxโ : x โ  0)
    {t : ๐} (ht : 1 < t) : x โ t โข Interior s := by
  rw [mem_smul_set_iff_inv_smul_memโ (zero_lt_one.trans ht).ne']
  exact hs.smul_mem_of_zero_mem zero_mem hx hxโ (inv_pos.2 <| zero_lt_one.trans ht) (inv_lt_one ht)

end AddCommGroupโ

end LinearOrderedField

/-!
#### Convex sets in an ordered space

Relates `convex` and `set.ord_connected`.
-/


section

variable [TopologicalSpace E]

/-- A set in a linear ordered field is strictly convex if and only if it is convex. -/
@[simp]
theorem strict_convex_iff_convex [LinearOrderedField ๐] [TopologicalSpace ๐] [OrderTopology ๐] {s : Set ๐} :
    StrictConvex ๐ s โ Convex ๐ s := by
  refine' โจStrictConvex.convex, fun hs => strict_convex_iff_open_segment_subset.2 fun x hx y hy hxy => _โฉ
  obtain h | h := hxy.lt_or_lt
  ยท refine' (open_segment_subset_Ioo h).trans _
    rw [โ interior_Icc]
    exact interior_mono (Icc_subset_segment.trans <| hs.segment_subset hx hy)
    
  ยท rw [open_segment_symm]
    refine' (open_segment_subset_Ioo h).trans _
    rw [โ interior_Icc]
    exact interior_mono (Icc_subset_segment.trans <| hs.segment_subset hy hx)
    

theorem strict_convex_iff_ord_connected [LinearOrderedField ๐] [TopologicalSpace ๐] [OrderTopology ๐] {s : Set ๐} :
    StrictConvex ๐ s โ s.OrdConnected :=
  strict_convex_iff_convex.trans convex_iff_ord_connected

alias strict_convex_iff_ord_connected โ StrictConvex.ord_connected _

end

