/-
Copyright (c) 2022 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, YaÃ«l Dillies
-/
import Mathbin.Analysis.Convex.Cone
import Mathbin.Analysis.Convex.Gauge

/-!
# Separation Hahn-Banach theorem

In this file we prove the geometric Hahn-Banach theorem. For any two disjoint convex sets, there
exists a continuous linear functional separating them, geometrically meaning that we can intercalate
a plane between them.

We provide many variations to stricten the result under more assumptions on the convex sets:
* `geometric_hahn_banach_open`: One set is open. Weak separation.
* `geometric_hahn_banach_open_point`, `geometric_hahn_banach_point_open`: One set is open, the
  other is a singleton. Weak separation.
* `geometric_hahn_banach_open_open`: Both sets are open. Semistrict separation.
* `geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_closed_compact`: One set is closed,
  the other one is compact. Strict separation.
* `geometric_hahn_banach_point_closed`, `geometric_hahn_banach_closed_point`: One set is closed, the
  other one is a singleton. Strict separation.
* `geometric_hahn_banach_point_point`: Both sets are singletons. Strict separation.

## TODO

* Eidelheit's theorem
* `convex â s â interior (closure s) â s`
-/


open Set

open Pointwise

variable {ð E : Type _}

/-- Given a set `s` which is a convex neighbourhood of `0` and a point `xâ` outside of it, there is
a continuous linear functional `f` separating `xâ` and `s`, in the sense that it sends `xâ` to 1 and
all of `s` to values strictly below `1`. -/
theorem separate_convex_open_set [SemiNormedGroup E] [NormedSpace â E] {s : Set E} (hsâ : (0 : E) â s)
    (hsâ : Convex â s) (hsâ : IsOpen s) {xâ : E} (hxâ : xâ â s) : â f : E âL[â] â, f xâ = 1 â§ â, â x â s, â, f x < 1 :=
  by
  let f : LinearPmap â E â := LinearPmap.mkSpanSingleton xâ 1 (ne_of_mem_of_not_mem hsâ hxâ).symm
  obtain â¨r, hr, hrsâ© :=
    Metric.mem_nhds_iff.1
      (Filter.inter_mem (hsâ.mem_nhds hsâ) <|
        hsâ.neg.mem_nhds <| by
          rwa [mem_neg, neg_zero])
  obtain â¨Ï, hÏâ, hÏââ© :=
    exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
      (gauge_add_le hsâ <| absorbent_nhds_zero <| hsâ.mem_nhds hsâ) _
  Â· refine' â¨(Ï.mk_continuous râ»Â¹) fun x => _, _, _â©
    Â· rw [Real.norm_eq_abs, abs_le, neg_le, â LinearMap.map_neg]
      nth_rw 0[â norm_neg x]
      suffices â x, Ï x â¤ râ»Â¹ * â¥xâ¥ by
        exact â¨this _, this _â©
      refine' fun x => (hÏâ _).trans _
      rw [â div_eq_inv_mul, â gauge_ball hr]
      exact gauge_mono (absorbent_ball_zero hr) (hrs.trans <| inter_subset_left _ _) x
      
    Â· dsimp'
      rw [â Submodule.coe_mk xâ (Submodule.mem_span_singleton_self _), hÏâ, LinearPmap.mk_span_singleton'_apply_self]
      
    Â· exact fun x hx => (hÏâ x).trans_lt (gauge_lt_one_of_mem_of_open hsâ hsâ hsâ hx)
      
    
  rintro â¨x, hxâ©
  obtain â¨y, rflâ© := Submodule.mem_span_singleton.1 hx
  rw [LinearPmap.mk_span_singleton'_apply]
  simp only [â mul_oneâ, â Algebra.id.smul_eq_mul, â Submodule.coe_mk]
  obtain h | h := le_or_ltâ y 0
  Â· exact h.trans (gauge_nonneg _)
    
  Â· rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h]
    exact
      one_le_gauge_of_not_mem (hsâ.star_convex hsâ)
        ((absorbent_ball_zero hr).Subset <| hrs.trans <| inter_subset_left _ _).Absorbs hxâ
    infer_instance
    

variable [NormedGroup E] [NormedSpace â E] {s t : Set E} {x y : E}

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is open,
there is a continuous linear functional which separates them. -/
theorem geometric_hahn_banach_open (hsâ : Convex â s) (hsâ : IsOpen s) (ht : Convex â t) (disj : Disjoint s t) :
    â (f : E âL[â] â)(u : â), (â, â a â s, â, f a < u) â§ â, â b â t, â, u â¤ f b := by
  obtain rfl | â¨aâ, haââ© := s.eq_empty_or_nonempty
  Â· exact
      â¨0, 0, by
        simp , fun b hb => le_rflâ©
    
  obtain rfl | â¨bâ, hbââ© := t.eq_empty_or_nonempty
  Â· exact
      â¨0, 1, fun a ha => zero_lt_one, by
        simp â©
    
  let xâ := bâ - aâ
  let C := xâ +áµ¥ (s - t)
  have : (0 : E) â C :=
    â¨aâ - bâ, sub_mem_sub haâ hbâ, by
      rw [vadd_eq_add, sub_add_sub_cancel', sub_self]â©
  have : Convex â C := (hsâ.sub ht).vadd _
  have : xâ â C := by
    intro hxâ
    rw [â add_zeroâ xâ] at hxâ
    exact disj.zero_not_mem_sub_set (vadd_mem_vadd_set_iff.1 hxâ)
  obtain â¨f, hfâ, hfââ© := separate_convex_open_set â¹0 â Câº â¹_âº (hsâ.sub_right.vadd _) â¹xâ â Câº
  have : f bâ = f aâ + 1 := by
    simp [hfâ]
  have forall_le : â, â a â s, â, â b â t, â, f a â¤ f b := by
    intro a ha b hb
    have := hfâ (xâ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [â f.map_add, â f.map_sub, â hfâ] at this
    linarith
  refine' â¨f, Inf (f '' t), image_subset_iff.1 (_ : f '' s â Iio (Inf (f '' t))), fun b hb => _â©
  Â· rw [â interior_Iic]
    refine' interior_maximal (image_subset_iff.2 fun a ha => _) (f.is_open_map_of_ne_zero _ _ hsâ)
    Â· exact le_cInf (nonempty.image _ â¨_, hbââ©) (ball_image_of_ball <| forall_le _ ha)
      
    Â· rintro rfl
      simpa using hfâ
      
    
  Â· exact cInf_le â¨f aâ, ball_image_of_ball <| forall_le _ haââ© (mem_image_of_mem _ hb)
    

theorem geometric_hahn_banach_open_point (hsâ : Convex â s) (hsâ : IsOpen s) (disj : x â s) :
    â f : E âL[â] â, â, â a â s, â, f a < f x :=
  let â¨f, s, hs, hxâ© := geometric_hahn_banach_open hsâ hsâ (convex_singleton x) (disjoint_singleton_right.2 disj)
  â¨f, fun a ha => lt_of_lt_of_leâ (hs a ha) (hx x (mem_singleton _))â©

theorem geometric_hahn_banach_point_open (htâ : Convex â t) (htâ : IsOpen t) (disj : x â t) :
    â f : E âL[â] â, â, â b â t, â, f x < f b :=
  let â¨f, hfâ© := geometric_hahn_banach_open_point htâ htâ disj
  â¨-f, by
    simpaâ©

theorem geometric_hahn_banach_open_open (hsâ : Convex â s) (hsâ : IsOpen s) (htâ : Convex â t) (htâ : IsOpen t)
    (disj : Disjoint s t) : â (f : E âL[â] â)(u : â), (â, â a â s, â, f a < u) â§ â, â b â t, â, u < f b := by
  obtain rfl | â¨aâ, haââ© := s.eq_empty_or_nonempty
  Â· exact
      â¨0, -1, by
        simp , fun b hb => by
        norm_numâ©
    
  obtain rfl | â¨bâ, hbââ© := t.eq_empty_or_nonempty
  Â· exact
      â¨0, 1, fun a ha => by
        norm_num, by
        simp â©
    
  obtain â¨f, s, hfâ, hfââ© := geometric_hahn_banach_open hsâ hsâ htâ disj
  have hf : IsOpenMap f := by
    refine' f.is_open_map_of_ne_zero _
    rintro rfl
    exact (hfâ _ haâ).not_le (hfâ _ hbâ)
  refine' â¨f, s, hfâ, image_subset_iff.1 (_ : f '' t â Ioi s)â©
  rw [â interior_Ici]
  refine' interior_maximal (image_subset_iff.2 hfâ) (f.is_open_map_of_ne_zero _ _ htâ)
  rintro rfl
  exact (hfâ _ haâ).not_le (hfâ _ hbâ)

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
compact and `t` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed (hsâ : Convex â s) (hsâ : IsCompact s) (htâ : Convex â t)
    (htâ : IsClosed t) (disj : Disjoint s t) :
    â (f : E âL[â] â)(u v : â), (â, â a â s, â, f a < u) â§ u < v â§ â, â b â t, â, v < f b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  Â· exact
      â¨0, -2, -1, by
        simp , by
        norm_num, fun b hb => by
        norm_numâ©
    
  obtain rfl | ht := t.eq_empty_or_nonempty
  Â· exact
      â¨0, 1, 2, fun a ha => by
        norm_num, by
        norm_num, by
        simp â©
    
  obtain â¨U, V, hU, hV, hUâ, hVâ, sU, tV, disj'â© := disj.exists_open_convexes hsâ hsâ htâ htâ
  obtain â¨f, u, hfâ, hfââ© := geometric_hahn_banach_open_open hUâ hU hVâ hV disj'
  obtain â¨x, hxâ, hxââ© := hsâ.exists_forall_ge hs f.continuous.continuous_on
  have : f x < u := hfâ x (sU hxâ)
  exact
    â¨f, (f x + u) / 2, u, fun a ha => by
      linarith [hxâ a ha], by
      linarith, fun b hb => hfâ b (tV hb)â©

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
closed, and `t` is compact, there is a continuous linear functional which strongly separates them.
-/
theorem geometric_hahn_banach_closed_compact (hsâ : Convex â s) (hsâ : IsClosed s) (htâ : Convex â t)
    (htâ : IsCompact t) (disj : Disjoint s t) :
    â (f : E âL[â] â)(u v : â), (â, â a â s, â, f a < u) â§ u < v â§ â, â b â t, â, v < f b :=
  let â¨f, s, t, hs, st, htâ© := geometric_hahn_banach_compact_closed htâ htâ hsâ hsâ disj.symm
  â¨-f, -t, -s, by
    simpa using ht, by
    simpa using st, by
    simpa using hsâ©

theorem geometric_hahn_banach_point_closed (htâ : Convex â t) (htâ : IsClosed t) (disj : x â t) :
    â (f : E âL[â] â)(u : â), f x < u â§ â, â b â t, â, u < f b :=
  let â¨f, u, v, ha, hst, hbâ© :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton htâ htâ
      (disjoint_singleton_left.2 disj)
  â¨f, v, hst.trans' <| ha x <| mem_singleton _, hbâ©

theorem geometric_hahn_banach_closed_point (hsâ : Convex â s) (hsâ : IsClosed s) (disj : x â s) :
    â (f : E âL[â] â)(u : â), (â, â a â s, â, f a < u) â§ u < f x :=
  let â¨f, s, t, ha, hst, hbâ© :=
    geometric_hahn_banach_closed_compact hsâ hsâ (convex_singleton x) is_compact_singleton
      (disjoint_singleton_right.2 disj)
  â¨f, s, ha, hst.trans <| hb x <| mem_singleton _â©

/-- Special case of `normed_space.eq_iff_forall_dual_eq`. -/
theorem geometric_hahn_banach_point_point (hxy : x â  y) : â f : E âL[â] â, f x < f y := by
  obtain â¨f, s, t, hs, st, htâ© :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton (convex_singleton y)
      is_closed_singleton (disjoint_singleton.2 hxy)
  exact
    â¨f, by
      linarith [hs x rfl, ht y rfl]â©

/-- A closed convex set is the intersection of the halfspaces containing it. -/
theorem Inter_halfspaces_eq (hsâ : Convex â s) (hsâ : IsClosed s) : (â l : E âL[â] â, { x | â y â s, l x â¤ l y }) = s :=
  by
  rw [Set.Inter_set_of]
  refine' Set.Subset.antisymm (fun x hx => _) fun x hx l => â¨x, hx, le_rflâ©
  by_contra
  obtain â¨l, s, hlA, hlâ© := geometric_hahn_banach_closed_point hsâ hsâ h
  obtain â¨y, hy, hxyâ© := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_le le_rfl

