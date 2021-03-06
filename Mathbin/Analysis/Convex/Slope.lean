/-
Copyright (c) 2021 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Malo JaffrΓ©
-/
import Mathbin.Analysis.Convex.Function

/-!
# Slopes of convex functions

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/


variable {π : Type _} [LinearOrderedField π] {s : Set π} {f : π β π}

/-- If `f : π β π` is convex, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem ConvexOn.slope_mono_adjacent (hf : ConvexOn π s f) {x y z : π} (hx : x β s) (hz : z β s) (hxy : x < y)
    (hyz : y < z) : (f y - f x) / (y - x) β€ (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  rw [β sub_pos] at hxy hxz hyz
  suffices f y / (y - x) + f y / (z - y) β€ f x / (y - x) + f z / (z - y) by
    ring_nf  at thisβ’
    linarith
  set a := (z - y) / (z - x)
  set b := (y - x) / (z - x)
  have hy : a β’ x + b β’ z = y := by
    field_simp
    rw [div_eq_iff] <;> [ring, linarith]
  have key :=
    hf.2 hx hz
      (show 0 β€ a by
        apply div_nonneg <;> linarith)
      (show 0 β€ b by
        apply div_nonneg <;> linarith)
      (show a + b = 1 by
        field_simp
        rw [div_eq_iff] <;> [ring, linarith])
  rw [hy] at key
  replace key := mul_le_mul_of_nonneg_left key hxz.le
  field_simp [β hxy.ne', β hyz.ne', β hxz.ne', β mul_comm (z - x) _]  at keyβ’
  rw [div_le_div_right]
  Β· linarith
    
  Β· nlinarith
    

/-- If `f : π β π` is concave, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem ConcaveOn.slope_anti_adjacent (hf : ConcaveOn π s f) {x y z : π} (hx : x β s) (hz : z β s) (hxy : x < y)
    (hyz : y < z) : (f z - f y) / (z - y) β€ (f y - f x) / (y - x) := by
  rw [β neg_le_neg_iff, β neg_sub_neg (f x), β neg_sub_neg (f y)]
  simp_rw [β Pi.neg_apply, β neg_div, neg_sub]
  exact ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz

/-- If `f : π β π` is strictly convex, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem StrictConvexOn.slope_strict_mono_adjacent (hf : StrictConvexOn π s f) {x y z : π} (hx : x β s) (hz : z β s)
    (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) < (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  have hxz' := hxz.ne
  rw [β sub_pos] at hxy hxz hyz
  suffices f y / (y - x) + f y / (z - y) < f x / (y - x) + f z / (z - y) by
    ring_nf  at thisβ’
    linarith
  set a := (z - y) / (z - x)
  set b := (y - x) / (z - x)
  have hy : a β’ x + b β’ z = y := by
    field_simp
    rw [div_eq_iff] <;> [ring, linarith]
  have key :=
    hf.2 hx hz hxz' (div_pos hyz hxz) (div_pos hxy hxz)
      (show a + b = 1 by
        field_simp
        rw [div_eq_iff] <;> [ring, linarith])
  rw [hy] at key
  replace key := mul_lt_mul_of_pos_left key hxz
  field_simp [β hxy.ne', β hyz.ne', β hxz.ne', β mul_comm (z - x) _]  at keyβ’
  rw [div_lt_div_right]
  Β· linarith
    
  Β· nlinarith
    

/-- If `f : π β π` is strictly concave, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem StrictConcaveOn.slope_anti_adjacent (hf : StrictConcaveOn π s f) {x y z : π} (hx : x β s) (hz : z β s)
    (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) < (f y - f x) / (y - x) := by
  rw [β neg_lt_neg_iff, β neg_sub_neg (f x), β neg_sub_neg (f y)]
  simp_rw [β Pi.neg_apply, β neg_div, neg_sub]
  exact StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz

/-- If for any three points `x < y < z`, the slope of the secant line of `f : π β π` on `[x, y]` is
less than the slope of the secant line of `f` on `[x, z]`, then `f` is convex. -/
theorem convex_on_of_slope_mono_adjacent (hs : Convex π s)
    (hf : β {x y z : π}, x β s β z β s β x < y β y < z β (f y - f x) / (y - x) β€ (f z - f y) / (z - y)) :
    ConvexOn π s f :=
  LinearOrderβ.convex_on_of_lt hs
    (by
      intro x z hx hz hxz a b ha hb hab
      let y := a * x + b * z
      have hxy : x < y := by
        rw [β one_mulβ x, β hab, add_mulβ]
        exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _
      have hyz : y < z := by
        rw [β one_mulβ z, β hab, add_mulβ]
        exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _
      have : (f y - f x) * (z - y) β€ (f z - f y) * (y - x) :=
        (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)
      have hxz : 0 < z - x := sub_pos.2 (hxy.trans hyz)
      have ha : (z - y) / (z - x) = a := by
        rw [eq_comm, β sub_eq_iff_eq_add'] at hab
        simp_rw [div_eq_iff hxz.ne', y, β hab]
        ring
      have hb : (y - x) / (z - x) = b := by
        rw [eq_comm, β sub_eq_iff_eq_add] at hab
        simp_rw [div_eq_iff hxz.ne', y, β hab]
        ring
      rwa [sub_mul, sub_mul, sub_le_iff_le_add', β add_sub_assoc, le_sub_iff_add_le, β mul_addβ, sub_add_sub_cancel, β
        le_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x), mul_comm (f z), ha, hb] at this)

/-- If for any three points `x < y < z`, the slope of the secant line of `f : π β π` on `[x, y]` is
greater than the slope of the secant line of `f` on `[x, z]`, then `f` is concave. -/
theorem concave_on_of_slope_anti_adjacent (hs : Convex π s)
    (hf : β {x y z : π}, x β s β z β s β x < y β y < z β (f z - f y) / (z - y) β€ (f y - f x) / (y - x)) :
    ConcaveOn π s f := by
  rw [β neg_convex_on_iff]
  refine' convex_on_of_slope_mono_adjacent hs fun x y z hx hz hxy hyz => _
  rw [β neg_le_neg_iff]
  simp_rw [β neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
  exact hf hx hz hxy hyz

/-- If for any three points `x < y < z`, the slope of the secant line of `f : π β π` on `[x, y]` is
strictly less than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly convex. -/
theorem strict_convex_on_of_slope_strict_mono_adjacent (hs : Convex π s)
    (hf : β {x y z : π}, x β s β z β s β x < y β y < z β (f y - f x) / (y - x) < (f z - f y) / (z - y)) :
    StrictConvexOn π s f :=
  LinearOrderβ.strict_convex_on_of_lt hs
    (by
      intro x z hx hz hxz a b ha hb hab
      let y := a * x + b * z
      have hxy : x < y := by
        rw [β one_mulβ x, β hab, add_mulβ]
        exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _
      have hyz : y < z := by
        rw [β one_mulβ z, β hab, add_mulβ]
        exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _
      have : (f y - f x) * (z - y) < (f z - f y) * (y - x) :=
        (div_lt_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)
      have hxz : 0 < z - x := sub_pos.2 (hxy.trans hyz)
      have ha : (z - y) / (z - x) = a := by
        rw [eq_comm, β sub_eq_iff_eq_add'] at hab
        simp_rw [div_eq_iff hxz.ne', y, β hab]
        ring
      have hb : (y - x) / (z - x) = b := by
        rw [eq_comm, β sub_eq_iff_eq_add] at hab
        simp_rw [div_eq_iff hxz.ne', y, β hab]
        ring
      rwa [sub_mul, sub_mul, sub_lt_iff_lt_add', β add_sub_assoc, lt_sub_iff_add_lt, β mul_addβ, sub_add_sub_cancel, β
        lt_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x), mul_comm (f z), ha, hb] at this)

/-- If for any three points `x < y < z`, the slope of the secant line of `f : π β π` on `[x, y]` is
strictly greater than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly concave.
-/
theorem strict_concave_on_of_slope_strict_anti_adjacent (hs : Convex π s)
    (hf : β {x y z : π}, x β s β z β s β x < y β y < z β (f z - f y) / (z - y) < (f y - f x) / (y - x)) :
    StrictConcaveOn π s f := by
  rw [β neg_strict_convex_on_iff]
  refine' strict_convex_on_of_slope_strict_mono_adjacent hs fun x y z hx hz hxy hyz => _
  rw [β neg_lt_neg_iff]
  simp_rw [β neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
  exact hf hx hz hxy hyz

/-- A function `f : π β π` is convex iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem convex_on_iff_slope_mono_adjacent :
    ConvexOn π s f β
      Convex π s β§ β β¦x y z : πβ¦, x β s β z β s β x < y β y < z β (f y - f x) / (y - x) β€ (f z - f y) / (z - y) :=
  β¨fun h => β¨h.1, fun x y z => h.slope_mono_adjacentβ©, fun h => convex_on_of_slope_mono_adjacent h.1 h.2β©

/-- A function `f : π β π` is concave iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem concave_on_iff_slope_anti_adjacent :
    ConcaveOn π s f β
      Convex π s β§ β β¦x y z : πβ¦, x β s β z β s β x < y β y < z β (f z - f y) / (z - y) β€ (f y - f x) / (y - x) :=
  β¨fun h => β¨h.1, fun x y z => h.slope_anti_adjacentβ©, fun h => concave_on_of_slope_anti_adjacent h.1 h.2β©

/-- A function `f : π β π` is strictly convex iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strict_convex_on_iff_slope_strict_mono_adjacent :
    StrictConvexOn π s f β
      Convex π s β§ β β¦x y z : πβ¦, x β s β z β s β x < y β y < z β (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
  β¨fun h => β¨h.1, fun x y z => h.slope_strict_mono_adjacentβ©, fun h =>
    strict_convex_on_of_slope_strict_mono_adjacent h.1 h.2β©

/-- A function `f : π β π` is strictly concave iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strict_concave_on_iff_slope_strict_anti_adjacent :
    StrictConcaveOn π s f β
      Convex π s β§ β β¦x y z : πβ¦, x β s β z β s β x < y β y < z β (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
  β¨fun h => β¨h.1, fun x y z => h.slope_anti_adjacentβ©, fun h => strict_concave_on_of_slope_strict_anti_adjacent h.1 h.2β©

