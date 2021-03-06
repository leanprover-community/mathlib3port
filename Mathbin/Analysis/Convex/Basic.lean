/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, YaΓ«l Dillies
-/
import Mathbin.Algebra.Order.Invertible
import Mathbin.Algebra.Order.Module
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace
import Mathbin.LinearAlgebra.Ray

/-!
# Convex sets and functions in vector spaces

In a π-vector space, we define the following objects and properties.
* `segment π x y`: Closed segment joining `x` and `y`.
* `open_segment π x y`: Open segment joining `x` and `y`.
* `convex π s`: A set `s` is convex if for any two points `x y β s` it includes `segment π x y`.
* `std_simplex π ΞΉ`: The standard simplex in `ΞΉ β π` (currently requires `fintype ΞΉ`). It is the
  intersection of the positive quadrant with the hyperplane `s.sum = 1`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex.

## Notations

We provide the following notation:
* `[x -[π] y] = segment π x y` in locale `convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `open_segment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopen_segment`/`convex.Ico`/`convex.Ioc`?
-/


variable {π E F Ξ² : Type _}

open LinearMap Set

open BigOperators Classical Pointwise

/-! ### Segment -/


section OrderedSemiring

variable [OrderedSemiring π] [AddCommMonoidβ E]

section HasSmul

variable (π) [HasSmul π E]

/-- Segments in a vector space. -/
def Segment (x y : E) : Set E :=
  { z : E | β (a b : π)(ha : 0 β€ a)(hb : 0 β€ b)(hab : a + b = 1), a β’ x + b β’ y = z }

/-- Open segment in a vector space. Note that `open_segment π x x = {x}` instead of being `β` when
the base semiring has some element between `0` and `1`. -/
def OpenSegment (x y : E) : Set E :=
  { z : E | β (a b : π)(ha : 0 < a)(hb : 0 < b)(hab : a + b = 1), a β’ x + b β’ y = z }

-- mathport name: Β«expr[ -[ ] ]Β»
localized [Convex] notation "[" x " -[" π "] " y "]" => Segment π x y

theorem segment_eq_imageβ (x y : E) :
    [x -[π] y] = (fun p : π Γ π => p.1 β’ x + p.2 β’ y) '' { p | 0 β€ p.1 β§ 0 β€ p.2 β§ p.1 + p.2 = 1 } := by
  simp only [β Segment, β image, β Prod.exists, β mem_set_of_eq, β exists_prop, β and_assoc]

theorem open_segment_eq_imageβ (x y : E) :
    OpenSegment π x y = (fun p : π Γ π => p.1 β’ x + p.2 β’ y) '' { p | 0 < p.1 β§ 0 < p.2 β§ p.1 + p.2 = 1 } := by
  simp only [β OpenSegment, β image, β Prod.exists, β mem_set_of_eq, β exists_prop, β and_assoc]

theorem segment_symm (x y : E) : [x -[π] y] = [y -[π] x] :=
  Set.ext fun z =>
    β¨fun β¨a, b, ha, hb, hab, Hβ© => β¨b, a, hb, ha, (add_commβ _ _).trans hab, (add_commβ _ _).trans Hβ©,
      fun β¨a, b, ha, hb, hab, Hβ© => β¨b, a, hb, ha, (add_commβ _ _).trans hab, (add_commβ _ _).trans Hβ©β©

theorem open_segment_symm (x y : E) : OpenSegment π x y = OpenSegment π y x :=
  Set.ext fun z =>
    β¨fun β¨a, b, ha, hb, hab, Hβ© => β¨b, a, hb, ha, (add_commβ _ _).trans hab, (add_commβ _ _).trans Hβ©,
      fun β¨a, b, ha, hb, hab, Hβ© => β¨b, a, hb, ha, (add_commβ _ _).trans hab, (add_commβ _ _).trans Hβ©β©

theorem open_segment_subset_segment (x y : E) : OpenSegment π x y β [x -[π] y] := fun z β¨a, b, ha, hb, hab, hzβ© =>
  β¨a, b, ha.le, hb.le, hab, hzβ©

theorem segment_subset_iff {x y : E} {s : Set E} :
    [x -[π] y] β s β β a b : π, 0 β€ a β 0 β€ b β a + b = 1 β a β’ x + b β’ y β s :=
  β¨fun H a b ha hb hab => H β¨a, b, ha, hb, hab, rflβ©, fun H z β¨a, b, ha, hb, hab, hzβ© => hz βΈ H a b ha hb habβ©

theorem open_segment_subset_iff {x y : E} {s : Set E} :
    OpenSegment π x y β s β β a b : π, 0 < a β 0 < b β a + b = 1 β a β’ x + b β’ y β s :=
  β¨fun H a b ha hb hab => H β¨a, b, ha, hb, hab, rflβ©, fun H z β¨a, b, ha, hb, hab, hzβ© => hz βΈ H a b ha hb habβ©

end HasSmul

open Convex

section MulActionWithZero

variable (π) [MulActionWithZero π E]

theorem left_mem_segment (x y : E) : x β [x -[π] y] :=
  β¨1, 0, zero_le_one, le_reflβ 0, add_zeroβ 1, by
    rw [zero_smul, one_smul, add_zeroβ]β©

theorem right_mem_segment (x y : E) : y β [x -[π] y] :=
  segment_symm π y x βΈ left_mem_segment π y x

end MulActionWithZero

section Module

variable (π) [Module π E] {x y z : E} {s : Set E}

@[simp]
theorem segment_same (x : E) : [x -[π] x] = {x} :=
  Set.ext fun z =>
    β¨fun β¨a, b, ha, hb, hab, hzβ© => by
      simpa only [β (add_smul _ _ _).symm, β mem_singleton_iff, β hab, β one_smul, β eq_comm] using hz, fun h =>
      mem_singleton_iff.1 h βΈ left_mem_segment π z zβ©

theorem insert_endpoints_open_segment (x y : E) : insert x (insert y (OpenSegment π x y)) = [x -[π] y] := by
  simp only [β subset_antisymm_iff, β insert_subset, β left_mem_segment, β right_mem_segment, β
    open_segment_subset_segment, β true_andβ]
  rintro z β¨a, b, ha, hb, hab, rflβ©
  refine' hb.eq_or_gt.imp _ fun hb' => ha.eq_or_gt.imp _ _
  Β· rintro rfl
    rw [add_zeroβ] at hab
    rw [hab, one_smul, zero_smul, add_zeroβ]
    
  Β· rintro rfl
    rw [zero_addβ] at hab
    rw [hab, one_smul, zero_smul, zero_addβ]
    
  Β· exact fun ha' => β¨a, b, ha', hb', hab, rflβ©
    

variable {π}

theorem mem_open_segment_of_ne_left_right (hx : x β  z) (hy : y β  z) (hz : z β [x -[π] y]) : z β OpenSegment π x y := by
  rw [β insert_endpoints_open_segment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm

theorem open_segment_subset_iff_segment_subset (hx : x β s) (hy : y β s) : OpenSegment π x y β s β [x -[π] y] β s := by
  simp only [insert_endpoints_open_segment, β insert_subset, *, β true_andβ]

end Module

end OrderedSemiring

open Convex

section OrderedRing

variable [OrderedRing π]

section AddCommGroupβ

variable (π) [AddCommGroupβ E] [AddCommGroupβ F] [Module π E] [Module π F]

section DenselyOrdered

variable [Nontrivial π] [DenselyOrdered π]

@[simp]
theorem open_segment_same (x : E) : OpenSegment π x x = {x} :=
  Set.ext fun z =>
    β¨fun β¨a, b, ha, hb, hab, hzβ© => by
      simpa only [add_smul, β mem_singleton_iff, β hab, β one_smul, β eq_comm] using hz, fun h : z = x => by
      obtain β¨a, haβ, haββ© := DenselyOrdered.dense (0 : π) 1 zero_lt_one
      refine' β¨a, 1 - a, haβ, sub_pos_of_lt haβ, add_sub_cancel'_right _ _, _β©
      rw [β add_smul, add_sub_cancel'_right, one_smul, h]β©

end DenselyOrdered

theorem segment_eq_image (x y : E) : [x -[π] y] = (fun ΞΈ : π => (1 - ΞΈ) β’ x + ΞΈ β’ y) '' Icc (0 : π) 1 :=
  Set.ext fun z =>
    β¨fun β¨a, b, ha, hb, hab, hzβ© =>
      β¨b, β¨hb, hab βΈ le_add_of_nonneg_left haβ©,
        hab βΈ
          hz βΈ by
            simp only [β add_sub_cancel]β©,
      fun β¨ΞΈ, β¨hΞΈβ, hΞΈββ©, hzβ© => β¨1 - ΞΈ, ΞΈ, sub_nonneg.2 hΞΈβ, hΞΈβ, sub_add_cancel _ _, hzβ©β©

theorem open_segment_eq_image (x y : E) : OpenSegment π x y = (fun ΞΈ : π => (1 - ΞΈ) β’ x + ΞΈ β’ y) '' Ioo (0 : π) 1 :=
  Set.ext fun z =>
    β¨fun β¨a, b, ha, hb, hab, hzβ© =>
      β¨b, β¨hb, hab βΈ lt_add_of_pos_left _ haβ©,
        hab βΈ
          hz βΈ by
            simp only [β add_sub_cancel]β©,
      fun β¨ΞΈ, β¨hΞΈβ, hΞΈββ©, hzβ© => β¨1 - ΞΈ, ΞΈ, sub_pos.2 hΞΈβ, hΞΈβ, sub_add_cancel _ _, hzβ©β©

theorem segment_eq_image' (x y : E) : [x -[π] y] = (fun ΞΈ : π => x + ΞΈ β’ (y - x)) '' Icc (0 : π) 1 := by
  convert segment_eq_image π x y
  ext ΞΈ
  simp only [β smul_sub, β sub_smul, β one_smul]
  abel

theorem open_segment_eq_image' (x y : E) : OpenSegment π x y = (fun ΞΈ : π => x + ΞΈ β’ (y - x)) '' Ioo (0 : π) 1 := by
  convert open_segment_eq_image π x y
  ext ΞΈ
  simp only [β smul_sub, β sub_smul, β one_smul]
  abel

theorem segment_eq_image_line_map (x y : E) : [x -[π] y] = AffineMap.lineMap x y '' Icc (0 : π) 1 := by
  convert segment_eq_image π x y
  ext
  exact AffineMap.line_map_apply_module _ _ _

theorem open_segment_eq_image_line_map (x y : E) : OpenSegment π x y = AffineMap.lineMap x y '' Ioo (0 : π) 1 := by
  convert open_segment_eq_image π x y
  ext
  exact AffineMap.line_map_apply_module _ _ _

theorem segment_image (f : E ββ[π] F) (a b : E) : f '' [a -[π] b] = [f a -[π] f b] :=
  Set.ext fun x => by
    simp_rw [segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul]

@[simp]
theorem open_segment_image (f : E ββ[π] F) (a b : E) : f '' OpenSegment π a b = OpenSegment π (f a) (f b) :=
  Set.ext fun x => by
    simp_rw [open_segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul]

theorem mem_segment_translate (a : E) {x b c} : a + x β [a + b -[π] a + c] β x β [b -[π] c] := by
  rw [segment_eq_image', segment_eq_image']
  refine' exists_congr fun ΞΈ => and_congr Iff.rfl _
  simp only [β add_sub_add_left_eq_sub, β add_assocβ, β add_right_injβ]

@[simp]
theorem mem_open_segment_translate (a : E) {x b c : E} :
    a + x β OpenSegment π (a + b) (a + c) β x β OpenSegment π b c := by
  rw [open_segment_eq_image', open_segment_eq_image']
  refine' exists_congr fun ΞΈ => and_congr Iff.rfl _
  simp only [β add_sub_add_left_eq_sub, β add_assocβ, β add_right_injβ]

theorem segment_translate_preimage (a b c : E) : (fun x => a + x) β»ΒΉ' [a + b -[π] a + c] = [b -[π] c] :=
  Set.ext fun x => mem_segment_translate π a

theorem open_segment_translate_preimage (a b c : E) :
    (fun x => a + x) β»ΒΉ' OpenSegment π (a + b) (a + c) = OpenSegment π b c :=
  Set.ext fun x => mem_open_segment_translate π a

theorem segment_translate_image (a b c : E) : (fun x => a + x) '' [b -[π] c] = [a + b -[π] a + c] :=
  segment_translate_preimage π a b c βΈ image_preimage_eq _ <| add_left_surjective a

theorem open_segment_translate_image (a b c : E) :
    (fun x => a + x) '' OpenSegment π b c = OpenSegment π (a + b) (a + c) :=
  open_segment_translate_preimage π a b c βΈ image_preimage_eq _ <| add_left_surjective a

end AddCommGroupβ

end OrderedRing

theorem same_ray_of_mem_segment [OrderedCommRing π] [AddCommGroupβ E] [Module π E] {x y z : E} (h : x β [y -[π] z]) :
    SameRay π (x - y) (z - x) := by
  rw [segment_eq_image'] at h
  rcases h with β¨ΞΈ, β¨hΞΈβ, hΞΈββ©, rflβ©
  simpa only [β add_sub_cancel', sub_sub, β sub_smul, β one_smul] using
    (same_ray_nonneg_smul_left (z - y) hΞΈβ).nonneg_smul_right (sub_nonneg.2 hΞΈβ)

section LinearOrderedRing

variable [LinearOrderedRing π]

section AddCommGroupβ

variable [AddCommGroupβ E] [AddCommGroupβ F] [Module π E] [Module π F]

theorem midpoint_mem_segment [Invertible (2 : π)] (x y : E) : midpoint π x y β [x -[π] y] := by
  rw [segment_eq_image_line_map]
  exact β¨β 2, β¨inv_of_nonneg.mpr zero_le_two, inv_of_le_one one_le_twoβ©, rflβ©

theorem mem_segment_sub_add [Invertible (2 : π)] (x y : E) : x β [x - y -[π] x + y] := by
  convert @midpoint_mem_segment π _ _ _ _ _ _ _
  rw [midpoint_sub_add]

theorem mem_segment_add_sub [Invertible (2 : π)] (x y : E) : x β [x + y -[π] x - y] := by
  convert @midpoint_mem_segment π _ _ _ _ _ _ _
  rw [midpoint_add_sub]

@[simp]
theorem left_mem_open_segment_iff [DenselyOrdered π] [NoZeroSmulDivisors π E] {x y : E} :
    x β OpenSegment π x y β x = y := by
  constructor
  Β· rintro β¨a, b, ha, hb, hab, hxβ©
    refine' smul_right_injective _ hb.ne' ((add_right_injβ (a β’ x)).1 _)
    rw [hx, β add_smul, hab, one_smul]
    
  Β· rintro rfl
    rw [open_segment_same]
    exact mem_singleton _
    

@[simp]
theorem right_mem_open_segment_iff [DenselyOrdered π] [NoZeroSmulDivisors π E] {x y : E} :
    y β OpenSegment π x y β x = y := by
  rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

end AddCommGroupβ

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField π]

section AddCommGroupβ

variable [AddCommGroupβ E] [AddCommGroupβ F] [Module π E] [Module π F] {x y z : E}

theorem mem_segment_iff_same_ray : x β [y -[π] z] β SameRay π (x - y) (z - x) := by
  refine' β¨same_ray_of_mem_segment, fun h => _β©
  rcases h.exists_eq_smul_add with β¨a, b, ha, hb, hab, hxy, hzxβ©
  rw [add_commβ, sub_add_sub_cancel] at hxy hzx
  rw [β mem_segment_translate _ (-x), neg_add_selfβ]
  refine' β¨b, a, hb, ha, add_commβ a b βΈ hab, _β©
  rw [β sub_eq_neg_add, β neg_sub, hxy, β sub_eq_neg_add, hzx, smul_neg, smul_comm, neg_add_selfβ]

theorem mem_segment_iff_div :
    x β [y -[π] z] β β a b : π, 0 β€ a β§ 0 β€ b β§ 0 < a + b β§ (a / (a + b)) β’ y + (b / (a + b)) β’ z = x := by
  constructor
  Β· rintro β¨a, b, ha, hb, hab, rflβ©
    use a, b, ha, hb
    simp [*]
    
  Β· rintro β¨a, b, ha, hb, hab, rflβ©
    refine' β¨a / (a + b), b / (a + b), div_nonneg ha hab.le, div_nonneg hb hab.le, _, rflβ©
    rw [β add_div, div_self hab.ne']
    

theorem mem_open_segment_iff_div :
    x β OpenSegment π y z β β a b : π, 0 < a β§ 0 < b β§ (a / (a + b)) β’ y + (b / (a + b)) β’ z = x := by
  constructor
  Β· rintro β¨a, b, ha, hb, hab, rflβ©
    use a, b, ha, hb
    rw [hab, div_one, div_one]
    
  Β· rintro β¨a, b, ha, hb, rflβ©
    have hab : 0 < a + b := add_pos ha hb
    refine' β¨a / (a + b), b / (a + b), div_pos ha hab, div_pos hb hab, _, rflβ©
    rw [β add_div, div_self hab.ne']
    

end AddCommGroupβ

end LinearOrderedField

/-!
#### Segments in an ordered space
Relates `segment`, `open_segment` and `set.Icc`, `set.Ico`, `set.Ioc`, `set.Ioo`
-/


section OrderedSemiring

variable [OrderedSemiring π]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid E] [Module π E] [OrderedSmul π E]

theorem segment_subset_Icc {x y : E} (h : x β€ y) : [x -[π] y] β Icc x y := by
  rintro z β¨a, b, ha, hb, hab, rflβ©
  constructor
  calc x = a β’ x + b β’ x := (Convex.combo_self hab _).symm _ β€ a β’ x + b β’ y :=
      add_le_add_left (smul_le_smul_of_nonneg h hb) _
  calc a β’ x + b β’ y β€ a β’ y + b β’ y := add_le_add_right (smul_le_smul_of_nonneg h ha) _ _ = y :=
      Convex.combo_self hab _

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid E] [Module π E] [OrderedSmul π E]

theorem open_segment_subset_Ioo {x y : E} (h : x < y) : OpenSegment π x y β Ioo x y := by
  rintro z β¨a, b, ha, hb, hab, rflβ©
  constructor
  calc x = a β’ x + b β’ x := (Convex.combo_self hab _).symm _ < a β’ x + b β’ y :=
      add_lt_add_left (smul_lt_smul_of_pos h hb) _
  calc a β’ x + b β’ y < a β’ y + b β’ y := add_lt_add_right (smul_lt_smul_of_pos h ha) _ _ = y := Convex.combo_self hab _

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [Module π E] [OrderedSmul π E] {π}

theorem segment_subset_interval (x y : E) : [x -[π] y] β Interval x y := by
  cases le_totalβ x y
  Β· rw [interval_of_le h]
    exact segment_subset_Icc h
    
  Β· rw [interval_of_ge h, segment_symm]
    exact segment_subset_Icc h
    

theorem Convex.min_le_combo (x y : E) {a b : π} (ha : 0 β€ a) (hb : 0 β€ b) (hab : a + b = 1) : min x y β€ a β’ x + b β’ y :=
  (segment_subset_interval x y β¨_, _, ha, hb, hab, rflβ©).1

theorem Convex.combo_le_max (x y : E) {a b : π} (ha : 0 β€ a) (hb : 0 β€ b) (hab : a + b = 1) : a β’ x + b β’ y β€ max x y :=
  (segment_subset_interval x y β¨_, _, ha, hb, hab, rflβ©).2

end LinearOrderedAddCommMonoid

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField π]

theorem Icc_subset_segment {x y : π} : Icc x y β [x -[π] y] := by
  rintro z β¨hxz, hyzβ©
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  Β· rw [segment_same]
    exact hyz.antisymm hxz
    
  rw [β sub_nonneg] at hxz hyz
  rw [β sub_pos] at h
  refine' β¨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, _, _β©
  Β· rw [β add_div, sub_add_sub_cancel, div_self h.ne']
    
  Β· rw [smul_eq_mul, smul_eq_mul, β mul_div_right_comm, β mul_div_right_comm, β add_div, div_eq_iff h.ne', add_commβ,
      sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub]
    

@[simp]
theorem segment_eq_Icc {x y : π} (h : x β€ y) : [x -[π] y] = Icc x y :=
  (segment_subset_Icc h).antisymm Icc_subset_segment

theorem Ioo_subset_open_segment {x y : π} : Ioo x y β OpenSegment π x y := fun z hz =>
  mem_open_segment_of_ne_left_right hz.1.Ne hz.2.ne' (Icc_subset_segment <| Ioo_subset_Icc_self hz)

@[simp]
theorem open_segment_eq_Ioo {x y : π} (h : x < y) : OpenSegment π x y = Ioo x y :=
  (open_segment_subset_Ioo h).antisymm Ioo_subset_open_segment

theorem segment_eq_Icc' (x y : π) : [x -[π] y] = Icc (min x y) (max x y) := by
  cases le_totalβ x y
  Β· rw [segment_eq_Icc h, max_eq_rightβ h, min_eq_leftβ h]
    
  Β· rw [segment_symm, segment_eq_Icc h, max_eq_leftβ h, min_eq_rightβ h]
    

theorem open_segment_eq_Ioo' {x y : π} (hxy : x β  y) : OpenSegment π x y = Ioo (min x y) (max x y) := by
  cases hxy.lt_or_lt
  Β· rw [open_segment_eq_Ioo h, max_eq_rightβ h.le, min_eq_leftβ h.le]
    
  Β· rw [open_segment_symm, open_segment_eq_Ioo h, max_eq_leftβ h.le, min_eq_rightβ h.le]
    

theorem segment_eq_interval (x y : π) : [x -[π] y] = Interval x y :=
  segment_eq_Icc' _ _

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
theorem Convex.mem_Icc {x y : π} (h : x β€ y) {z : π} :
    z β Icc x y β β a b : π, 0 β€ a β§ 0 β€ b β§ a + b = 1 β§ a * x + b * y = z := by
  rw [β segment_eq_Icc h]
  simp_rw [β exists_prop]
  rfl

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
theorem Convex.mem_Ioo {x y : π} (h : x < y) {z : π} :
    z β Ioo x y β β a b : π, 0 < a β§ 0 < b β§ a + b = 1 β§ a * x + b * y = z := by
  rw [β open_segment_eq_Ioo h]
  simp_rw [β exists_prop]
  rfl

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ioc {x y : π} (h : x < y) {z : π} :
    z β Ioc x y β β a b : π, 0 β€ a β§ 0 < b β§ a + b = 1 β§ a * x + b * y = z := by
  constructor
  Β· rintro hz
    obtain β¨a, b, ha, hb, hab, rflβ© := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    Β· rw [add_zeroβ] at hab
      rw [hab, one_mulβ, zero_mul, add_zeroβ] at hz
      exact (hz.1.Ne rfl).elim
      
    Β· exact β¨a, b, ha, hb', hab, rflβ©
      
    
  Β· rintro β¨a, b, ha, hb, hab, rflβ©
    obtain rfl | ha' := ha.eq_or_lt
    Β· rw [zero_addβ] at hab
      rwa [hab, one_mulβ, zero_mul, zero_addβ, right_mem_Ioc]
      
    Β· exact Ioo_subset_Ioc_self ((Convex.mem_Ioo h).2 β¨a, b, ha', hb, hab, rflβ©)
      
    

/-- A point is in an `Ico` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ico {x y : π} (h : x < y) {z : π} :
    z β Ico x y β β a b : π, 0 < a β§ 0 β€ b β§ a + b = 1 β§ a * x + b * y = z := by
  constructor
  Β· rintro hz
    obtain β¨a, b, ha, hb, hab, rflβ© := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    Β· rw [zero_addβ] at hab
      rw [hab, one_mulβ, zero_mul, zero_addβ] at hz
      exact (hz.2.Ne rfl).elim
      
    Β· exact β¨a, b, ha', hb, hab, rflβ©
      
    
  Β· rintro β¨a, b, ha, hb, hab, rflβ©
    obtain rfl | hb' := hb.eq_or_lt
    Β· rw [add_zeroβ] at hab
      rwa [hab, one_mulβ, zero_mul, add_zeroβ, left_mem_Ico]
      
    Β· exact Ioo_subset_Ico_self ((Convex.mem_Ioo h).2 β¨a, b, ha, hb', hab, rflβ©)
      
    

end LinearOrderedField

/-! ### Convexity of sets -/


section OrderedSemiring

variable [OrderedSemiring π]

section AddCommMonoidβ

variable [AddCommMonoidβ E] [AddCommMonoidβ F]

section HasSmul

variable (π) [HasSmul π E] [HasSmul π F] (s : Set E)

/-- Convexity of sets. -/
def Convex : Prop :=
  β β¦x y : Eβ¦, x β s β y β s β β β¦a b : πβ¦, 0 β€ a β 0 β€ b β a + b = 1 β a β’ x + b β’ y β s

variable {π s}

theorem convex_iff_segment_subset : Convex π s β β β¦x yβ¦, x β s β y β s β [x -[π] y] β s :=
  forallβ_congrβ fun x y hx hy => (segment_subset_iff _).symm

theorem Convex.segment_subset (h : Convex π s) {x y : E} (hx : x β s) (hy : y β s) : [x -[π] y] β s :=
  convex_iff_segment_subset.1 h hx hy

theorem Convex.open_segment_subset (h : Convex π s) {x y : E} (hx : x β s) (hy : y β s) : OpenSegment π x y β s :=
  (open_segment_subset_segment π x y).trans (h.segment_subset hx hy)

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
theorem convex_iff_pointwise_add_subset : Convex π s β β β¦a b : πβ¦, 0 β€ a β 0 β€ b β a + b = 1 β a β’ s + b β’ s β s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w β¨au, bv, β¨u, hu, rflβ©, β¨v, hv, rflβ©, rflβ©
      exact hA hu hv ha hb hab)
    fun h x y hx hy a b ha hb hab => (h ha hb hab) (Set.add_mem_add β¨_, hx, rflβ© β¨_, hy, rflβ©)

alias convex_iff_pointwise_add_subset β Convex.set_combo_subset _

theorem convex_empty : Convex π (β : Set E) := fun x y => False.elim

theorem convex_univ : Convex π (Set.Univ : Set E) := fun _ _ _ _ _ _ _ _ _ => trivialβ

theorem Convex.inter {t : Set E} (hs : Convex π s) (ht : Convex π t) : Convex π (s β© t) :=
  fun x y (hx : x β s β© t) (hy : y β s β© t) a b (ha : 0 β€ a) (hb : 0 β€ b) (hab : a + b = 1) =>
  β¨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb habβ©

theorem convex_sInter {S : Set (Set E)} (h : β, β s β S, β, Convex π s) : Convex π (ββ S) :=
  fun x y hx hy a b ha hb hab s hs => h s hs (hx s hs) (hy s hs) ha hb hab

theorem convex_Inter {ΞΉ : Sort _} {s : ΞΉ β Set E} (h : β i, Convex π (s i)) : Convex π (β i, s i) :=
  sInter_range s βΈ convex_sInter <| forall_range_iff.2 h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem convex_Interβ {ΞΉ : Sort _} {ΞΊ : ΞΉ β Sort _} {s : β i, ΞΊ i β Set E} (h : β i j, Convex π (s i j)) :
    Convex π (β (i) (j), s i j) :=
  convex_Inter fun i => convex_Inter <| h i

theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex π s) (ht : Convex π t) : Convex π (s ΓΛ’ t) := by
  intro x y hx hy a b ha hb hab
  apply mem_prod.2
  exact β¨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab, ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb habβ©

theorem convex_pi {ΞΉ : Type _} {E : ΞΉ β Type _} [β i, AddCommMonoidβ (E i)] [β i, HasSmul π (E i)] {s : Set ΞΉ}
    {t : β i, Set (E i)} (ht : β i, Convex π (t i)) : Convex π (s.pi t) := fun x y hx hy a b ha hb hab i hi =>
  ht i (hx i hi) (hy i hi) ha hb hab

theorem Directed.convex_Union {ΞΉ : Sort _} {s : ΞΉ β Set E} (hdir : Directed (Β· β Β·) s)
    (hc : β β¦i : ΞΉβ¦, Convex π (s i)) : Convex π (β i, s i) := by
  rintro x y hx hy a b ha hb hab
  rw [mem_Union] at hx hyβ’
  obtain β¨i, hxβ© := hx
  obtain β¨j, hyβ© := hy
  obtain β¨k, hik, hjkβ© := hdir i j
  exact β¨k, hc (hik hx) (hjk hy) ha hb habβ©

theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (Β· β Β·) c)
    (hc : β β¦A : Set Eβ¦, A β c β Convex π A) : Convex π (ββc) := by
  rw [sUnion_eq_Union]
  exact (directed_on_iff_directed.1 hdir).convex_Union fun A => hc A.2

end HasSmul

section Module

variable [Module π E] [Module π F] {s : Set E}

theorem convex_iff_open_segment_subset : Convex π s β β β¦x yβ¦, x β s β y β s β OpenSegment π x y β s :=
  convex_iff_segment_subset.trans <| forallβ_congrβ fun x y hx hy => (open_segment_subset_iff_segment_subset hx hy).symm

theorem convex_iff_forall_pos :
    Convex π s β β β¦x yβ¦, x β s β y β s β β β¦a b : πβ¦, 0 < a β 0 < b β a + b = 1 β a β’ x + b β’ y β s :=
  convex_iff_open_segment_subset.trans <| forallβ_congrβ fun x y hx hy => open_segment_subset_iff π

theorem convex_iff_pairwise_pos :
    Convex π s β s.Pairwise fun x y => β β¦a b : πβ¦, 0 < a β 0 < b β a + b = 1 β a β’ x + b β’ y β s := by
  refine' convex_iff_forall_pos.trans β¨fun h x hx y hy _ => h hx hy, _β©
  intro h x y hx hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  Β· rwa [Convex.combo_self hab]
    
  Β· exact h hx hy hxy ha hb hab
    

protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex π s :=
  convex_iff_pairwise_pos.mpr (h.Pairwise _)

theorem convex_singleton (c : E) : Convex π ({c} : Set E) :=
  subsingleton_singleton.Convex

theorem convex_segment (x y : E) : Convex π [x -[π] y] := by
  rintro p q β¨ap, bp, hap, hbp, habp, rflβ© β¨aq, bq, haq, hbq, habq, rflβ© a b ha hb hab
  refine'
    β¨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), _, _β©
  Β· rw [add_add_add_commβ, β mul_addβ, β mul_addβ, habp, habq, mul_oneβ, mul_oneβ, hab]
    
  Β· simp_rw [add_smul, mul_smul, smul_add]
    exact add_add_add_commβ _ _ _ _
    

theorem convex_open_segment (a b : E) : Convex π (OpenSegment π a b) := by
  rw [convex_iff_open_segment_subset]
  rintro p q β¨ap, bp, hap, hbp, habp, rflβ© β¨aq, bq, haq, hbq, habq, rflβ© z β¨a, b, ha, hb, hab, rflβ©
  refine'
    β¨a * ap + b * aq, a * bp + b * bq, add_pos (mul_pos ha hap) (mul_pos hb haq),
      add_pos (mul_pos ha hbp) (mul_pos hb hbq), _, _β©
  Β· rw [add_add_add_commβ, β mul_addβ, β mul_addβ, habp, habq, mul_oneβ, mul_oneβ, hab]
    
  Β· simp_rw [add_smul, mul_smul, smul_add]
    exact add_add_add_commβ _ _ _ _
    

theorem Convex.linear_image (hs : Convex π s) (f : E ββ[π] F) : Convex π (f '' s) := by
  intro x y hx hy a b ha hb hab
  obtain β¨x', hx', rflβ© := mem_image_iff_bex.1 hx
  obtain β¨y', hy', rflβ© := mem_image_iff_bex.1 hy
  exact
    β¨a β’ x' + b β’ y', hs hx' hy' ha hb hab, by
      rw [f.map_add, f.map_smul, f.map_smul]β©

theorem Convex.is_linear_image (hs : Convex π s) {f : E β F} (hf : IsLinearMap π f) : Convex π (f '' s) :=
  hs.linear_image <| hf.mk' f

theorem Convex.linear_preimage {s : Set F} (hs : Convex π s) (f : E ββ[π] F) : Convex π (f β»ΒΉ' s) := by
  intro x y hx hy a b ha hb hab
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy ha hb hab

theorem Convex.is_linear_preimage {s : Set F} (hs : Convex π s) {f : E β F} (hf : IsLinearMap π f) :
    Convex π (f β»ΒΉ' s) :=
  hs.linear_preimage <| hf.mk' f

theorem Convex.add {t : Set E} (hs : Convex π s) (ht : Convex π t) : Convex π (s + t) := by
  rw [β add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.is_linear_map_add

theorem Convex.vadd (hs : Convex π s) (z : E) : Convex π (z +α΅₯ s) := by
  simp_rw [β image_vadd, vadd_eq_add, β singleton_add]
  exact (convex_singleton _).add hs

theorem Convex.translate (hs : Convex π s) (z : E) : Convex π ((fun x => z + x) '' s) :=
  hs.vadd _

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_right (hs : Convex π s) (z : E) : Convex π ((fun x => z + x) β»ΒΉ' s) := by
  intro x y hx hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_commβ, β add_smul, hab, one_smul] at h

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_left (hs : Convex π s) (z : E) : Convex π ((fun x => x + z) β»ΒΉ' s) := by
  simpa only [β add_commβ] using hs.translate_preimage_right z

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid Ξ²] [Module π Ξ²] [OrderedSmul π Ξ²]

theorem convex_Iic (r : Ξ²) : Convex π (Iic r) := fun x y hx hy a b ha hb hab =>
  calc
    a β’ x + b β’ y β€ a β’ r + b β’ r := add_le_add (smul_le_smul_of_nonneg hx ha) (smul_le_smul_of_nonneg hy hb)
    _ = r := Convex.combo_self hab _
    

theorem convex_Ici (r : Ξ²) : Convex π (Ici r) :=
  @convex_Iic π Ξ²α΅α΅ _ _ _ _ r

theorem convex_Icc (r s : Ξ²) : Convex π (Icc r s) :=
  Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)

theorem convex_halfspace_le {f : E β Ξ²} (h : IsLinearMap π f) (r : Ξ²) : Convex π { w | f w β€ r } :=
  (convex_Iic r).is_linear_preimage h

theorem convex_halfspace_ge {f : E β Ξ²} (h : IsLinearMap π f) (r : Ξ²) : Convex π { w | r β€ f w } :=
  (convex_Ici r).is_linear_preimage h

theorem convex_hyperplane {f : E β Ξ²} (h : IsLinearMap π f) (r : Ξ²) : Convex π { w | f w = r } := by
  simp_rw [le_antisymm_iffβ]
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r)

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid Ξ²] [Module π Ξ²] [OrderedSmul π Ξ²]

theorem convex_Iio (r : Ξ²) : Convex π (Iio r) := by
  intro x y hx hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  Β· rw [zero_addβ] at hab
    rwa [zero_smul, zero_addβ, hab, one_smul]
    
  rw [mem_Iio] at hx hy
  calc a β’ x + b β’ y < a β’ r + b β’ r :=
      add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx ha') (smul_le_smul_of_nonneg hy.le hb)_ = r :=
      Convex.combo_self hab _

theorem convex_Ioi (r : Ξ²) : Convex π (Ioi r) :=
  @convex_Iio π Ξ²α΅α΅ _ _ _ _ r

theorem convex_Ioo (r s : Ξ²) : Convex π (Ioo r s) :=
  Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)

theorem convex_Ico (r s : Ξ²) : Convex π (Ico r s) :=
  Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)

theorem convex_Ioc (r s : Ξ²) : Convex π (Ioc r s) :=
  Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)

theorem convex_halfspace_lt {f : E β Ξ²} (h : IsLinearMap π f) (r : Ξ²) : Convex π { w | f w < r } :=
  (convex_Iio r).is_linear_preimage h

theorem convex_halfspace_gt {f : E β Ξ²} (h : IsLinearMap π f) (r : Ξ²) : Convex π { w | r < f w } :=
  (convex_Ioi r).is_linear_preimage h

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid Ξ²] [Module π Ξ²] [OrderedSmul π Ξ²]

theorem convex_interval (r s : Ξ²) : Convex π (Interval r s) :=
  convex_Icc _ _

end LinearOrderedAddCommMonoid

end Module

end AddCommMonoidβ

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [OrderedAddCommMonoid Ξ²] [Module π E] [OrderedSmul π E] {s : Set E} {f : E β Ξ²}

theorem MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | f x β€ r }) :=
  fun x y hx hy a b ha hb hab =>
  β¨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' _ hx.2 hy.2)β©

theorem MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | f x < r }) :=
  fun x y hx hy a b ha hb hab =>
  β¨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' _ hx.2 hy.2)β©

theorem MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | r β€ f x }) :=
  @MonotoneOn.convex_le π Eα΅α΅ Ξ²α΅α΅ _ _ _ _ _ _ _ hf.dual hs r

theorem MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | r < f x }) :=
  @MonotoneOn.convex_lt π Eα΅α΅ Ξ²α΅α΅ _ _ _ _ _ _ _ hf.dual hs r

theorem AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | f x β€ r }) :=
  @MonotoneOn.convex_ge π E Ξ²α΅α΅ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | f x < r }) :=
  @MonotoneOn.convex_gt π E Ξ²α΅α΅ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | r β€ f x }) :=
  @MonotoneOn.convex_le π E Ξ²α΅α΅ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex π s) (r : Ξ²) : Convex π ({ x β s | r < f x }) :=
  @MonotoneOn.convex_lt π E Ξ²α΅α΅ _ _ _ _ _ _ _ hf hs r

theorem Monotone.convex_le (hf : Monotone f) (r : Ξ²) : Convex π { x | f x β€ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Monotone.convex_lt (hf : Monotone f) (r : Ξ²) : Convex π { x | f x β€ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Monotone.convex_ge (hf : Monotone f) (r : Ξ²) : Convex π { x | r β€ f x } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_ge convex_univ r)

theorem Monotone.convex_gt (hf : Monotone f) (r : Ξ²) : Convex π { x | f x β€ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Antitone.convex_le (hf : Antitone f) (r : Ξ²) : Convex π { x | f x β€ r } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_le convex_univ r)

theorem Antitone.convex_lt (hf : Antitone f) (r : Ξ²) : Convex π { x | f x < r } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_lt convex_univ r)

theorem Antitone.convex_ge (hf : Antitone f) (r : Ξ²) : Convex π { x | r β€ f x } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_ge convex_univ r)

theorem Antitone.convex_gt (hf : Antitone f) (r : Ξ²) : Convex π { x | r < f x } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_gt convex_univ r)

end LinearOrderedAddCommMonoid

section AddCommGroupβ

variable [AddCommGroupβ E] [Module π E] {s t : Set E}

theorem Convex.combo_eq_vadd {a b : π} {x y : E} (h : a + b = 1) : a β’ x + b β’ y = b β’ (y - x) + x :=
  calc
    a β’ x + b β’ y = b β’ y - b β’ x + (a β’ x + b β’ x) := by
      abel
    _ = b β’ (y - x) + x := by
      rw [smul_sub, Convex.combo_self h]
    

end AddCommGroupβ

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring π]

section AddCommMonoidβ

variable [AddCommMonoidβ E] [AddCommMonoidβ F] [Module π E] [Module π F] {s : Set E}

theorem Convex.smul (hs : Convex π s) (c : π) : Convex π (c β’ s) :=
  hs.linear_image (LinearMap.lsmul _ _ c)

theorem Convex.smul_preimage (hs : Convex π s) (c : π) : Convex π ((fun z => c β’ z) β»ΒΉ' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)

theorem Convex.affinity (hs : Convex π s) (z : E) (c : π) : Convex π ((fun x => z + c β’ x) '' s) := by
  simpa only [image_smul, image_vadd, β image_image] using (hs.smul c).vadd z

end AddCommMonoidβ

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing π]

section AddCommGroupβ

variable [AddCommGroupβ E] [AddCommGroupβ F] [Module π E] [Module π F] {s t : Set E}

theorem Convex.add_smul_mem (hs : Convex π s) {x y : E} (hx : x β s) (hy : x + y β s) {t : π} (ht : t β Icc (0 : π) 1) :
    x + t β’ y β s := by
  have h : x + t β’ y = (1 - t) β’ x + t β’ (x + y) := by
    rw [smul_add, β add_assocβ, β add_smul, sub_add_cancel, one_smul]
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)

theorem Convex.smul_mem_of_zero_mem (hs : Convex π s) {x : E} (zero_mem : (0 : E) β s) (hx : x β s) {t : π}
    (ht : t β Icc (0 : π) 1) : t β’ x β s := by
  simpa using
    hs.add_smul_mem zero_mem
      (by
        simpa using hx)
      ht

theorem Convex.add_smul_sub_mem (h : Convex π s) {x y : E} (hx : x β s) (hy : y β s) {t : π} (ht : t β Icc (0 : π) 1) :
    x + t β’ (y - x) β s := by
  apply h.segment_subset hx hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ht

/-- Affine subspaces are convex. -/
theorem AffineSubspace.convex (Q : AffineSubspace π E) : Convex π (Q : Set E) := by
  intro x y hx hy a b ha hb hab
  rw [eq_sub_of_add_eq hab, β AffineMap.line_map_apply_module]
  exact AffineMap.line_map_mem b hx hy

/-- Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
theorem Convex.combo_affine_apply {a b : π} {x y : E} {f : E βα΅[π] F} (h : a + b = 1) :
    f (a β’ x + b β’ y) = a β’ f x + b β’ f y := by
  simp only [β Convex.combo_eq_vadd h, vsub_eq_sub]
  exact f.apply_line_map _ _ _

/-- The preimage of a convex set under an affine map is convex. -/
theorem Convex.affine_preimage (f : E βα΅[π] F) {s : Set F} (hs : Convex π s) : Convex π (f β»ΒΉ' s) := by
  intro x y xs ys a b ha hb hab
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs xs ys ha hb hab

/-- The image of a convex set under an affine map is convex. -/
theorem Convex.affine_image (f : E βα΅[π] F) (hs : Convex π s) : Convex π (f '' s) := by
  rintro x y β¨x', β¨hx', hx'fβ©β© β¨y', β¨hy', hy'fβ©β© a b ha hb hab
  refine' β¨a β’ x' + b β’ y', β¨hs hx' hy' ha hb hab, _β©β©
  rw [Convex.combo_affine_apply hab, hx'f, hy'f]

theorem Convex.neg (hs : Convex π s) : Convex π (-s) :=
  hs.is_linear_preimage IsLinearMap.is_linear_map_neg

theorem Convex.sub (hs : Convex π s) (ht : Convex π t) : Convex π (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

end AddCommGroupβ

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField π]

section AddCommGroupβ

variable [AddCommGroupβ E] [AddCommGroupβ F] [Module π E] [Module π F] {s : Set E}

/-- Alternative definition of set convexity, using division. -/
theorem convex_iff_div :
    Convex π s β
      β β¦x y : Eβ¦, x β s β y β s β β β¦a b : πβ¦, 0 β€ a β 0 β€ b β 0 < a + b β (a / (a + b)) β’ x + (b / (a + b)) β’ y β s :=
  by
  simp only [β convex_iff_segment_subset, β subset_def, β mem_segment_iff_div]
  refine' forallβ_congrβ fun x y hx hy => β¨fun H a b ha hb hab => H _ β¨a, b, ha, hb, hab, rflβ©, _β©
  rintro H _ β¨a, b, ha, hb, hab, rflβ©
  exact H ha hb hab

theorem Convex.mem_smul_of_zero_mem (h : Convex π s) {x : E} (zero_mem : (0 : E) β s) (hx : x β s) {t : π}
    (ht : 1 β€ t) : x β t β’ s := by
  rw [mem_smul_set_iff_inv_smul_memβ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx β¨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one htβ©

theorem Convex.add_smul (h_conv : Convex π s) {p q : π} (hp : 0 β€ p) (hq : 0 β€ q) : (p + q) β’ s = p β’ s + q β’ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  Β· simp_rw [smul_set_empty, add_empty]
    
  obtain rfl | hp' := hp.eq_or_lt
  Β· rw [zero_addβ, zero_smul_set hs, zero_addβ]
    
  obtain rfl | hq' := hq.eq_or_lt
  Β· rw [add_zeroβ, zero_smul_set hs, add_zeroβ]
    
  ext
  constructor
  Β· rintro β¨v, hv, rflβ©
    exact β¨p β’ v, q β’ v, smul_mem_smul_set hv, smul_mem_smul_set hv, (add_smul _ _ _).symmβ©
    
  Β· rintro β¨vβ, vβ, β¨vββ, hββ, rflβ©, β¨vββ, hββ, rflβ©, rflβ©
    have hpq := add_pos hp' hq'
    exact
      mem_smul_set.2
        β¨_,
          h_conv hββ hββ (div_pos hp' hpq).le (div_pos hq' hpq).le
            (by
              rw [β div_self hpq.ne', add_div] : p / (p + q) + q / (p + q) = 1),
          by
          simp only [mul_smul, β smul_add, β mul_div_cancel' _ hpq.ne']β©
    

end AddCommGroupβ

end LinearOrderedField

/-!
#### Convex sets in an ordered space
Relates `convex` and `ord_connected`.
-/


section

theorem Set.OrdConnected.convex_of_chain [OrderedSemiring π] [OrderedAddCommMonoid E] [Module π E] [OrderedSmul π E]
    {s : Set E} (hs : s.OrdConnected) (h : IsChain (Β· β€ Β·) s) : Convex π s := by
  refine' convex_iff_segment_subset.mpr fun x y hx hy => _
  obtain hxy | hyx := h.total hx hy
  Β· exact (segment_subset_Icc hxy).trans (hs.out hx hy)
    
  Β· rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)
    

theorem Set.OrdConnected.convex [OrderedSemiring π] [LinearOrderedAddCommMonoid E] [Module π E] [OrderedSmul π E]
    {s : Set E} (hs : s.OrdConnected) : Convex π s :=
  hs.convex_of_chain <| is_chain_of_trichotomous s

theorem convex_iff_ord_connected [LinearOrderedField π] {s : Set π} : Convex π s β s.OrdConnected := by
  simp_rw [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset]
  exact forall_congrβ fun x => forall_swap

alias convex_iff_ord_connected β Convex.ord_connected _

end

/-! #### Convexity of submodules/subspaces -/


section Submodule

open Submodule

theorem Submodule.convex [OrderedSemiring π] [AddCommMonoidβ E] [Module π E] (K : Submodule π E) :
    Convex π (βK : Set E) := by
  repeat'
    intro
  refine' add_mem (smul_mem _ _ _) (smul_mem _ _ _) <;> assumption

theorem Subspace.convex [LinearOrderedField π] [AddCommGroupβ E] [Module π E] (K : Subspace π E) :
    Convex π (βK : Set E) :=
  K.Convex

end Submodule

/-! ### Simplex -/


section Simplex

variable (π) (ΞΉ : Type _) [OrderedSemiring π] [Fintype ΞΉ]

/-- The standard simplex in the space of functions `ΞΉ β π` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of convex spaces. -/
def StdSimplex : Set (ΞΉ β π) :=
  { f | (β x, 0 β€ f x) β§ (β x, f x) = 1 }

theorem std_simplex_eq_inter : StdSimplex π ΞΉ = (β x, { f | 0 β€ f x }) β© { f | (β x, f x) = 1 } := by
  ext f
  simp only [β StdSimplex, β Set.mem_inter_eq, β Set.mem_Inter, β Set.mem_set_of_eq]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem convex_std_simplex : Convex π (StdSimplex π ΞΉ) := by
  refine' fun f g hf hg a b ha hb hab => β¨fun x => _, _β©
  Β· apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
    
  Β· erw [Finset.sum_add_distrib, β Finset.smul_sum, β Finset.smul_sum, hf.2, hg.2, smul_eq_mul, smul_eq_mul, mul_oneβ,
      mul_oneβ]
    exact hab
    

variable {ΞΉ}

theorem ite_eq_mem_std_simplex (i : ΞΉ) : (fun j => ite (i = j) (1 : π) 0) β StdSimplex π ΞΉ :=
  β¨fun j => by
    simp only <;> split_ifs <;> norm_num, by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]β©

end Simplex

