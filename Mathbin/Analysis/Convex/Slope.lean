import Mathbin.Analysis.Convex.Function

/-!
# Slopes of convex functions

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/


variable {𝕜 : Type _} [LinearOrderedField 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜}

-- error in Analysis.Convex.Slope: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : 𝕜 → 𝕜` is convex, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem convex_on.slope_mono_adjacent
(hf : convex_on 𝕜 s f)
{x y z : 𝕜}
(hx : «expr ∈ »(x, s))
(hz : «expr ∈ »(z, s))
(hxy : «expr < »(x, y))
(hyz : «expr < »(y, z)) : «expr ≤ »(«expr / »(«expr - »(f y, f x), «expr - »(y, x)), «expr / »(«expr - »(f z, f y), «expr - »(z, y))) :=
begin
  have [ident hxz] [] [":=", expr hxy.trans hyz],
  rw ["<-", expr sub_pos] ["at", ident hxy, ident hxz, ident hyz],
  suffices [] [":", expr «expr ≤ »(«expr + »(«expr / »(f y, «expr - »(y, x)), «expr / »(f y, «expr - »(z, y))), «expr + »(«expr / »(f x, «expr - »(y, x)), «expr / »(f z, «expr - »(z, y))))],
  { ring_nf [] [] ["at", ident this, "⊢"],
    linarith [] [] [] },
  set [] [ident a] [] [":="] [expr «expr / »(«expr - »(z, y), «expr - »(z, x))] [],
  set [] [ident b] [] [":="] [expr «expr / »(«expr - »(y, x), «expr - »(z, x))] [],
  have [ident hy] [":", expr «expr = »(«expr + »(«expr • »(a, x), «expr • »(b, z)), y)] [],
  by { field_simp [] [] [] [],
    rw [expr div_eq_iff] []; [ring [], linarith [] [] []] },
  have [ident key] [] [],
  from [expr hf.2 hx hz (show «expr ≤ »(0, a), by apply [expr div_nonneg]; linarith [] [] []) (show «expr ≤ »(0, b), by apply [expr div_nonneg]; linarith [] [] []) (show «expr = »(«expr + »(a, b), 1), by { field_simp [] [] [] [],
      rw [expr div_eq_iff] []; [ring [], linarith [] [] []] })],
  rw [expr hy] ["at", ident key],
  replace [ident key] [] [":=", expr mul_le_mul_of_nonneg_left key hxz.le],
  field_simp [] ["[", expr hxy.ne', ",", expr hyz.ne', ",", expr hxz.ne', ",", expr mul_comm «expr - »(z, x) _, "]"] [] ["at", ident key, "⊢"],
  rw [expr div_le_div_right] [],
  { linarith [] [] [] },
  { nlinarith [] [] [] }
end

/-- If `f : 𝕜 → 𝕜` is concave, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem ConcaveOn.slope_anti_adjacent (hf : ConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y)
  (hyz : y < z) : (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
  by 
    rw [←neg_le_neg_iff, ←neg_sub_neg (f x), ←neg_sub_neg (f y)]
    simpRw [←Pi.neg_apply, ←neg_div, neg_sub]
    exact ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz

-- error in Analysis.Convex.Slope: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : 𝕜 → 𝕜` is strictly convex, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strict_convex_on.slope_strict_mono_adjacent
(hf : strict_convex_on 𝕜 s f)
{x y z : 𝕜}
(hx : «expr ∈ »(x, s))
(hz : «expr ∈ »(z, s))
(hxy : «expr < »(x, y))
(hyz : «expr < »(y, z)) : «expr < »(«expr / »(«expr - »(f y, f x), «expr - »(y, x)), «expr / »(«expr - »(f z, f y), «expr - »(z, y))) :=
begin
  have [ident hxz] [] [":=", expr hxy.trans hyz],
  have [ident hxz'] [] [":=", expr hxz.ne],
  rw ["<-", expr sub_pos] ["at", ident hxy, ident hxz, ident hyz],
  suffices [] [":", expr «expr < »(«expr + »(«expr / »(f y, «expr - »(y, x)), «expr / »(f y, «expr - »(z, y))), «expr + »(«expr / »(f x, «expr - »(y, x)), «expr / »(f z, «expr - »(z, y))))],
  { ring_nf [] [] ["at", ident this, "⊢"],
    linarith [] [] [] },
  set [] [ident a] [] [":="] [expr «expr / »(«expr - »(z, y), «expr - »(z, x))] [],
  set [] [ident b] [] [":="] [expr «expr / »(«expr - »(y, x), «expr - »(z, x))] [],
  have [ident hy] [":", expr «expr = »(«expr + »(«expr • »(a, x), «expr • »(b, z)), y)] [],
  by { field_simp [] [] [] [],
    rw [expr div_eq_iff] []; [ring [], linarith [] [] []] },
  have [ident key] [] [],
  from [expr hf.2 hx hz hxz' (div_pos hyz hxz) (div_pos hxy hxz) (show «expr = »(«expr + »(a, b), 1), by { field_simp [] [] [] [],
      rw [expr div_eq_iff] []; [ring [], linarith [] [] []] })],
  rw [expr hy] ["at", ident key],
  replace [ident key] [] [":=", expr mul_lt_mul_of_pos_left key hxz],
  field_simp [] ["[", expr hxy.ne', ",", expr hyz.ne', ",", expr hxz.ne', ",", expr mul_comm «expr - »(z, x) _, "]"] [] ["at", ident key, "⊢"],
  rw [expr div_lt_div_right] [],
  { linarith [] [] [] },
  { nlinarith [] [] [] }
end

/-- If `f : 𝕜 → 𝕜` is strictly concave, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem StrictConcaveOn.slope_anti_adjacent (hf : StrictConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
  (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
  by 
    rw [←neg_lt_neg_iff, ←neg_sub_neg (f x), ←neg_sub_neg (f y)]
    simpRw [←Pi.neg_apply, ←neg_div, neg_sub]
    exact StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz

-- error in Analysis.Convex.Slope: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
less than the slope of the secant line of `f` on `[x, z]`, then `f` is convex. -/
theorem convex_on_of_slope_mono_adjacent
(hs : convex 𝕜 s)
(hf : ∀
 {x
  y
  z : 𝕜}, «expr ∈ »(x, s) → «expr ∈ »(z, s) → «expr < »(x, y) → «expr < »(y, z) → «expr ≤ »(«expr / »(«expr - »(f y, f x), «expr - »(y, x)), «expr / »(«expr - »(f z, f y), «expr - »(z, y)))) : convex_on 𝕜 s f :=
linear_order.convex_on_of_lt hs (begin
   assume [binders (x z hx hz hxz a b ha hb hab)],
   let [ident y] [] [":=", expr «expr + »(«expr * »(a, x), «expr * »(b, z))],
   have [ident hxy] [":", expr «expr < »(x, y)] [],
   { rw ["[", "<-", expr one_mul x, ",", "<-", expr hab, ",", expr add_mul, "]"] [],
     exact [expr add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _] },
   have [ident hyz] [":", expr «expr < »(y, z)] [],
   { rw ["[", "<-", expr one_mul z, ",", "<-", expr hab, ",", expr add_mul, "]"] [],
     exact [expr add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _] },
   have [] [":", expr «expr ≤ »(«expr * »(«expr - »(f y, f x), «expr - »(z, y)), «expr * »(«expr - »(f z, f y), «expr - »(y, x)))] [],
   from [expr (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)],
   have [ident hxz] [":", expr «expr < »(0, «expr - »(z, x))] [],
   from [expr sub_pos.2 (hxy.trans hyz)],
   have [ident ha] [":", expr «expr = »(«expr / »(«expr - »(z, y), «expr - »(z, x)), a)] [],
   { rw ["[", expr eq_comm, ",", "<-", expr sub_eq_iff_eq_add', "]"] ["at", ident hab],
     simp_rw ["[", expr div_eq_iff hxz.ne', ",", expr y, ",", "<-", expr hab, "]"] [],
     ring [] },
   have [ident hb] [":", expr «expr = »(«expr / »(«expr - »(y, x), «expr - »(z, x)), b)] [],
   { rw ["[", expr eq_comm, ",", "<-", expr sub_eq_iff_eq_add, "]"] ["at", ident hab],
     simp_rw ["[", expr div_eq_iff hxz.ne', ",", expr y, ",", "<-", expr hab, "]"] [],
     ring [] },
   rwa ["[", expr sub_mul, ",", expr sub_mul, ",", expr sub_le_iff_le_add', ",", "<-", expr add_sub_assoc, ",", expr le_sub_iff_add_le, ",", "<-", expr mul_add, ",", expr sub_add_sub_cancel, ",", "<-", expr le_div_iff hxz, ",", expr add_div, ",", expr mul_div_assoc, ",", expr mul_div_assoc, ",", expr mul_comm (f x), ",", expr mul_comm (f z), ",", expr ha, ",", expr hb, "]"] ["at", ident this]
 end)

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
greater than the slope of the secant line of `f` on `[x, z]`, then `f` is concave. -/
theorem concave_on_of_slope_anti_adjacent (hs : Convex 𝕜 s)
  (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :
  ConcaveOn 𝕜 s f :=
  by 
    rw [←neg_convex_on_iff]
    refine' convex_on_of_slope_mono_adjacent hs fun x y z hx hz hxy hyz => _ 
    rw [←neg_le_neg_iff]
    simpRw [←neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
    exact hf hx hz hxy hyz

-- error in Analysis.Convex.Slope: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly less than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly convex. -/
theorem strict_convex_on_of_slope_strict_mono_adjacent
(hs : convex 𝕜 s)
(hf : ∀
 {x
  y
  z : 𝕜}, «expr ∈ »(x, s) → «expr ∈ »(z, s) → «expr < »(x, y) → «expr < »(y, z) → «expr < »(«expr / »(«expr - »(f y, f x), «expr - »(y, x)), «expr / »(«expr - »(f z, f y), «expr - »(z, y)))) : strict_convex_on 𝕜 s f :=
linear_order.strict_convex_on_of_lt hs (begin
   assume [binders (x z hx hz hxz a b ha hb hab)],
   let [ident y] [] [":=", expr «expr + »(«expr * »(a, x), «expr * »(b, z))],
   have [ident hxy] [":", expr «expr < »(x, y)] [],
   { rw ["[", "<-", expr one_mul x, ",", "<-", expr hab, ",", expr add_mul, "]"] [],
     exact [expr add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _] },
   have [ident hyz] [":", expr «expr < »(y, z)] [],
   { rw ["[", "<-", expr one_mul z, ",", "<-", expr hab, ",", expr add_mul, "]"] [],
     exact [expr add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _] },
   have [] [":", expr «expr < »(«expr * »(«expr - »(f y, f x), «expr - »(z, y)), «expr * »(«expr - »(f z, f y), «expr - »(y, x)))] [],
   from [expr (div_lt_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)],
   have [ident hxz] [":", expr «expr < »(0, «expr - »(z, x))] [],
   from [expr sub_pos.2 (hxy.trans hyz)],
   have [ident ha] [":", expr «expr = »(«expr / »(«expr - »(z, y), «expr - »(z, x)), a)] [],
   { rw ["[", expr eq_comm, ",", "<-", expr sub_eq_iff_eq_add', "]"] ["at", ident hab],
     simp_rw ["[", expr div_eq_iff hxz.ne', ",", expr y, ",", "<-", expr hab, "]"] [],
     ring [] },
   have [ident hb] [":", expr «expr = »(«expr / »(«expr - »(y, x), «expr - »(z, x)), b)] [],
   { rw ["[", expr eq_comm, ",", "<-", expr sub_eq_iff_eq_add, "]"] ["at", ident hab],
     simp_rw ["[", expr div_eq_iff hxz.ne', ",", expr y, ",", "<-", expr hab, "]"] [],
     ring [] },
   rwa ["[", expr sub_mul, ",", expr sub_mul, ",", expr sub_lt_iff_lt_add', ",", "<-", expr add_sub_assoc, ",", expr lt_sub_iff_add_lt, ",", "<-", expr mul_add, ",", expr sub_add_sub_cancel, ",", "<-", expr lt_div_iff hxz, ",", expr add_div, ",", expr mul_div_assoc, ",", expr mul_div_assoc, ",", expr mul_comm (f x), ",", expr mul_comm (f z), ",", expr ha, ",", expr hb, "]"] ["at", ident this]
 end)

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly greater than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly concave.
-/
theorem strict_concave_on_of_slope_strict_anti_adjacent (hs : Convex 𝕜 s)
  (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) < (f y - f x) / (y - x)) :
  StrictConcaveOn 𝕜 s f :=
  by 
    rw [←neg_strict_convex_on_iff]
    refine' strict_convex_on_of_slope_strict_mono_adjacent hs fun x y z hx hz hxy hyz => _ 
    rw [←neg_lt_neg_iff]
    simpRw [←neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
    exact hf hx hz hxy hyz

/-- A function `f : 𝕜 → 𝕜` is convex iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem convex_on_iff_slope_mono_adjacent :
  ConvexOn 𝕜 s f ↔
    Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_mono_adjacent⟩, fun h => convex_on_of_slope_mono_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is concave iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem concave_on_iff_slope_anti_adjacent :
  ConcaveOn 𝕜 s f ↔
    Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_anti_adjacent⟩, fun h => concave_on_of_slope_anti_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is strictly convex iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strict_convex_on_iff_slope_strict_mono_adjacent :
  StrictConvexOn 𝕜 s f ↔
    Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_strict_mono_adjacent⟩,
    fun h => strict_convex_on_of_slope_strict_mono_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is strictly concave iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strict_concave_on_iff_slope_strict_anti_adjacent :
  StrictConcaveOn 𝕜 s f ↔
    Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_anti_adjacent⟩, fun h => strict_concave_on_of_slope_strict_anti_adjacent h.1 h.2⟩

