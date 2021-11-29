import Mathbin.MeasureTheory.Measure.Lebesgue 
import Mathbin.NumberTheory.Liouville.Residual 
import Mathbin.NumberTheory.Liouville.LiouvilleWith 
import Mathbin.Analysis.PSeries

/-!
# Volume of the set of Liouville numbers

In this file we prove that the set of Liouville numbers with exponent (irrationality measure)
strictly greater than two is a set of Lebesuge measure zero, see
`volume_Union_set_of_liouville_with`.

Since this set is a residual set, we show that the filters `residual` and `volume.ae` are disjoint.
These filters correspond to two common notions of genericity on `ℝ`: residual sets and sets of full
measure. The fact that the filters are disjoint means that two mutually exclusive properties can be
“generic” at the same time (in the sense of different “genericity” filters).

## Tags

Liouville number, Lebesgue measure, residual, generic property
-/


open_locale Filter BigOperators Ennreal TopologicalSpace Nnreal

open Filter Set Metric MeasureTheory Real

-- error in NumberTheory.Liouville.Measure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set_of_liouville_with_subset_aux : «expr ⊆ »({x : exprℝ() | «expr∃ , »((p «expr > » 2), liouville_with p x)}, «expr⋃ , »((m : exprℤ()), «expr ⁻¹' »(λ
   x : exprℝ(), «expr + »(x, m), «expr⋃ , »((n «expr > » (0 : exprℕ())), {x : exprℝ() | «expr∃ᶠ in , »((b : exprℕ()), at_top, «expr∃ , »((a «expr ∈ » finset.Icc (0 : exprℤ()) b), «expr < »(«expr| |»(«expr - »(x, «expr / »((a : exprℤ()), b))), «expr / »(1, «expr ^ »(b, («expr + »(2, «expr / »(1, n)) : exprℝ()))))))})))) :=
begin
  rintro [ident x, "⟨", ident p, ",", ident hp, ",", ident hxp, "⟩"],
  rcases [expr exists_nat_one_div_lt (sub_pos.2 hp), "with", "⟨", ident n, ",", ident hn, "⟩"],
  rw [expr lt_sub_iff_add_lt'] ["at", ident hn],
  suffices [] [":", expr ∀
   y : exprℝ(), liouville_with p y → «expr ∈ »(y, Ico (0 : exprℝ()) 1) → «expr∃ᶠ in , »((b : exprℕ()), at_top, «expr∃ , »((a «expr ∈ » finset.Icc (0 : exprℤ()) b), «expr < »(«expr| |»(«expr - »(y, «expr / »(a, b))), «expr / »(1, «expr ^ »(b, («expr + »(2, «expr / »(1, «expr + »(n, 1))) : exprℝ()))))))],
  { simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_preimage, "]"] [] [],
    have [ident hx] [":", expr «expr ∈ »(«expr + »(x, «expr↑ »(«expr- »(«expr⌊ ⌋»(x)))), Ico (0 : exprℝ()) 1)] [],
    { simp [] [] ["only"] ["[", expr int.floor_le, ",", expr int.lt_floor_add_one, ",", expr add_neg_lt_iff_le_add', ",", expr zero_add, ",", expr and_self, ",", expr mem_Ico, ",", expr int.cast_neg, ",", expr le_add_neg_iff_add_le, "]"] [] [] },
    refine [expr ⟨«expr- »(«expr⌊ ⌋»(x)), «expr + »(n, 1), n.succ_pos, this _ (hxp.add_int _) hx⟩] },
  clear [ident hxp, ident x],
  intros [ident x, ident hxp, ident hx01],
  refine [expr ((hxp.frequently_lt_rpow_neg hn).and_eventually (eventually_ge_at_top 1)).mono _],
  rintro [ident b, "⟨", "⟨", ident a, ",", ident hne, ",", ident hlt, "⟩", ",", ident hb, "⟩"],
  rw ["[", expr rpow_neg b.cast_nonneg, ",", "<-", expr one_div, "]"] ["at", ident hlt],
  refine [expr ⟨a, _, hlt⟩],
  replace [ident hb] [":", expr «expr ≤ »((1 : exprℝ()), b)] [],
  from [expr nat.one_le_cast.2 hb],
  have [ident hb0] [":", expr «expr < »((0 : exprℝ()), b)] [":=", expr zero_lt_one.trans_le hb],
  replace [ident hlt] [":", expr «expr < »(«expr| |»(«expr - »(x, «expr / »(a, b))), «expr / »(1, b))] [],
  { refine [expr hlt.trans_le (one_div_le_one_div_of_le hb0 _)],
    calc
      «expr = »((b : exprℝ()), «expr ^ »(b, (1 : exprℝ()))) : (rpow_one _).symm
      «expr ≤ »(..., «expr ^ »(b, («expr + »(2, «expr / »(1, «expr + »(n, 1))) : exprℝ()))) : rpow_le_rpow_of_exponent_le hb (one_le_two.trans _),
    simpa [] [] [] [] [] ["using", expr n.cast_add_one_pos.le] },
  rw ["[", expr sub_div' _ _ _ hb0.ne', ",", expr abs_div, ",", expr abs_of_pos hb0, ",", expr div_lt_div_right hb0, ",", expr abs_sub_lt_iff, ",", expr sub_lt_iff_lt_add, ",", expr sub_lt_iff_lt_add, ",", "<-", expr sub_lt_iff_lt_add', "]"] ["at", ident hlt],
  rw ["[", expr finset.mem_Icc, ",", "<-", expr int.lt_add_one_iff, ",", "<-", expr int.lt_add_one_iff, ",", "<-", expr neg_lt_iff_pos_add, ",", expr add_comm, ",", "<-", expr @int.cast_lt exprℝ(), ",", "<-", expr @int.cast_lt exprℝ(), "]"] [],
  push_cast [] [],
  refine [expr ⟨lt_of_le_of_lt _ hlt.1, hlt.2.trans_le _⟩],
  { simp [] [] ["only"] ["[", expr mul_nonneg hx01.left b.cast_nonneg, ",", expr neg_le_sub_iff_le_add, ",", expr le_add_iff_nonneg_left, "]"] [] [] },
  { rw ["[", expr add_le_add_iff_left, "]"] [],
    calc
      «expr ≤ »(«expr * »(x, b), «expr * »(1, b)) : mul_le_mul_of_nonneg_right hx01.2.le hb0.le
      «expr = »(..., b) : one_mul b }
end

-- error in NumberTheory.Liouville.Measure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The set of numbers satisfying the Liouville condition with some exponent `p > 2` has Lebesgue
measure zero. -/
@[simp]
theorem volume_Union_set_of_liouville_with : «expr = »(volume «expr⋃ , »((p : exprℝ())
  (hp : «expr < »(2, p)), {x : exprℝ() | liouville_with p x}), 0) :=
begin
  simp [] [] ["only"] ["[", "<-", expr set_of_exists, "]"] [] [],
  refine [expr measure_mono_null set_of_liouville_with_subset_aux _],
  rw [expr measure_Union_null_iff] [],
  intro [ident m],
  rw [expr real.volume_preimage_add_right] [],
  clear [ident m],
  refine [expr «expr $ »(measure_bUnion_null_iff, countable_encodable _).2 (λ (n) (hn : «expr ≤ »(1, n)), _)],
  generalize [ident hr] [":"] [expr «expr = »((«expr + »(2, «expr / »(1, n)) : exprℝ()), r)],
  replace [ident hr] [":", expr «expr < »(2, r)] [],
  by simp [] [] [] ["[", "<-", expr hr, ",", expr zero_lt_one.trans_le hn, "]"] [] [],
  clear [ident hn, ident n],
  refine [expr measure_set_of_frequently_eq_zero _],
  simp [] [] ["only"] ["[", expr set_of_exists, ",", "<-", expr real.dist_eq, ",", "<-", expr mem_ball, ",", expr set_of_mem_eq, "]"] [] [],
  set [] [ident B] [":", expr exprℤ() → exprℕ() → set exprℝ()] [":="] [expr λ
   a b, ball «expr / »(a, b) «expr / »(1, «expr ^ »(b, r))] [],
  have [ident hB] [":", expr ∀
   a b, «expr = »(volume (B a b), «expr↑ »((«expr / »(2, «expr ^ »(b, r)) : «exprℝ≥0»())))] [],
  { intros [ident a, ident b],
    simp [] [] ["only"] ["[", expr B, ",", expr real.volume_ball, "]"] [] [],
    rw ["[", expr ennreal.of_real, ",", expr mul_one_div, ",", expr to_nnreal_div zero_le_two, ",", expr to_nnreal_bit0 zero_le_one, ",", expr to_nnreal_one, ",", expr to_nnreal_rpow_of_nonneg (nat.cast_nonneg _), ",", expr nnreal.to_nnreal_coe_nat, "]"] [] },
  have [] [":", expr ∀
   b : exprℕ(), «expr ≤ »(volume «expr⋃ , »((a «expr ∈ » finset.Icc (0 : exprℤ()) b), B a b), («expr * »(2, «expr + »(«expr ^ »(b, «expr - »(1, r)), «expr ^ »(b, «expr- »(r)))) : «exprℝ≥0»()))] [],
  { intro [ident b],
    calc
      «expr ≤ »(volume «expr⋃ , »((a «expr ∈ » finset.Icc (0 : exprℤ()) b), B a b), «expr∑ in , »((a), finset.Icc (0 : exprℤ()) b, volume (B a b))) : measure_bUnion_finset_le _ _
      «expr = »(..., («expr * »(«expr + »(b, 1), «expr / »(2, «expr ^ »(b, r))) : «exprℝ≥0»())) : by simp [] [] ["only"] ["[", expr hB, ",", expr int.card_Icc, ",", expr finset.sum_const, ",", expr nsmul_eq_mul, ",", expr sub_zero, ",", "<-", expr int.coe_nat_succ, ",", expr int.to_nat_coe_nat, ",", "<-", expr nat.cast_succ, ",", expr ennreal.coe_mul, ",", expr ennreal.coe_nat, "]"] [] []
      «expr = »(..., _) : _,
    have [] [":", expr «expr ≠ »(«expr - »(1, r), 0)] [],
    by linarith [] [] [],
    rw ["[", expr ennreal.coe_eq_coe, "]"] [],
    simp [] [] [] ["[", expr add_mul, ",", expr div_eq_mul_inv, ",", expr nnreal.rpow_neg, ",", expr nnreal.rpow_sub' _ this, ",", expr mul_add, ",", expr mul_left_comm, "]"] [] [] },
  refine [expr ne_top_of_le_ne_top (ennreal.tsum_coe_ne_top_iff_summable.2 _) (ennreal.tsum_le_tsum this)],
  refine [expr (summable.add _ _).mul_left _]; simp [] [] ["only"] ["[", expr nnreal.summable_rpow, "]"] [] []; linarith [] [] []
end

theorem ae_not_liouville_with : ∀ᵐx, ∀ p (_ : p > (2 : ℝ)), ¬LiouvilleWith p x :=
  by 
    simpa only [ae_iff, not_forall, not_not, set_of_exists] using volume_Union_set_of_liouville_with

theorem ae_not_liouville : ∀ᵐx, ¬Liouville x :=
  ae_not_liouville_with.mono$
    fun x h₁ h₂ =>
      h₁ 3
        (by 
          normNum)
        (h₂.liouville_with 3)

/-- The set of Liouville numbers has Lebesgue measure zero. -/
@[simp]
theorem volume_set_of_liouville : volume { x:ℝ | Liouville x } = 0 :=
  by 
    simpa only [ae_iff, not_not] using ae_not_liouville

/-- The filters `residual ℝ` and `volume.ae` are disjoint. This means that there exists a residual
set of Lebesgue measure zero (e.g., the set of Liouville numbers). -/
theorem Real.disjoint_residual_ae : Disjoint (residual ℝ) volume.ae :=
  disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville

