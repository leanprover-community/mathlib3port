import Mathbin.MeasureTheory.Decomposition.SignedHahn 
import Mathbin.MeasureTheory.Measure.MutuallySingular

/-!
# Jordan decomposition

This file proves the existence and uniqueness of the Jordan decomposition for signed measures.
The Jordan decomposition theorem states that, given a signed measure `s`, there exists a
unique pair of mutually singular measures `μ` and `ν`, such that `s = μ - ν`.

The Jordan decomposition theorem for measures is a corollary of the Hahn decomposition theorem and
is useful for the Lebesgue decomposition theorem.

## Main definitions

* `measure_theory.jordan_decomposition`: a Jordan decomposition of a measurable space is a
  pair of mutually singular finite measures. We say `j` is a Jordan decomposition of a signed
  measure `s` if `s = j.pos_part - j.neg_part`.
* `measure_theory.signed_measure.to_jordan_decomposition`: the Jordan decomposition of a
  signed measure.
* `measure_theory.signed_measure.to_jordan_decomposition_equiv`: is the `equiv` between
  `measure_theory.signed_measure` and `measure_theory.jordan_decomposition` formed by
  `measure_theory.signed_measure.to_jordan_decomposition`.

## Main results

* `measure_theory.signed_measure.to_signed_measure_to_jordan_decomposition` : the Jordan
  decomposition theorem.
* `measure_theory.jordan_decomposition.to_signed_measure_injective` : the Jordan decomposition of a
  signed measure is unique.

## Tags

Jordan decomposition theorem
-/


noncomputable theory

open_locale Classical MeasureTheory Ennreal Nnreal

variable{α β : Type _}[MeasurableSpace α]

namespace MeasureTheory

/-- A Jordan decomposition of a measurable space is a pair of mutually singular,
finite measures. -/
@[ext]
structure jordan_decomposition(α : Type _)[MeasurableSpace α] where 
  (posPart negPart : Measureₓ α)
  [pos_part_finite : is_finite_measure pos_part]
  [neg_part_finite : is_finite_measure neg_part]
  MutuallySingular : pos_part ⊥ₘ neg_part

attribute [instance] jordan_decomposition.pos_part_finite

attribute [instance] jordan_decomposition.neg_part_finite

namespace JordanDecomposition

open Measureₓ VectorMeasure

variable(j : jordan_decomposition α)

instance  : HasZero (jordan_decomposition α) :=
  { zero := ⟨0, 0, mutually_singular.zero_right⟩ }

instance  : Inhabited (jordan_decomposition α) :=
  { default := 0 }

instance  : Neg (jordan_decomposition α) :=
  { neg := fun j => ⟨j.neg_part, j.pos_part, j.mutually_singular.symm⟩ }

instance  : HasScalar ℝ≥0  (jordan_decomposition α) :=
  { smul :=
      fun r j =>
        ⟨r • j.pos_part, r • j.neg_part,
          mutually_singular.smul _ (mutually_singular.smul _ j.mutually_singular.symm).symm⟩ }

instance has_scalar_real : HasScalar ℝ (jordan_decomposition α) :=
  { smul := fun r j => if hr : 0 ≤ r then r.to_nnreal • j else -((-r).toNnreal • j) }

@[simp]
theorem zero_pos_part : (0 : jordan_decomposition α).posPart = 0 :=
  rfl

@[simp]
theorem zero_neg_part : (0 : jordan_decomposition α).negPart = 0 :=
  rfl

@[simp]
theorem neg_pos_part : (-j).posPart = j.neg_part :=
  rfl

@[simp]
theorem neg_neg_part : (-j).negPart = j.pos_part :=
  rfl

@[simp]
theorem smul_pos_part (r :  ℝ≥0 ) : (r • j).posPart = r • j.pos_part :=
  rfl

@[simp]
theorem smul_neg_part (r :  ℝ≥0 ) : (r • j).negPart = r • j.neg_part :=
  rfl

theorem real_smul_def (r : ℝ) (j : jordan_decomposition α) :
  r • j = if hr : 0 ≤ r then r.to_nnreal • j else -((-r).toNnreal • j) :=
  rfl

@[simp]
theorem coe_smul (r :  ℝ≥0 ) : (r : ℝ) • j = r • j :=
  show dite _ _ _ = _ by 
    rw [dif_pos (Nnreal.coe_nonneg r), Real.to_nnreal_coe]

theorem real_smul_nonneg (r : ℝ) (hr : 0 ≤ r) : r • j = r.to_nnreal • j :=
  dif_pos hr

theorem real_smul_neg (r : ℝ) (hr : r < 0) : r • j = -((-r).toNnreal • j) :=
  dif_neg (not_leₓ.2 hr)

theorem real_smul_pos_part_nonneg (r : ℝ) (hr : 0 ≤ r) : (r • j).posPart = r.to_nnreal • j.pos_part :=
  by 
    rw [real_smul_def, ←smul_pos_part, dif_pos hr]

theorem real_smul_neg_part_nonneg (r : ℝ) (hr : 0 ≤ r) : (r • j).negPart = r.to_nnreal • j.neg_part :=
  by 
    rw [real_smul_def, ←smul_neg_part, dif_pos hr]

theorem real_smul_pos_part_neg (r : ℝ) (hr : r < 0) : (r • j).posPart = (-r).toNnreal • j.neg_part :=
  by 
    rw [real_smul_def, ←smul_neg_part, dif_neg (not_leₓ.2 hr), neg_pos_part]

theorem real_smul_neg_part_neg (r : ℝ) (hr : r < 0) : (r • j).negPart = (-r).toNnreal • j.pos_part :=
  by 
    rw [real_smul_def, ←smul_pos_part, dif_neg (not_leₓ.2 hr), neg_neg_part]

/-- The signed measure associated with a Jordan decomposition. -/
def to_signed_measure : signed_measure α :=
  j.pos_part.to_signed_measure - j.neg_part.to_signed_measure

theorem to_signed_measure_zero : (0 : jordan_decomposition α).toSignedMeasure = 0 :=
  by 
    ext1 i hi 
    erw [to_signed_measure, to_signed_measure_sub_apply hi, sub_self, zero_apply]

theorem to_signed_measure_neg : (-j).toSignedMeasure = -j.to_signed_measure :=
  by 
    ext1 i hi 
    rw [neg_apply, to_signed_measure, to_signed_measure, to_signed_measure_sub_apply hi, to_signed_measure_sub_apply hi,
      neg_sub]
    rfl

theorem to_signed_measure_smul (r :  ℝ≥0 ) : (r • j).toSignedMeasure = r • j.to_signed_measure :=
  by 
    ext1 i hi 
    rw [vector_measure.smul_apply, to_signed_measure, to_signed_measure, to_signed_measure_sub_apply hi,
      to_signed_measure_sub_apply hi, smul_sub, smul_pos_part, smul_neg_part, ←Ennreal.to_real_smul,
      ←Ennreal.to_real_smul]
    rfl

/-- A Jordan decomposition provides a Hahn decomposition. -/
theorem exists_compl_positive_negative :
  ∃ S : Set α,
    MeasurableSet S ∧
      j.to_signed_measure ≤[S] 0 ∧
        0 ≤[«expr ᶜ» S] j.to_signed_measure ∧ j.pos_part S = 0 ∧ j.neg_part («expr ᶜ» S) = 0 :=
  by 
    obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutually_singular 
    refine' ⟨S, hS₁, _, _, hS₂, hS₃⟩
    ·
      refine' restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => _ 
      rw [to_signed_measure, to_signed_measure_sub_apply hA,
        show j.pos_part A = 0 by 
          exact nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA₁),
        Ennreal.zero_to_real, zero_sub, neg_le, zero_apply, neg_zero]
      exact Ennreal.to_real_nonneg
    ·
      refine' restrict_le_restrict_of_subset_le _ _ fun A hA hA₁ => _ 
      rw [to_signed_measure, to_signed_measure_sub_apply hA,
        show j.neg_part A = 0 by 
          exact nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA₁),
        Ennreal.zero_to_real, sub_zero]
      exact Ennreal.to_real_nonneg

end JordanDecomposition

namespace SignedMeasure

open Measureₓ VectorMeasure JordanDecomposition Classical

variable{s : signed_measure α}{μ ν : Measureₓ α}[is_finite_measure μ][is_finite_measure ν]

/-- Given a signed measure `s`, `s.to_jordan_decomposition` is the Jordan decomposition `j`,
such that `s = j.to_signed_measure`. This property is known as the Jordan decomposition
theorem, and is shown by
`measure_theory.signed_measure.to_signed_measure_to_jordan_decomposition`. -/
def to_jordan_decomposition (s : signed_measure α) : jordan_decomposition α :=
  let i := some s.exists_compl_positive_negative 
  let hi := some_spec s.exists_compl_positive_negative
  { posPart := s.to_measure_of_zero_le i hi.1 hi.2.1, negPart := s.to_measure_of_le_zero («expr ᶜ» i) hi.1.Compl hi.2.2,
    pos_part_finite := inferInstance, neg_part_finite := inferInstance,
    MutuallySingular :=
      by 
        refine' ⟨«expr ᶜ» i, hi.1.Compl, _, _⟩
        ·
          rw [to_measure_of_zero_le_apply _ _ hi.1 hi.1.Compl]
          simp 
        ·
          rw [to_measure_of_le_zero_apply _ _ hi.1.Compl hi.1.Compl.Compl]
          simp  }

theorem to_jordan_decomposition_spec (s : signed_measure α) :
  ∃ (i : Set α)(hi₁ : MeasurableSet i)(hi₂ : 0 ≤[i] s)(hi₃ : s ≤[«expr ᶜ» i] 0),
    s.to_jordan_decomposition.pos_part = s.to_measure_of_zero_le i hi₁ hi₂ ∧
      s.to_jordan_decomposition.neg_part = s.to_measure_of_le_zero («expr ᶜ» i) hi₁.compl hi₃ :=
  by 
    set i := some s.exists_compl_positive_negative 
    obtain ⟨hi₁, hi₂, hi₃⟩ := some_spec s.exists_compl_positive_negative 
    exact ⟨i, hi₁, hi₂, hi₃, rfl, rfl⟩

/-- **The Jordan decomposition theorem**: Given a signed measure `s`, there exists a pair of
mutually singular measures `μ` and `ν` such that `s = μ - ν`. In this case, the measures `μ`
and `ν` are given by `s.to_jordan_decomposition.pos_part` and
`s.to_jordan_decomposition.neg_part` respectively.

Note that we use `measure_theory.jordan_decomposition.to_signed_measure` to represent the
signed measure corresponding to
`s.to_jordan_decomposition.pos_part - s.to_jordan_decomposition.neg_part`. -/
@[simp]
theorem to_signed_measure_to_jordan_decomposition (s : signed_measure α) :
  s.to_jordan_decomposition.to_signed_measure = s :=
  by 
    obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.to_jordan_decomposition_spec 
    simp only [jordan_decomposition.to_signed_measure, hμ, hν]
    ext k hk 
    rw [to_signed_measure_sub_apply hk, to_measure_of_zero_le_apply _ hi₂ hi₁ hk,
      to_measure_of_le_zero_apply _ hi₃ hi₁.compl hk]
    simp only [Ennreal.coe_to_real, Subtype.coe_mk, Ennreal.some_eq_coe, sub_neg_eq_add]
    rw [←of_union _ (MeasurableSet.inter hi₁ hk) (MeasurableSet.inter hi₁.compl hk), Set.inter_comm i,
      Set.inter_comm («expr ᶜ» i), Set.inter_union_compl _ _]
    ·
      infer_instance
    ·
      rintro x ⟨⟨hx₁, _⟩, hx₂, _⟩
      exact False.elim (hx₂ hx₁)

section 

variable{u v w : Set α}

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a positive set `u`. -/
theorem subset_positive_null_set
(hu : measurable_set u)
(hv : measurable_set v)
(hw : measurable_set w)
(hsu : «expr ≤[ ] »(0, u, s))
(hw₁ : «expr = »(s w, 0))
(hw₂ : «expr ⊆ »(w, u))
(hwt : «expr ⊆ »(v, w)) : «expr = »(s v, 0) :=
begin
  have [] [":", expr «expr = »(«expr + »(s v, s «expr \ »(w, v)), 0)] [],
  { rw ["[", "<-", expr hw₁, ",", "<-", expr of_union set.disjoint_diff hv (hw.diff hv), ",", expr set.union_diff_self, ",", expr set.union_eq_self_of_subset_left hwt, "]"] [],
    apply_instance },
  have [ident h₁] [] [":=", expr nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂))],
  have [ident h₂] [] [":=", expr nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu ((w.diff_subset v).trans hw₂))],
  linarith [] [] []
end

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a negative set `u`. -/
theorem subset_negative_null_set
(hu : measurable_set u)
(hv : measurable_set v)
(hw : measurable_set w)
(hsu : «expr ≤[ ] »(s, u, 0))
(hw₁ : «expr = »(s w, 0))
(hw₂ : «expr ⊆ »(w, u))
(hwt : «expr ⊆ »(v, w)) : «expr = »(s v, 0) :=
begin
  rw ["[", "<-", expr s.neg_le_neg_iff _ hu, ",", expr neg_zero, "]"] ["at", ident hsu],
  have [] [] [":=", expr subset_positive_null_set hu hv hw hsu],
  simp [] [] ["only"] ["[", expr pi.neg_apply, ",", expr neg_eq_zero, ",", expr coe_neg, "]"] [] ["at", ident this],
  exact [expr this hw₁ hw₂ hwt]
end

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the symmetric difference of two positive sets is a null-set, then so are the differences
between the two sets. -/
theorem of_diff_eq_zero_of_symm_diff_eq_zero_positive
(hu : measurable_set u)
(hv : measurable_set v)
(hsu : «expr ≤[ ] »(0, u, s))
(hsv : «expr ≤[ ] »(0, v, s))
(hs : «expr = »(s «expr Δ »(u, v), 0)) : «expr ∧ »(«expr = »(s «expr \ »(u, v), 0), «expr = »(s «expr \ »(v, u), 0)) :=
begin
  rw [expr restrict_le_restrict_iff] ["at", ident hsu, ident hsv],
  have [ident a] [] [":=", expr hsu (hu.diff hv) (u.diff_subset v)],
  have [ident b] [] [":=", expr hsv (hv.diff hu) (v.diff_subset u)],
  erw ["[", expr of_union (set.disjoint_of_subset_left (u.diff_subset v) set.disjoint_diff) (hu.diff hv) (hv.diff hu), "]"] ["at", ident hs],
  rw [expr zero_apply] ["at", ident a, ident b],
  split,
  all_goals { linarith [] [] [] <|> apply_instance <|> assumption }
end

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the symmetric difference of two negative sets is a null-set, then so are the differences
between the two sets. -/
theorem of_diff_eq_zero_of_symm_diff_eq_zero_negative
(hu : measurable_set u)
(hv : measurable_set v)
(hsu : «expr ≤[ ] »(s, u, 0))
(hsv : «expr ≤[ ] »(s, v, 0))
(hs : «expr = »(s «expr Δ »(u, v), 0)) : «expr ∧ »(«expr = »(s «expr \ »(u, v), 0), «expr = »(s «expr \ »(v, u), 0)) :=
begin
  rw ["[", "<-", expr s.neg_le_neg_iff _ hu, ",", expr neg_zero, "]"] ["at", ident hsu],
  rw ["[", "<-", expr s.neg_le_neg_iff _ hv, ",", expr neg_zero, "]"] ["at", ident hsv],
  have [] [] [":=", expr of_diff_eq_zero_of_symm_diff_eq_zero_positive hu hv hsu hsv],
  simp [] [] ["only"] ["[", expr pi.neg_apply, ",", expr neg_eq_zero, ",", expr coe_neg, "]"] [] ["at", ident this],
  exact [expr this hs]
end

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_inter_eq_of_symm_diff_eq_zero_positive
(hu : measurable_set u)
(hv : measurable_set v)
(hw : measurable_set w)
(hsu : «expr ≤[ ] »(0, u, s))
(hsv : «expr ≤[ ] »(0, v, s))
(hs : «expr = »(s «expr Δ »(u, v), 0)) : «expr = »(s «expr ∩ »(w, u), s «expr ∩ »(w, v)) :=
begin
  have [ident hwuv] [":", expr «expr = »(s «expr Δ »(«expr ∩ »(w, u), «expr ∩ »(w, v)), 0)] [],
  { refine [expr subset_positive_null_set (hu.union hv) ((hw.inter hu).symm_diff (hw.inter hv)) (hu.symm_diff hv) (restrict_le_restrict_union _ _ hu hsu hv hsv) hs _ _],
    { exact [expr symm_diff_le_sup u v] },
    { rintro [ident x, "(", "⟨", "⟨", ident hxw, ",", ident hxu, "⟩", ",", ident hx, "⟩", "|", "⟨", "⟨", ident hxw, ",", ident hxv, "⟩", ",", ident hx, "⟩", ")"]; rw ["[", expr set.mem_inter_eq, ",", expr not_and, "]"] ["at", ident hx],
      { exact [expr or.inl ⟨hxu, hx hxw⟩] },
      { exact [expr or.inr ⟨hxv, hx hxw⟩] } } },
  obtain ["⟨", ident huv, ",", ident hvu, "⟩", ":=", expr of_diff_eq_zero_of_symm_diff_eq_zero_positive (hw.inter hu) (hw.inter hv) (restrict_le_restrict_subset _ _ hu hsu (w.inter_subset_right u)) (restrict_le_restrict_subset _ _ hv hsv (w.inter_subset_right v)) hwuv],
  rw ["[", "<-", expr of_diff_of_diff_eq_zero (hw.inter hu) (hw.inter hv) hvu, ",", expr huv, ",", expr zero_add, "]"] []
end

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_inter_eq_of_symm_diff_eq_zero_negative
(hu : measurable_set u)
(hv : measurable_set v)
(hw : measurable_set w)
(hsu : «expr ≤[ ] »(s, u, 0))
(hsv : «expr ≤[ ] »(s, v, 0))
(hs : «expr = »(s «expr Δ »(u, v), 0)) : «expr = »(s «expr ∩ »(w, u), s «expr ∩ »(w, v)) :=
begin
  rw ["[", "<-", expr s.neg_le_neg_iff _ hu, ",", expr neg_zero, "]"] ["at", ident hsu],
  rw ["[", "<-", expr s.neg_le_neg_iff _ hv, ",", expr neg_zero, "]"] ["at", ident hsv],
  have [] [] [":=", expr of_inter_eq_of_symm_diff_eq_zero_positive hu hv hw hsu hsv],
  simp [] [] ["only"] ["[", expr pi.neg_apply, ",", expr neg_inj, ",", expr neg_eq_zero, ",", expr coe_neg, "]"] [] ["at", ident this],
  exact [expr this hs]
end

end 

end SignedMeasure

namespace JordanDecomposition

open Measureₓ VectorMeasure SignedMeasure Function

private theorem eq_of_pos_part_eq_pos_part {j₁ j₂ : jordan_decomposition α} (hj : j₁.pos_part = j₂.pos_part)
  (hj' : j₁.to_signed_measure = j₂.to_signed_measure) : j₁ = j₂ :=
  by 
    ext1
    ·
      exact hj
    ·
      rw [←to_signed_measure_eq_to_signed_measure_iff]
      suffices  :
        j₁.pos_part.to_signed_measure - j₁.neg_part.to_signed_measure =
          j₁.pos_part.to_signed_measure - j₂.neg_part.to_signed_measure
      ·
        exact sub_right_inj.mp this 
      convert hj'

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Jordan decomposition of a signed measure is unique. -/
theorem to_signed_measure_injective : «expr $ »(injective, @jordan_decomposition.to_signed_measure α _) :=
begin
  intros [ident j₁, ident j₂, ident hj],
  obtain ["⟨", ident S, ",", ident hS₁, ",", ident hS₂, ",", ident hS₃, ",", ident hS₄, ",", ident hS₅, "⟩", ":=", expr j₁.exists_compl_positive_negative],
  obtain ["⟨", ident T, ",", ident hT₁, ",", ident hT₂, ",", ident hT₃, ",", ident hT₄, ",", ident hT₅, "⟩", ":=", expr j₂.exists_compl_positive_negative],
  rw ["<-", expr hj] ["at", ident hT₂, ident hT₃],
  obtain ["⟨", ident hST₁, ",", "-", "⟩", ":=", expr of_symm_diff_compl_positive_negative hS₁.compl hT₁.compl ⟨hS₃, «expr ▸ »((compl_compl S).symm, hS₂)⟩ ⟨hT₃, «expr ▸ »((compl_compl T).symm, hT₂)⟩],
  refine [expr eq_of_pos_part_eq_pos_part _ hj],
  ext1 [] [ident i, ident hi],
  have [ident hμ₁] [":", expr «expr = »((j₁.pos_part i).to_real, j₁.to_signed_measure «expr ∩ »(i, «expr ᶜ»(S)))] [],
  { rw ["[", expr to_signed_measure, ",", expr to_signed_measure_sub_apply (hi.inter hS₁.compl), ",", expr show «expr = »(j₁.neg_part «expr ∩ »(i, «expr ᶜ»(S)), 0), by exact [expr nonpos_iff_eq_zero.1 «expr ▸ »(hS₅, measure_mono (set.inter_subset_right _ _))], ",", expr ennreal.zero_to_real, ",", expr sub_zero, "]"] [],
    conv_lhs [] [] { rw ["<-", expr set.inter_union_compl i S] },
    rw ["[", expr measure_union, ",", expr show «expr = »(j₁.pos_part «expr ∩ »(i, S), 0), by exact [expr nonpos_iff_eq_zero.1 «expr ▸ »(hS₄, measure_mono (set.inter_subset_right _ _))], ",", expr zero_add, "]"] [],
    { refine [expr set.disjoint_of_subset_left (set.inter_subset_right _ _) (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right)] },
    { exact [expr hi.inter hS₁] },
    { exact [expr hi.inter hS₁.compl] } },
  have [ident hμ₂] [":", expr «expr = »((j₂.pos_part i).to_real, j₂.to_signed_measure «expr ∩ »(i, «expr ᶜ»(T)))] [],
  { rw ["[", expr to_signed_measure, ",", expr to_signed_measure_sub_apply (hi.inter hT₁.compl), ",", expr show «expr = »(j₂.neg_part «expr ∩ »(i, «expr ᶜ»(T)), 0), by exact [expr nonpos_iff_eq_zero.1 «expr ▸ »(hT₅, measure_mono (set.inter_subset_right _ _))], ",", expr ennreal.zero_to_real, ",", expr sub_zero, "]"] [],
    conv_lhs [] [] { rw ["<-", expr set.inter_union_compl i T] },
    rw ["[", expr measure_union, ",", expr show «expr = »(j₂.pos_part «expr ∩ »(i, T), 0), by exact [expr nonpos_iff_eq_zero.1 «expr ▸ »(hT₄, measure_mono (set.inter_subset_right _ _))], ",", expr zero_add, "]"] [],
    { exact [expr set.disjoint_of_subset_left (set.inter_subset_right _ _) (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right)] },
    { exact [expr hi.inter hT₁] },
    { exact [expr hi.inter hT₁.compl] } },
  rw ["[", "<-", expr ennreal.to_real_eq_to_real (measure_ne_top _ _) (measure_ne_top _ _), ",", expr hμ₁, ",", expr hμ₂, ",", "<-", expr hj, "]"] [],
  exact [expr of_inter_eq_of_symm_diff_eq_zero_positive hS₁.compl hT₁.compl hi hS₃ hT₃ hST₁],
  all_goals { apply_instance }
end

@[simp]
theorem to_jordan_decomposition_to_signed_measure (j : jordan_decomposition α) :
  j.to_signed_measure.toJordanDecomposition = j :=
  (@to_signed_measure_injective _ _ j j.to_signed_measure.toJordanDecomposition
      (by 
        simp )).symm

end JordanDecomposition

namespace SignedMeasure

open JordanDecomposition

/-- `measure_theory.signed_measure.to_jordan_decomposition` and
`measure_theory.jordan_decomposition.to_signed_measure` form a `equiv`. -/
@[simps apply symmApply]
def to_jordan_decomposition_equiv (α : Type _) [MeasurableSpace α] : signed_measure α ≃ jordan_decomposition α :=
  { toFun := to_jordan_decomposition, invFun := to_signed_measure,
    left_inv := to_signed_measure_to_jordan_decomposition, right_inv := to_jordan_decomposition_to_signed_measure }

theorem to_jordan_decomposition_zero : (0 : signed_measure α).toJordanDecomposition = 0 :=
  by 
    apply to_signed_measure_injective 
    simp [to_signed_measure_zero]

theorem to_jordan_decomposition_neg (s : signed_measure α) : (-s).toJordanDecomposition = -s.to_jordan_decomposition :=
  by 
    apply to_signed_measure_injective 
    simp [to_signed_measure_neg]

theorem to_jordan_decomposition_smul (s : signed_measure α) (r :  ℝ≥0 ) :
  (r • s).toJordanDecomposition = r • s.to_jordan_decomposition :=
  by 
    apply to_signed_measure_injective 
    simp [to_signed_measure_smul]

private theorem to_jordan_decomposition_smul_real_nonneg (s : signed_measure α) (r : ℝ) (hr : 0 ≤ r) :
  (r • s).toJordanDecomposition = r • s.to_jordan_decomposition :=
  by 
    lift r to  ℝ≥0  using hr 
    rw [jordan_decomposition.coe_smul, ←to_jordan_decomposition_smul]
    rfl

theorem to_jordan_decomposition_smul_real (s : signed_measure α) (r : ℝ) :
  (r • s).toJordanDecomposition = r • s.to_jordan_decomposition :=
  by 
    byCases' hr : 0 ≤ r
    ·
      exact to_jordan_decomposition_smul_real_nonneg s r hr
    ·
      ext1
      ·
        rw [real_smul_pos_part_neg _ _ (not_leₓ.1 hr),
          show r • s = -(-r • s)by 
            rw [neg_smul, neg_negₓ],
          to_jordan_decomposition_neg, neg_pos_part, to_jordan_decomposition_smul_real_nonneg, ←smul_neg_part,
          real_smul_nonneg]
        all_goals 
          exact Left.nonneg_neg_iff.2 (le_of_ltₓ (not_leₓ.1 hr))
      ·
        rw [real_smul_neg_part_neg _ _ (not_leₓ.1 hr),
          show r • s = -(-r • s)by 
            rw [neg_smul, neg_negₓ],
          to_jordan_decomposition_neg, neg_neg_part, to_jordan_decomposition_smul_real_nonneg, ←smul_pos_part,
          real_smul_nonneg]
        all_goals 
          exact Left.nonneg_neg_iff.2 (le_of_ltₓ (not_leₓ.1 hr))

theorem to_jordan_decomposition_eq {s : signed_measure α} {j : jordan_decomposition α} (h : s = j.to_signed_measure) :
  s.to_jordan_decomposition = j :=
  by 
    rw [h, to_jordan_decomposition_to_signed_measure]

/-- The total variation of a signed measure. -/
def total_variation (s : signed_measure α) : Measureₓ α :=
  s.to_jordan_decomposition.pos_part+s.to_jordan_decomposition.neg_part

theorem total_variation_zero : (0 : signed_measure α).totalVariation = 0 :=
  by 
    simp [total_variation, to_jordan_decomposition_zero]

theorem total_variation_neg (s : signed_measure α) : (-s).totalVariation = s.total_variation :=
  by 
    simp [total_variation, to_jordan_decomposition_neg, add_commₓ]

theorem null_of_total_variation_zero (s : signed_measure α) {i : Set α} (hs : s.total_variation i = 0) : s i = 0 :=
  by 
    rw [total_variation, measure.coe_add, Pi.add_apply, add_eq_zero_iff] at hs 
    rw [←to_signed_measure_to_jordan_decomposition s, to_signed_measure, vector_measure.coe_sub, Pi.sub_apply,
      measure.to_signed_measure_apply, measure.to_signed_measure_apply]
    byCases' hi : MeasurableSet i
    ·
      rw [if_pos hi, if_pos hi]
      simp [hs.1, hs.2]
    ·
      simp [if_neg hi]

theorem absolutely_continuous_ennreal_iff (s : signed_measure α) (μ : vector_measure α ℝ≥0∞) :
  s ≪ᵥ μ ↔ s.total_variation ≪ μ.ennreal_to_measure :=
  by 
    split  <;> intro h
    ·
      refine' measure.absolutely_continuous.mk fun S hS₁ hS₂ => _ 
      obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.to_jordan_decomposition_spec 
      rw [total_variation, measure.add_apply, hpos, hneg, to_measure_of_zero_le_apply _ _ _ hS₁,
        to_measure_of_le_zero_apply _ _ _ hS₁]
      rw [←vector_measure.absolutely_continuous.ennreal_to_measure] at h 
      simp [h (measure_mono_null (i.inter_subset_right S) hS₂),
        h (measure_mono_null ((«expr ᶜ» i).inter_subset_right S) hS₂)]
    ·
      refine' vector_measure.absolutely_continuous.mk fun S hS₁ hS₂ => _ 
      rw [←vector_measure.ennreal_to_measure_apply hS₁] at hS₂ 
      exact null_of_total_variation_zero s (h hS₂)

-- error in MeasureTheory.Decomposition.Jordan: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem total_variation_absolutely_continuous_iff
(s : signed_measure α)
(μ : measure α) : «expr ↔ »(«expr ≪ »(s.total_variation, μ), «expr ∧ »(«expr ≪ »(s.to_jordan_decomposition.pos_part, μ), «expr ≪ »(s.to_jordan_decomposition.neg_part, μ))) :=
begin
  split; intro [ident h],
  { split,
    all_goals { refine [expr measure.absolutely_continuous.mk (λ S hS₁ hS₂, _)],
      have [] [] [":=", expr h hS₂],
      rw ["[", expr total_variation, ",", expr measure.add_apply, ",", expr add_eq_zero_iff, "]"] ["at", ident this] },
    exacts ["[", expr this.1, ",", expr this.2, "]"] },
  { refine [expr measure.absolutely_continuous.mk (λ S hS₁ hS₂, _)],
    rw ["[", expr total_variation, ",", expr measure.add_apply, ",", expr h.1 hS₂, ",", expr h.2 hS₂, ",", expr add_zero, "]"] [] }
end

theorem mutually_singular_iff (s t : signed_measure α) : s ⊥ᵥ t ↔ s.total_variation ⊥ₘ t.total_variation :=
  by 
    split 
    ·
      rintro ⟨u, hmeas, hu₁, hu₂⟩
      obtain ⟨i, hi₁, hi₂, hi₃, hipos, hineg⟩ := s.to_jordan_decomposition_spec 
      obtain ⟨j, hj₁, hj₂, hj₃, hjpos, hjneg⟩ := t.to_jordan_decomposition_spec 
      refine' ⟨u, hmeas, _, _⟩
      ·
        rw [total_variation, measure.add_apply, hipos, hineg, to_measure_of_zero_le_apply _ _ _ hmeas,
          to_measure_of_le_zero_apply _ _ _ hmeas]
        simp [hu₁ _ (Set.inter_subset_right _ _)]
      ·
        rw [total_variation, measure.add_apply, hjpos, hjneg, to_measure_of_zero_le_apply _ _ _ hmeas.compl,
          to_measure_of_le_zero_apply _ _ _ hmeas.compl]
        simp [hu₂ _ (Set.inter_subset_right _ _)]
    ·
      rintro ⟨u, hmeas, hu₁, hu₂⟩
      exact
        ⟨u, hmeas, fun t htu => null_of_total_variation_zero _ (measure_mono_null htu hu₁),
          fun t htv => null_of_total_variation_zero _ (measure_mono_null htv hu₂)⟩

theorem mutually_singular_ennreal_iff (s : signed_measure α) (μ : vector_measure α ℝ≥0∞) :
  s ⊥ᵥ μ ↔ s.total_variation ⊥ₘ μ.ennreal_to_measure :=
  by 
    split 
    ·
      rintro ⟨u, hmeas, hu₁, hu₂⟩
      obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.to_jordan_decomposition_spec 
      refine' ⟨u, hmeas, _, _⟩
      ·
        rw [total_variation, measure.add_apply, hpos, hneg, to_measure_of_zero_le_apply _ _ _ hmeas,
          to_measure_of_le_zero_apply _ _ _ hmeas]
        simp [hu₁ _ (Set.inter_subset_right _ _)]
      ·
        rw [vector_measure.ennreal_to_measure_apply hmeas.compl]
        exact hu₂ _ (Set.Subset.refl _)
    ·
      rintro ⟨u, hmeas, hu₁, hu₂⟩
      refine'
        vector_measure.mutually_singular.mk u hmeas
          (fun t htu _ => null_of_total_variation_zero _ (measure_mono_null htu hu₁)) fun t htv hmt => _ 
      rw [←vector_measure.ennreal_to_measure_apply hmt]
      exact measure_mono_null htv hu₂

theorem total_variation_mutually_singular_iff (s : signed_measure α) (μ : Measureₓ α) :
  s.total_variation ⊥ₘ μ ↔ s.to_jordan_decomposition.pos_part ⊥ₘ μ ∧ s.to_jordan_decomposition.neg_part ⊥ₘ μ :=
  measure.mutually_singular.add_left_iff

end SignedMeasure

end MeasureTheory

