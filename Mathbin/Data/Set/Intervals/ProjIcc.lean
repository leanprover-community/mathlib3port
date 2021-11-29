import Mathbin.Data.Set.Intervals.Basic

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `set.proj_Icc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `set.Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Icc a b h`.

We also prove some trivial properties of these maps.
-/


variable {α β : Type _} [LinearOrderₓ α]

open Function

namespace Set

/-- Projection of `α` to the closed interval `[a, b]`. -/
def proj_Icc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_leftₓ _ _, max_leₓ h (min_le_leftₓ _ _)⟩

variable {a b : α} (h : a ≤ b) {x : α}

theorem proj_Icc_of_le_left (hx : x ≤ a) : proj_Icc a b h x = ⟨a, left_mem_Icc.2 h⟩ :=
  by 
    simp [proj_Icc, hx, hx.trans h]

@[simp]
theorem proj_Icc_left : proj_Icc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
  proj_Icc_of_le_left h le_rfl

theorem proj_Icc_of_right_le (hx : b ≤ x) : proj_Icc a b h x = ⟨b, right_mem_Icc.2 h⟩ :=
  by 
    simp [proj_Icc, hx, h]

@[simp]
theorem proj_Icc_right : proj_Icc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
  proj_Icc_of_right_le h le_rfl

theorem proj_Icc_eq_left (h : a < b) : proj_Icc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a :=
  by 
    refine' ⟨fun h' => _, proj_Icc_of_le_left _⟩
    simpRw [Subtype.ext_iff_val, proj_Icc, max_eq_left_iff, min_le_iff, h.not_le, false_orₓ]  at h' 
    exact h'

-- error in Data.Set.Intervals.ProjIcc: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem proj_Icc_eq_right
(h : «expr < »(a, b)) : «expr ↔ »(«expr = »(proj_Icc a b h.le x, ⟨b, right_mem_Icc.mpr h.le⟩), «expr ≤ »(b, x)) :=
begin
  refine [expr ⟨λ h', _, proj_Icc_of_right_le _⟩],
  simp_rw ["[", expr subtype.ext_iff_val, ",", expr proj_Icc, "]"] ["at", ident h'],
  have [] [] [":=", expr ((max_choice _ _).resolve_left (by simp [] [] [] ["[", expr h.ne', ",", expr h', "]"] [] [])).symm.trans h'],
  exact [expr min_eq_left_iff.mp this]
end

theorem proj_Icc_of_mem (hx : x ∈ Icc a b) : proj_Icc a b h x = ⟨x, hx⟩ :=
  by 
    simp [proj_Icc, hx.1, hx.2]

@[simp]
theorem proj_Icc_coe (x : Icc a b) : proj_Icc a b h x = x :=
  by 
    cases x 
    apply proj_Icc_of_mem

theorem proj_Icc_surj_on : surj_on (proj_Icc a b h) (Icc a b) univ :=
  fun x _ => ⟨x, x.2, proj_Icc_coe h x⟩

theorem proj_Icc_surjective : surjective (proj_Icc a b h) :=
  fun x => ⟨x, proj_Icc_coe h x⟩

@[simp]
theorem range_proj_Icc : range (proj_Icc a b h) = univ :=
  (proj_Icc_surjective h).range_eq

theorem monotone_proj_Icc : Monotone (proj_Icc a b h) :=
  fun x y hxy => max_le_max le_rfl$ min_le_min le_rfl hxy

theorem strict_mono_on_proj_Icc : StrictMonoOn (proj_Icc a b h) (Icc a b) :=
  fun x hx y hy hxy =>
    by 
      simpa only [proj_Icc_of_mem, hx, hy]

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β) : α → β :=
  f ∘ proj_Icc a b h

@[simp]
theorem Icc_extend_range (f : Icc a b → β) : range (Icc_extend h f) = range f :=
  by 
    simp [Icc_extend, range_comp f]

theorem Icc_extend_of_le_left (f : Icc a b → β) (hx : x ≤ a) : Icc_extend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
  congr_argₓ f$ proj_Icc_of_le_left h hx

@[simp]
theorem Icc_extend_left (f : Icc a b → β) : Icc_extend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
  Icc_extend_of_le_left h f le_rfl

theorem Icc_extend_of_right_le (f : Icc a b → β) (hx : b ≤ x) : Icc_extend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
  congr_argₓ f$ proj_Icc_of_right_le h hx

@[simp]
theorem Icc_extend_right (f : Icc a b → β) : Icc_extend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
  Icc_extend_of_right_le h f le_rfl

theorem Icc_extend_of_mem (f : Icc a b → β) (hx : x ∈ Icc a b) : Icc_extend h f x = f ⟨x, hx⟩ :=
  congr_argₓ f$ proj_Icc_of_mem h hx

@[simp]
theorem Icc_extend_coe (f : Icc a b → β) (x : Icc a b) : Icc_extend h f x = f x :=
  congr_argₓ f$ proj_Icc_coe h x

end Set

open Set

variable [Preorderₓ β] {a b : α} (h : a ≤ b) {f : Icc a b → β}

theorem Monotone.Icc_extend (hf : Monotone f) : Monotone (Icc_extend h f) :=
  hf.comp$ monotone_proj_Icc h

theorem StrictMono.strict_mono_on_Icc_extend (hf : StrictMono f) : StrictMonoOn (Icc_extend h f) (Icc a b) :=
  hf.comp_strict_mono_on (strict_mono_on_proj_Icc h)

