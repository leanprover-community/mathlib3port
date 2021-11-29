import Mathbin.Order.Bounds 
import Mathbin.Data.Set.Intervals.ImagePreimage

/-!
# Intervals without endpoints ordering

In any decidable linear order `α`, we define the set of elements lying between two elements `a` and
`b` as `Icc (min a b) (max a b)`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `Icc (min a b) (max a b)` is the same as `segment ℝ a b`.

## Notation

We use the localized notation `[a, b]` for `interval a b`. One can open the locale `interval` to
make the notation available.

-/


universe u

open_locale Pointwise

namespace Set

section LinearOrderₓ

variable{α : Type u}[LinearOrderₓ α]{a a₁ a₂ b b₁ b₂ x : α}

/-- `interval a b` is the set of elements lying between `a` and `b`, with `a` and `b` included. -/
def interval (a b : α) :=
  Icc (min a b) (max a b)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp] theorem interval_of_le (h : «expr ≤ »(a, b)) : «expr = »(«expr[ , ]»(a, b), Icc a b) :=
by rw ["[", expr interval, ",", expr min_eq_left h, ",", expr max_eq_right h, "]"] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp] theorem interval_of_ge (h : «expr ≤ »(b, a)) : «expr = »(«expr[ , ]»(a, b), Icc b a) :=
by { rw ["[", expr interval, ",", expr min_eq_right h, ",", expr max_eq_left h, "]"] [] }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_swap (a b : α) : «expr = »(«expr[ , ]»(a, b), «expr[ , ]»(b, a)) :=
or.elim (le_total a b) (by simp [] [] [] [] [] [] { contextual := tt }) (by simp [] [] [] [] [] [] { contextual := tt })

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_of_lt (h : «expr < »(a, b)) : «expr = »(«expr[ , ]»(a, b), Icc a b) := interval_of_le (le_of_lt h)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_of_gt (h : «expr < »(b, a)) : «expr = »(«expr[ , ]»(a, b), Icc b a) := interval_of_ge (le_of_lt h)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_of_not_le (h : «expr¬ »(«expr ≤ »(a, b))) : «expr = »(«expr[ , ]»(a, b), Icc b a) :=
interval_of_gt (lt_of_not_ge h)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_of_not_ge (h : «expr¬ »(«expr ≤ »(b, a))) : «expr = »(«expr[ , ]»(a, b), Icc a b) :=
interval_of_lt (lt_of_not_ge h)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp] theorem interval_self : «expr = »(«expr[ , ]»(a, a), {a}) :=
«expr $ »(set.ext, by simp [] [] [] ["[", expr le_antisymm_iff, ",", expr and_comm, "]"] [] [])

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp] theorem nonempty_interval : set.nonempty «expr[ , ]»(a, b) :=
by { simp [] [] ["only"] ["[", expr interval, ",", expr min_le_iff, ",", expr le_max_iff, ",", expr nonempty_Icc, "]"] [] [],
  left,
  left,
  refl }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp] theorem left_mem_interval : «expr ∈ »(a, «expr[ , ]»(a, b)) :=
by { rw ["[", expr interval, ",", expr mem_Icc, "]"] [],
  exact [expr ⟨min_le_left _ _, le_max_left _ _⟩] }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp] theorem right_mem_interval : «expr ∈ »(b, «expr[ , ]»(a, b)) :=
by { rw [expr interval_swap] [],
  exact [expr left_mem_interval] }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem Icc_subset_interval : «expr ⊆ »(Icc a b, «expr[ , ]»(a, b)) :=
by { assume [binders (x h)],
  rwa [expr interval_of_le] [],
  exact [expr le_trans h.1 h.2] }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem Icc_subset_interval' : «expr ⊆ »(Icc b a, «expr[ , ]»(a, b)) :=
by { rw [expr interval_swap] [],
  apply [expr Icc_subset_interval] }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem mem_interval_of_le (ha : «expr ≤ »(a, x)) (hb : «expr ≤ »(x, b)) : «expr ∈ »(x, «expr[ , ]»(a, b)) :=
Icc_subset_interval ⟨ha, hb⟩

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem mem_interval_of_ge (hb : «expr ≤ »(b, x)) (ha : «expr ≤ »(x, a)) : «expr ∈ »(x, «expr[ , ]»(a, b)) :=
Icc_subset_interval' ⟨hb, ha⟩

theorem not_mem_interval_of_lt {c : α} (ha : c < a) (hb : c < b) : c ∉ interval a b :=
  not_mem_Icc_of_lt$ lt_min_iff.mpr ⟨ha, hb⟩

theorem not_mem_interval_of_gt {c : α} (ha : a < c) (hb : b < c) : c ∉ interval a b :=
  not_mem_Icc_of_gt$ max_lt_iff.mpr ⟨ha, hb⟩

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_subset_interval
(h₁ : «expr ∈ »(a₁, «expr[ , ]»(a₂, b₂)))
(h₂ : «expr ∈ »(b₁, «expr[ , ]»(a₂, b₂))) : «expr ⊆ »(«expr[ , ]»(a₁, b₁), «expr[ , ]»(a₂, b₂)) :=
Icc_subset_Icc (le_min h₁.1 h₂.1) (max_le h₁.2 h₂.2)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_subset_Icc
(ha : «expr ∈ »(a₁, Icc a₂ b₂))
(hb : «expr ∈ »(b₁, Icc a₂ b₂)) : «expr ⊆ »(«expr[ , ]»(a₁, b₁), Icc a₂ b₂) :=
Icc_subset_Icc (le_min ha.1 hb.1) (max_le ha.2 hb.2)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_subset_interval_iff_mem : «expr ↔ »(«expr ⊆ »(«expr[ , ]»(a₁, b₁), «expr[ , ]»(a₂, b₂)), «expr ∧ »(«expr ∈ »(a₁, «expr[ , ]»(a₂, b₂)), «expr ∈ »(b₁, «expr[ , ]»(a₂, b₂)))) :=
iff.intro (λ h, ⟨h left_mem_interval, h right_mem_interval⟩) (λ h, interval_subset_interval h.1 h.2)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_subset_interval_iff_le : «expr ↔ »(«expr ⊆ »(«expr[ , ]»(a₁, b₁), «expr[ , ]»(a₂, b₂)), «expr ∧ »(«expr ≤ »(min a₂ b₂, min a₁ b₁), «expr ≤ »(max a₁ b₁, max a₂ b₂))) :=
by { rw ["[", expr interval, ",", expr interval, ",", expr Icc_subset_Icc_iff, "]"] [],
  exact [expr min_le_max] }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_subset_interval_right
(h : «expr ∈ »(x, «expr[ , ]»(a, b))) : «expr ⊆ »(«expr[ , ]»(x, b), «expr[ , ]»(a, b)) :=
interval_subset_interval h right_mem_interval

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_subset_interval_left
(h : «expr ∈ »(x, «expr[ , ]»(a, b))) : «expr ⊆ »(«expr[ , ]»(a, x), «expr[ , ]»(a, b)) :=
interval_subset_interval left_mem_interval h

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem bdd_below_bdd_above_iff_subset_interval
(s : set α) : «expr ↔ »(«expr ∧ »(bdd_below s, bdd_above s), «expr∃ , »((a b), «expr ⊆ »(s, «expr[ , ]»(a, b)))) :=
begin
  rw ["[", expr bdd_below_bdd_above_iff_subset_Icc, "]"] [],
  split,
  { rintro ["⟨", ident a, ",", ident b, ",", ident h, "⟩"],
    exact [expr ⟨a, b, λ x hx, Icc_subset_interval (h hx)⟩] },
  { rintro ["⟨", ident a, ",", ident b, ",", ident h, "⟩"],
    exact [expr ⟨min a b, max a b, h⟩] }
end

/-- The open-closed interval with unordered bounds. -/
def interval_oc : α → α → Set α :=
  fun a b => Ioc (min a b) (max a b)

localized [Interval] notation "Ι" => Set.IntervalOc

theorem interval_oc_of_le (h : a ≤ b) : Ι a b = Ioc a b :=
  by 
    simp [interval_oc, h]

theorem interval_oc_of_lt (h : b < a) : Ι a b = Ioc b a :=
  by 
    simp [interval_oc, le_of_ltₓ h]

theorem forall_interval_oc_iff {P : α → Prop} :
  (∀ x (_ : x ∈ Ι a b), P x) ↔ (∀ x (_ : x ∈ Ioc a b), P x) ∧ ∀ x (_ : x ∈ Ioc b a), P x :=
  by 
    dsimp [interval_oc]
    cases' le_totalₓ a b with hab hab <;> simp [hab]

end LinearOrderₓ

open_locale Interval

section OrderedAddCommGroup

variable{α : Type u}[LinearOrderedAddCommGroup α](a b c x y : α)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem preimage_const_add_interval : «expr = »(«expr ⁻¹' »(λ
  x, «expr + »(a, x), «expr[ , ]»(b, c)), «expr[ , ]»(«expr - »(b, a), «expr - »(c, a))) :=
by simp [] [] ["only"] ["[", expr interval, ",", expr preimage_const_add_Icc, ",", expr min_sub_sub_right, ",", expr max_sub_sub_right, "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem preimage_add_const_interval : «expr = »(«expr ⁻¹' »(λ
  x, «expr + »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr - »(b, a), «expr - »(c, a))) :=
by simpa [] [] ["only"] ["[", expr add_comm, "]"] [] ["using", expr preimage_const_add_interval a b c]

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp] theorem preimage_neg_interval : «expr = »(«expr- »(«expr[ , ]»(a, b)), «expr[ , ]»(«expr- »(a), «expr- »(b))) :=
by simp [] [] ["only"] ["[", expr interval, ",", expr preimage_neg_Icc, ",", expr min_neg_neg, ",", expr max_neg_neg, "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem preimage_sub_const_interval : «expr = »(«expr ⁻¹' »(λ
  x, «expr - »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr + »(b, a), «expr + »(c, a))) :=
by simp [] [] [] ["[", expr sub_eq_add_neg, "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem preimage_const_sub_interval : «expr = »(«expr ⁻¹' »(λ
  x, «expr - »(a, x), «expr[ , ]»(b, c)), «expr[ , ]»(«expr - »(a, b), «expr - »(a, c))) :=
by { rw ["[", expr interval, ",", expr interval, ",", expr preimage_const_sub_Icc, "]"] [],
  simp [] [] ["only"] ["[", expr sub_eq_add_neg, ",", expr min_add_add_left, ",", expr max_add_add_left, ",", expr min_neg_neg, ",", expr max_neg_neg, "]"] [] [] }

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem image_const_add_interval : «expr = »(«expr '' »(λ
  x, «expr + »(a, x), «expr[ , ]»(b, c)), «expr[ , ]»(«expr + »(a, b), «expr + »(a, c))) :=
by simp [] [] [] ["[", expr add_comm, "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem image_add_const_interval : «expr = »(«expr '' »(λ
  x, «expr + »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr + »(b, a), «expr + »(c, a))) :=
by simp [] [] [] [] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem image_const_sub_interval : «expr = »(«expr '' »(λ
  x, «expr - »(a, x), «expr[ , ]»(b, c)), «expr[ , ]»(«expr - »(a, b), «expr - »(a, c))) :=
by simp [] [] [] ["[", expr sub_eq_add_neg, ",", expr image_comp (λ x, «expr + »(a, x)) (λ x, «expr- »(x)), "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem image_sub_const_interval : «expr = »(«expr '' »(λ
  x, «expr - »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr - »(b, a), «expr - »(c, a))) :=
by simp [] [] [] ["[", expr sub_eq_add_neg, ",", expr add_comm, "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem image_neg_interval : «expr = »(«expr '' »(has_neg.neg, «expr[ , ]»(a, b)), «expr[ , ]»(«expr- »(a), «expr- »(b))) :=
by simp [] [] [] [] [] []

variable{a b c x y}

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
/-- If `[x, y]` is a subinterval of `[a, b]`, then the distance between `x` and `y`
is less than or equal to that of `a` and `b` -/
theorem abs_sub_le_of_subinterval
(h : «expr ⊆ »(«expr[ , ]»(x, y), «expr[ , ]»(a, b))) : «expr ≤ »(«expr| |»(«expr - »(y, x)), «expr| |»(«expr - »(b, a))) :=
begin
  rw ["[", "<-", expr max_sub_min_eq_abs, ",", "<-", expr max_sub_min_eq_abs, "]"] [],
  rw ["[", expr interval_subset_interval_iff_le, "]"] ["at", ident h],
  exact [expr sub_le_sub h.2 h.1]
end

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
/-- If `x ∈ [a, b]`, then the distance between `a` and `x` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_left_of_mem_interval
(h : «expr ∈ »(x, «expr[ , ]»(a, b))) : «expr ≤ »(«expr| |»(«expr - »(x, a)), «expr| |»(«expr - »(b, a))) :=
abs_sub_le_of_subinterval (interval_subset_interval_left h)

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
/-- If `x ∈ [a, b]`, then the distance between `x` and `b` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_right_of_mem_interval
(h : «expr ∈ »(x, «expr[ , ]»(a, b))) : «expr ≤ »(«expr| |»(«expr - »(b, x)), «expr| |»(«expr - »(b, a))) :=
abs_sub_le_of_subinterval (interval_subset_interval_right h)

end OrderedAddCommGroup

section LinearOrderedField

variable{k : Type u}[LinearOrderedField k]{a : k}

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem preimage_mul_const_interval
(ha : «expr ≠ »(a, 0))
(b
 c : k) : «expr = »(«expr ⁻¹' »(λ
  x, «expr * »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr / »(b, a), «expr / »(c, a))) :=
(lt_or_gt_of_ne ha).elim (λ
 ha, by simp [] [] [] ["[", expr interval, ",", expr ha, ",", expr ha.le, ",", expr min_div_div_right_of_nonpos, ",", expr max_div_div_right_of_nonpos, "]"] [] []) (λ
 ha : «expr < »(0, a), by simp [] [] [] ["[", expr interval, ",", expr ha, ",", expr ha.le, ",", expr min_div_div_right, ",", expr max_div_div_right, "]"] [] [])

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem preimage_const_mul_interval
(ha : «expr ≠ »(a, 0))
(b
 c : k) : «expr = »(«expr ⁻¹' »(λ
  x, «expr * »(a, x), «expr[ , ]»(b, c)), «expr[ , ]»(«expr / »(b, a), «expr / »(c, a))) :=
by simp [] [] ["only"] ["[", "<-", expr preimage_mul_const_interval ha, ",", expr mul_comm, "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem preimage_div_const_interval
(ha : «expr ≠ »(a, 0))
(b
 c : k) : «expr = »(«expr ⁻¹' »(λ
  x, «expr / »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr * »(b, a), «expr * »(c, a))) :=
by simp [] [] ["only"] ["[", expr div_eq_mul_inv, ",", expr preimage_mul_const_interval (inv_ne_zero ha), ",", expr inv_inv₀, "]"] [] []

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem image_mul_const_interval
(a
 b
 c : k) : «expr = »(«expr '' »(λ
  x, «expr * »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr * »(b, a), «expr * »(c, a))) :=
if ha : «expr = »(a, 0) then by simp [] [] [] ["[", expr ha, "]"] [] [] else calc
  «expr = »(«expr '' »(λ
    x, «expr * »(x, a), «expr[ , ]»(b, c)), «expr ⁻¹' »(λ
    x, «expr * »(x, «expr ⁻¹»(a)), «expr[ , ]»(b, c))) : (units.mk0 a ha).mul_right.image_eq_preimage _
  «expr = »(..., «expr ⁻¹' »(λ
    x, «expr / »(x, a), «expr[ , ]»(b, c))) : by simp [] [] ["only"] ["[", expr div_eq_mul_inv, "]"] [] []
  «expr = »(..., «expr[ , ]»(«expr * »(b, a), «expr * »(c, a))) : preimage_div_const_interval ha _ _

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem image_const_mul_interval
(a
 b
 c : k) : «expr = »(«expr '' »(λ
  x, «expr * »(a, x), «expr[ , ]»(b, c)), «expr[ , ]»(«expr * »(a, b), «expr * »(a, c))) :=
by simpa [] [] ["only"] ["[", expr mul_comm, "]"] [] ["using", expr image_mul_const_interval a b c]

-- error in Data.Set.Intervals.UnorderedInterval: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem image_div_const_interval
(a
 b
 c : k) : «expr = »(«expr '' »(λ
  x, «expr / »(x, a), «expr[ , ]»(b, c)), «expr[ , ]»(«expr / »(b, a), «expr / »(c, a))) :=
by simp [] [] ["only"] ["[", expr div_eq_mul_inv, ",", expr image_mul_const_interval, "]"] [] []

end LinearOrderedField

end Set

