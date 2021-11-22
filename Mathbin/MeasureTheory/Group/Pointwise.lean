import Mathbin.MeasureTheory.Group.Arithmetic

/-!
# Pointwise set operations on `measurable_set`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `measurable_set.mul` etc.
-/


open_locale Pointwise

open Set

@[toAdditive]
theorem MeasurableSet.const_smul {G α : Type _} [Groupₓ G] [MulAction G α] [MeasurableSpace G] [MeasurableSpace α]
  [HasMeasurableSmul G α] {s : Set α} (hs : MeasurableSet s) (a : G) : MeasurableSet (a • s) :=
  by 
    rw [←preimage_smul_inv]
    exact measurable_const_smul _ hs

theorem MeasurableSet.const_smul_of_ne_zero {G₀ α : Type _} [GroupWithZeroₓ G₀] [MulAction G₀ α] [MeasurableSpace G₀]
  [MeasurableSpace α] [HasMeasurableSmul G₀ α] {s : Set α} (hs : MeasurableSet s) {a : G₀} (ha : a ≠ 0) :
  MeasurableSet (a • s) :=
  by 
    rw [←preimage_smul_inv₀ ha]
    exact measurable_const_smul _ hs

-- error in MeasureTheory.Group.Pointwise: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem measurable_set.const_smul₀
{G₀ α : Type*}
[group_with_zero G₀]
[has_zero α]
[mul_action_with_zero G₀ α]
[measurable_space G₀]
[measurable_space α]
[has_measurable_smul G₀ α]
[measurable_singleton_class α]
{s : set α}
(hs : measurable_set s)
(a : G₀) : measurable_set «expr • »(a, s) :=
begin
  rcases [expr eq_or_ne a 0, "with", "(", ident rfl, "|", ident ha, ")"],
  exacts ["[", expr (subsingleton_zero_smul_set s).measurable_set, ",", expr hs.const_smul_of_ne_zero ha, "]"]
end

