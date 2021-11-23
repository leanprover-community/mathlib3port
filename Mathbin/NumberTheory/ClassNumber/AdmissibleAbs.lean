import Mathbin.Algebra.Algebra.Basic 
import Mathbin.NumberTheory.ClassNumber.AdmissibleAbsoluteValue

/-!
# Admissible absolute value on the integers
This file defines an admissible absolute value `absolute_value.abs_is_admissible`
which we use to show the class number of the ring of integers of a number field
is finite.

## Main results

 * `absolute_value.abs_is_admissible` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is admissible.
-/


namespace AbsoluteValue

open Int

-- error in NumberTheory.ClassNumber.AdmissibleAbs: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- We can partition a finite family into `partition_card ε` sets, such that the remainders
in each set are close together. -/
theorem exists_partition_int
(n : exprℕ())
{ε : exprℝ()}
(hε : «expr < »(0, ε))
{b : exprℤ()}
(hb : «expr ≠ »(b, 0))
(A : fin n → exprℤ()) : «expr∃ , »((t : fin n → fin «expr⌈ ⌉₊»(«expr / »(1, ε))), ∀
 i₀
 i₁, «expr = »(t i₀, t i₁) → «expr < »(«expr↑ »(abs «expr - »(«expr % »(A i₁, b), «expr % »(A i₀, b))), «expr • »(abs b, ε))) :=
begin
  have [ident hb'] [":", expr «expr < »((0 : exprℝ()), «expr↑ »(abs b))] [":=", expr int.cast_pos.mpr (abs_pos.mpr hb)],
  have [ident hbε] [":", expr «expr < »(0, «expr • »(abs b, ε))] [],
  { rw [expr algebra.smul_def] [],
    exact [expr mul_pos hb' hε] },
  have [ident hfloor] [":", expr ∀
   i, «expr ≤ »(0, floor («expr / »((«expr % »(A i, b) : exprℤ()), «expr • »(abs b, ε)) : exprℝ()))] [],
  { intro [ident i],
    exact [expr floor_nonneg.mpr (div_nonneg (cast_nonneg.mpr (mod_nonneg _ hb)) hbε.le)] },
  refine [expr ⟨λ
    i, ⟨nat_abs (floor («expr / »((«expr % »(A i, b) : exprℤ()), «expr • »(abs b, ε)) : exprℝ())), _⟩, _⟩],
  { rw ["[", "<-", expr coe_nat_lt, ",", expr nat_abs_of_nonneg (hfloor i), ",", expr floor_lt, "]"] [],
    apply [expr lt_of_lt_of_le _ (nat.le_ceil _)],
    rw ["[", expr algebra.smul_def, ",", expr ring_hom.eq_int_cast, ",", "<-", expr div_div_eq_div_mul, ",", expr div_lt_div_right hε, ",", expr div_lt_iff hb', ",", expr one_mul, ",", expr cast_lt, "]"] [],
    exact [expr int.mod_lt _ hb] },
  intros [ident i₀, ident i₁, ident hi],
  have [ident hi] [":", expr «expr = »((«expr⌊ ⌋»(«expr / »(«expr↑ »(«expr % »(A i₀, b)), «expr • »(abs b, ε))).nat_abs : exprℤ()), «expr⌊ ⌋»(«expr / »(«expr↑ »(«expr % »(A i₁, b)), «expr • »(abs b, ε))).nat_abs)] [":=", expr congr_arg (coe : exprℕ() → exprℤ()) (subtype.mk_eq_mk.mp hi)],
  rw ["[", expr nat_abs_of_nonneg (hfloor i₀), ",", expr nat_abs_of_nonneg (hfloor i₁), "]"] ["at", ident hi],
  have [ident hi] [] [":=", expr abs_sub_lt_one_of_floor_eq_floor hi],
  rw ["[", expr abs_sub_comm, ",", "<-", expr sub_div, ",", expr abs_div, ",", expr abs_of_nonneg hbε.le, ",", expr div_lt_iff hbε, ",", expr one_mul, "]"] ["at", ident hi],
  rwa ["[", expr int.cast_abs, ",", expr int.cast_sub, "]"] []
end

/-- `abs : ℤ → ℤ` is an admissible absolute value -/
noncomputable def abs_is_admissible : is_admissible AbsoluteValue.abs :=
  { AbsoluteValue.abs_is_euclidean with card := fun ε => ⌈1 / ε⌉₊,
    exists_partition' := fun n ε hε b hb => exists_partition_int n hε hb }

noncomputable instance  : Inhabited (is_admissible AbsoluteValue.abs) :=
  ⟨abs_is_admissible⟩

end AbsoluteValue

