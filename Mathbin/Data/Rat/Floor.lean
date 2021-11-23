import Mathbin.Algebra.Order.Floor 
import Mathbin.Tactic.FieldSimp

/-!
# Floor Function for Rational Numbers

## Summary

We define the `floor` function and the `floor_ring` instance on `ℚ`. Some technical lemmas relating
`floor` to integer division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/


open Int

namespace Rat

/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
protected def floor : ℚ → ℤ
| ⟨n, d, h, c⟩ => n / d

-- error in Data.Rat.Floor: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem le_floor {z : exprℤ()} : ∀ {r : exprℚ()}, «expr ↔ »(«expr ≤ »(z, rat.floor r), «expr ≤ »((z : exprℚ()), r))
| ⟨n, d, h, c⟩ := begin
  simp [] [] [] ["[", expr rat.floor, "]"] [] [],
  rw ["[", expr num_denom', "]"] [],
  have [ident h'] [] [":=", expr int.coe_nat_lt.2 h],
  conv [] [] { to_rhs,
    rw ["[", expr coe_int_eq_mk, ",", expr rat.le_def zero_lt_one h', ",", expr mul_one, "]"] },
  exact [expr int.le_div_iff_mul_le h']
end

instance  : FloorRing ℚ :=
  FloorRing.ofFloor ℚ Rat.floor$ fun a z => Rat.le_floor.symm

protected theorem floor_def {q : ℚ} : ⌊q⌋ = q.num / q.denom :=
  by 
    cases q 
    rfl

-- error in Data.Rat.Floor: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem floor_int_div_nat_eq_div
{n : exprℤ()}
{d : exprℕ()} : «expr = »(«expr⌊ ⌋»(«expr / »((«expr↑ »(n) : exprℚ()), («expr↑ »(d) : exprℚ()))), «expr / »(n, («expr↑ »(d) : exprℤ()))) :=
begin
  rw ["[", expr rat.floor_def, "]"] [],
  cases [expr decidable.em «expr = »(d, 0)] ["with", ident d_eq_zero, ident d_ne_zero],
  { simp [] [] [] ["[", expr d_eq_zero, "]"] [] [] },
  { cases [expr decidable.em «expr = »(n, 0)] ["with", ident n_eq_zero, ident n_ne_zero],
    { simp [] [] [] ["[", expr n_eq_zero, "]"] [] [] },
    { set [] [ident q] [] [":="] [expr «expr / »((n : exprℚ()), d)] ["with", ident q_eq],
      obtain ["⟨", ident c, ",", ident n_eq_c_mul_num, ",", ident d_eq_c_mul_denom, "⟩", ":", expr «expr∃ , »((c), «expr ∧ »(«expr = »(n, «expr * »(c, q.num)), «expr = »((d : exprℤ()), «expr * »(c, q.denom))))],
      by { rw [expr q_eq] [],
        exact_mod_cast [expr @rat.exists_eq_mul_div_num_and_eq_mul_div_denom n d n_ne_zero (by exact_mod_cast [expr d_ne_zero])] },
      suffices [] [":", expr «expr = »(«expr / »(q.num, q.denom), «expr / »(«expr * »(c, q.num), «expr * »(c, q.denom)))],
      by rwa ["[", expr n_eq_c_mul_num, ",", expr d_eq_c_mul_denom, "]"] [],
      suffices [] [":", expr «expr > »(c, 0)],
      by solve_by_elim [] [] ["[", expr int.mul_div_mul_of_pos, "]"] [],
      have [ident q_denom_mul_c_pos] [":", expr «expr < »((0 : exprℤ()), «expr * »(q.denom, c))] [],
      by { have [] [":", expr «expr > »((d : exprℤ()), 0)] [],
        by exact_mod_cast [expr pos_iff_ne_zero.elim_right d_ne_zero],
        rwa ["[", expr d_eq_c_mul_denom, ",", expr mul_comm, "]"] ["at", ident this] },
      suffices [] [":", expr «expr ≤ »((0 : exprℤ()), q.denom)],
      from [expr pos_of_mul_pos_left q_denom_mul_c_pos this],
      exact_mod_cast [expr le_of_lt q.pos] } }
end

end Rat

theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d*⌊(n : ℚ) / d⌋ :=
  by 
    rw [eq_sub_of_add_eq$ Int.mod_add_div n d, Rat.floor_int_div_nat_eq_div]

-- error in Data.Rat.Floor: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat.coprime_sub_mul_floor_rat_div_of_coprime
{n d : exprℕ()}
(n_coprime_d : n.coprime d) : «expr - »((n : exprℤ()), «expr * »(d, «expr⌊ ⌋»(«expr / »((n : exprℚ()), d)))).nat_abs.coprime d :=
begin
  have [] [":", expr «expr = »(«expr % »((n : exprℤ()), d), «expr - »(n, «expr * »(d, «expr⌊ ⌋»(«expr / »((n : exprℚ()), d)))))] [],
  from [expr int.mod_nat_eq_sub_mul_floor_rat_div],
  rw ["<-", expr this] [],
  have [] [":", expr d.coprime n] [],
  from [expr n_coprime_d.symm],
  rwa ["[", expr nat.coprime, ",", expr nat.gcd_rec, "]"] ["at", ident this]
end

namespace Rat

-- error in Data.Rat.Floor: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem num_lt_succ_floor_mul_denom (q : exprℚ()) : «expr < »(q.num, «expr * »(«expr + »(«expr⌊ ⌋»(q), 1), q.denom)) :=
begin
  suffices [] [":", expr «expr < »((q.num : exprℚ()), «expr * »(«expr + »(«expr⌊ ⌋»(q), 1), q.denom))],
  by exact_mod_cast [expr this],
  suffices [] [":", expr «expr < »((q.num : exprℚ()), «expr * »(«expr + »(«expr - »(q, fract q), 1), q.denom))],
  by { have [] [":", expr «expr = »((«expr⌊ ⌋»(q) : exprℚ()), «expr - »(q, fract q))] [],
    from [expr «expr $ »(eq_sub_of_add_eq, floor_add_fract q)],
    rwa [expr this] [] },
  suffices [] [":", expr «expr < »((q.num : exprℚ()), «expr + »(q.num, «expr * »(«expr - »(1, fract q), q.denom)))],
  by { have [] [":", expr «expr = »(«expr * »(«expr + »(«expr - »(q, fract q), 1), q.denom), «expr + »(q.num, «expr * »(«expr - »(1, fract q), q.denom)))] [],
    calc
      «expr = »(«expr * »(«expr + »(«expr - »(q, fract q), 1), q.denom), «expr * »(«expr + »(q, «expr - »(1, fract q)), q.denom)) : by ring []
      «expr = »(..., «expr + »(«expr * »(q, q.denom), «expr * »(«expr - »(1, fract q), q.denom))) : by rw [expr add_mul] []
      «expr = »(..., «expr + »(q.num, «expr * »(«expr - »(1, fract q), q.denom))) : by simp [] [] [] [] [] [],
    rwa [expr this] [] },
  suffices [] [":", expr «expr < »(0, «expr * »(«expr - »(1, fract q), q.denom))],
  by { rw ["<-", expr sub_lt_iff_lt_add'] [],
    simpa [] [] [] [] [] [] },
  have [] [":", expr «expr < »(0, «expr - »(1, fract q))] [],
  by { have [] [":", expr «expr < »(fract q, 1)] [],
    from [expr fract_lt_one q],
    have [] [":", expr «expr < »(«expr + »(0, fract q), 1)] [],
    by simp [] [] [] ["[", expr this, "]"] [] [],
    rwa [expr lt_sub_iff_add_lt] [] },
  exact [expr mul_pos this (by exact_mod_cast [expr q.pos])]
end

-- error in Data.Rat.Floor: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fract_inv_num_lt_num_of_pos
{q : exprℚ()}
(q_pos : «expr < »(0, q)) : «expr < »((fract «expr ⁻¹»(q)).num, q.num) :=
begin
  have [ident q_num_pos] [":", expr «expr < »(0, q.num)] [],
  from [expr rat.num_pos_iff_pos.elim_right q_pos],
  have [ident q_num_abs_eq_q_num] [":", expr «expr = »((q.num.nat_abs : exprℤ()), q.num)] [],
  from [expr int.nat_abs_of_nonneg q_num_pos.le],
  set [] [ident q_inv] [] [":="] [expr «expr / »((q.denom : exprℚ()), q.num)] ["with", ident q_inv_def],
  have [ident q_inv_eq] [":", expr «expr = »(«expr ⁻¹»(q), q_inv)] [],
  from [expr rat.inv_def'],
  suffices [] [":", expr «expr < »(«expr - »(q_inv, «expr⌊ ⌋»(q_inv)).num, q.num)],
  by rwa [expr q_inv_eq] [],
  suffices [] [":", expr «expr < »(«expr / »((«expr - »(q.denom, «expr * »(q.num, «expr⌊ ⌋»(q_inv))) : exprℚ()), q.num).num, q.num)],
  by field_simp [] ["[", expr this, ",", expr ne_of_gt q_num_pos, "]"] [] [],
  suffices [] [":", expr «expr < »(«expr - »((q.denom : exprℤ()), «expr * »(q.num, «expr⌊ ⌋»(q_inv))), q.num)],
  by { have [] [":", expr «expr = »(«expr / »((«expr - »(q.denom, «expr * »(q.num, «expr⌊ ⌋»(q_inv))) : exprℚ()), q.num).num, «expr - »(q.denom, «expr * »(q.num, «expr⌊ ⌋»(q_inv))))] [],
    by { suffices [] [":", expr «expr - »((q.denom : exprℤ()), «expr * »(q.num, «expr⌊ ⌋»(q_inv))).nat_abs.coprime q.num.nat_abs],
      by exact_mod_cast [expr rat.num_div_eq_of_coprime q_num_pos this],
      have [] [":", expr «expr = »((q.num.nat_abs : exprℚ()), (q.num : exprℚ()))] [],
      by exact_mod_cast [expr q_num_abs_eq_q_num],
      have [ident tmp] [] [":=", expr nat.coprime_sub_mul_floor_rat_div_of_coprime q.cop.symm],
      simpa [] [] ["only"] ["[", expr this, ",", expr q_num_abs_eq_q_num, "]"] [] ["using", expr tmp] },
    rwa [expr this] [] },
  have [ident q_inv_num_denom_ineq] [":", expr «expr < »(«expr - »(«expr ⁻¹»(q).num, «expr * »(«expr⌊ ⌋»(«expr ⁻¹»(q)), «expr ⁻¹»(q).denom)), «expr ⁻¹»(q).denom)] [],
  by { have [] [":", expr «expr < »(«expr ⁻¹»(q).num, «expr * »(«expr + »(«expr⌊ ⌋»(«expr ⁻¹»(q)), 1), «expr ⁻¹»(q).denom))] [],
    from [expr rat.num_lt_succ_floor_mul_denom «expr ⁻¹»(q)],
    have [] [":", expr «expr < »(«expr ⁻¹»(q).num, «expr + »(«expr * »(«expr⌊ ⌋»(«expr ⁻¹»(q)), «expr ⁻¹»(q).denom), «expr ⁻¹»(q).denom))] [],
    by rwa ["[", expr right_distrib, ",", expr one_mul, "]"] ["at", ident this],
    rwa ["[", "<-", expr sub_lt_iff_lt_add', "]"] ["at", ident this] },
  have [] [":", expr «expr ∧ »(«expr = »(q_inv.num, q.denom), «expr = »(q_inv.denom, q.num.nat_abs))] [],
  by { have [ident coprime_q_denom_q_num] [":", expr q.denom.coprime q.num.nat_abs] [],
    from [expr q.cop.symm],
    have [] [":", expr «expr = »(int.nat_abs q.denom, q.denom)] [],
    by simp [] [] [] [] [] [],
    rw ["<-", expr this] ["at", ident coprime_q_denom_q_num],
    rw [expr q_inv_def] [],
    split,
    { exact_mod_cast [expr rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num] },
    { suffices [] [":", expr «expr = »((«expr / »((q.denom : exprℚ()), q.num).denom : exprℤ()), q.num.nat_abs)],
      by exact_mod_cast [expr this],
      rw [expr q_num_abs_eq_q_num] [],
      exact_mod_cast [expr rat.denom_div_eq_of_coprime q_num_pos coprime_q_denom_q_num] } },
  rwa ["[", expr q_inv_eq, ",", expr this.left, ",", expr this.right, ",", expr q_num_abs_eq_q_num, ",", expr mul_comm, "]"] ["at", ident q_inv_num_denom_ineq]
end

end Rat

