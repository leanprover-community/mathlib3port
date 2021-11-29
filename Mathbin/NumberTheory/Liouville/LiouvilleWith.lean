import Mathbin.Analysis.SpecialFunctions.Pow 
import Mathbin.NumberTheory.Liouville.Basic 
import Mathbin.Topology.Instances.Irrational

/-!
# Liouville numbers with a given exponent

We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`. A number is a Liouville number in the sense of
`liouville` if it is `liouville_with` any real exponent, see `forall_liouville_with_iff`.

* If `p ≤ 1`, then this condition is trivial.

* If `1 < p ≤ 2`, then this condition is equivalent to `irrational x`. The forward implication
  does not require `p ≤ 2` and is formalized as `liouville_with.irrational`; the other implication
  follows from approximations by continued fractions and is not formalized yet.

* If `p > 2`, then this is a non-trivial condition on irrational numbers. In particular,
  [Thue–Siegel–Roth theorem](https://en.wikipedia.org/wiki/Roth's_theorem) states that such numbers
  must be transcendental.

In this file we define the predicate `liouville_with` and prove some basic facts about this
predicate.

## Tags

Liouville number, irrational, irrationality exponent
-/


open Filter Metric Real Set

open_locale Filter TopologicalSpace

/-- We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`.

A number is a Liouville number in the sense of `liouville` if it is `liouville_with` any real
exponent. -/
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠn : ℕ in at_top, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / (n^p)

-- error in NumberTheory.Liouville.LiouvilleWith: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For `p = 1` (hence, for any `p ≤ 1`), the condition `liouville_with p x` is trivial. -/
theorem liouville_with_one (x : exprℝ()) : liouville_with 1 x :=
begin
  use [expr 2],
  refine [expr «expr $ »((eventually_gt_at_top 0).mono, λ n hn, _).frequently],
  have [ident hn'] [":", expr «expr < »((0 : exprℝ()), n)] [],
  by simpa [] [] [] [] [] [],
  have [] [":", expr «expr < »(x, «expr / »(«expr↑ »(«expr + »(«expr⌊ ⌋»(«expr * »(x, «expr↑ »(n))), 1)), «expr↑ »(n)))] [],
  { rw ["[", expr lt_div_iff hn', ",", expr int.cast_add, ",", expr int.cast_one, "]"] [],
    exact [expr int.lt_floor_add_one _] },
  refine [expr ⟨«expr + »(«expr⌊ ⌋»(«expr * »(x, n)), 1), this.ne, _⟩],
  rw ["[", expr abs_sub_comm, ",", expr abs_of_pos (sub_pos.2 this), ",", expr rpow_one, ",", expr sub_lt_iff_lt_add', ",", expr add_div_eq_mul_add_div _ _ hn'.ne', ",", expr div_lt_div_right hn', "]"] [],
  simpa [] [] [] ["[", expr bit0, ",", "<-", expr add_assoc, "]"] [] ["using", expr (int.floor_le «expr * »(x, n)).trans_lt (lt_add_one _)]
end

namespace LiouvilleWith

variable {p q x y : ℝ} {r : ℚ} {m : ℤ} {n : ℕ}

/-- The constant `C` provided by the definition of `liouville_with` can be made positive.
We also add `1 ≤ n` to the list of assumptions about the denominator. While it is equivalent to
the original statement, the case `n = 0` breaks many arguments. -/
theorem exists_pos (h : LiouvilleWith p x) :
  ∃ (C : ℝ)(h₀ : 0 < C), ∃ᶠn : ℕ in at_top, 1 ≤ n ∧ ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / (n^p) :=
  by 
    rcases h with ⟨C, hC⟩
    refine' ⟨max C 1, zero_lt_one.trans_le$ le_max_rightₓ _ _, _⟩
    refine' ((eventually_ge_at_top 1).and_frequently hC).mono _ 
    rintro n ⟨hle, m, hne, hlt⟩
    refine' ⟨hle, m, hne, hlt.trans_le _⟩
    exact div_le_div_of_le (rpow_nonneg_of_nonneg n.cast_nonneg _) (le_max_leftₓ _ _)

/-- If a number is Liouville with exponent `p`, then it is Liouville with any smaller exponent. -/
theorem mono (h : LiouvilleWith p x) (hle : q ≤ p) : LiouvilleWith q x :=
  by 
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine' ⟨C, hC.mono _⟩
    rintro n ⟨hn, m, hne, hlt⟩
    refine' ⟨m, hne, hlt.trans_le$ div_le_div_of_le_left hC₀.le _ _⟩
    exacts[rpow_pos_of_pos (Nat.cast_pos.2 hn) _, rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hle]

-- error in NumberTheory.Liouville.LiouvilleWith: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x` satisfies Liouville condition with exponent `p` and `q < p`, then `x`
satisfies Liouville condition with exponent `q` and constant `1`. -/
theorem frequently_lt_rpow_neg
(h : liouville_with p x)
(hlt : «expr < »(q, p)) : «expr∃ᶠ in , »((n : exprℕ()), at_top, «expr∃ , »((m : exprℤ()), «expr ∧ »(«expr ≠ »(x, «expr / »(m, n)), «expr < »(«expr| |»(«expr - »(x, «expr / »(m, n))), «expr ^ »(n, «expr- »(q)))))) :=
begin
  rcases [expr h.exists_pos, "with", "⟨", ident C, ",", ident hC₀, ",", ident hC, "⟩"],
  have [] [":", expr «expr∀ᶠ in , »((n : exprℕ()), at_top, «expr < »(C, «expr ^ »(n, «expr - »(p, q))))] [],
  by simpa [] [] ["only"] ["[", expr («expr ∘ »), ",", expr neg_sub, ",", expr one_div, "]"] [] ["using", expr ((tendsto_rpow_at_top (sub_pos.2 hlt)).comp tendsto_coe_nat_at_top_at_top).eventually (eventually_gt_at_top C)],
  refine [expr (this.and_frequently hC).mono _],
  rintro [ident n, "⟨", ident hnC, ",", ident hn, ",", ident m, ",", ident hne, ",", ident hlt, "⟩"],
  replace [ident hn] [":", expr «expr < »((0 : exprℝ()), n)] [":=", expr nat.cast_pos.2 hn],
  refine [expr ⟨m, hne, «expr $ »(hlt.trans, «expr $ »(div_lt_iff, rpow_pos_of_pos hn _).2 _)⟩],
  rwa ["[", expr mul_comm, ",", "<-", expr rpow_add hn, ",", "<-", expr sub_eq_add_neg, "]"] []
end

-- error in NumberTheory.Liouville.LiouvilleWith: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product of a Liouville number and a nonzero rational number is again a Liouville number.  -/
theorem mul_rat (h : liouville_with p x) (hr : «expr ≠ »(r, 0)) : liouville_with p «expr * »(x, r) :=
begin
  rcases [expr h.exists_pos, "with", "⟨", ident C, ",", ident hC₀, ",", ident hC, "⟩"],
  refine [expr ⟨«expr * »(«expr ^ »(r.denom, p), «expr * »(«expr| |»(r), C)), (tendsto_id.nsmul_at_top r.pos).frequently (hC.mono _)⟩],
  rintro [ident n, "⟨", ident hn, ",", ident m, ",", ident hne, ",", ident hlt, "⟩"],
  have [ident A] [":", expr «expr = »(«expr / »((«expr↑ »(«expr * »(r.num, m)) : exprℝ()), «expr↑ »(«expr • »(r.denom, id n))), «expr * »(«expr / »(m, n), r))] [],
  by simp [] [] [] ["[", "<-", expr div_mul_div, ",", "<-", expr r.cast_def, ",", expr mul_comm, "]"] [] [],
  refine [expr ⟨«expr * »(r.num, m), _, _⟩],
  { rw [expr A] [],
    simp [] [] [] ["[", expr hne, ",", expr hr, "]"] [] [] },
  { rw ["[", expr A, ",", "<-", expr sub_mul, ",", expr abs_mul, "]"] [],
    simp [] [] ["only"] ["[", expr smul_eq_mul, ",", expr id.def, ",", expr nat.cast_mul, "]"] [] [],
    refine [expr «expr $ »(mul_lt_mul_of_pos_right hlt, «expr $ »(abs_pos.2, rat.cast_ne_zero.2 hr)).trans_le _],
    rw ["[", expr mul_rpow, ",", expr mul_div_mul_left, ",", expr mul_comm, ",", expr mul_div_assoc, "]"] [],
    exacts ["[", expr (rpow_pos_of_pos (nat.cast_pos.2 r.pos) _).ne', ",", expr nat.cast_nonneg _, ",", expr nat.cast_nonneg _, "]"] }
end

/-- The product `x * r`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem mul_rat_iff (hr : r ≠ 0) : LiouvilleWith p (x*r) ↔ LiouvilleWith p x :=
  ⟨fun h =>
      by 
        simpa only [mul_assocₓ, ←Rat.cast_mul, mul_inv_cancel hr, Rat.cast_one, mul_oneₓ] using
          h.mul_rat (inv_ne_zero hr),
    fun h => h.mul_rat hr⟩

/-- The product `r * x`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem rat_mul_iff (hr : r ≠ 0) : LiouvilleWith p (r*x) ↔ LiouvilleWith p x :=
  by 
    rw [mul_commₓ, mul_rat_iff hr]

theorem rat_mul (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (r*x) :=
  (rat_mul_iff hr).2 h

theorem mul_int_iff (hm : m ≠ 0) : LiouvilleWith p (x*m) ↔ LiouvilleWith p x :=
  by 
    rw [←Rat.cast_coe_int, mul_rat_iff (Int.cast_ne_zero.2 hm)]

theorem mul_int (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (x*m) :=
  (mul_int_iff hm).2 h

theorem int_mul_iff (hm : m ≠ 0) : LiouvilleWith p (m*x) ↔ LiouvilleWith p x :=
  by 
    rw [mul_commₓ, mul_int_iff hm]

theorem int_mul (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (m*x) :=
  (int_mul_iff hm).2 h

theorem mul_nat_iff (hn : n ≠ 0) : LiouvilleWith p (x*n) ↔ LiouvilleWith p x :=
  by 
    rw [←Rat.cast_coe_nat, mul_rat_iff (Nat.cast_ne_zero.2 hn)]

theorem mul_nat (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (x*n) :=
  (mul_nat_iff hn).2 h

theorem nat_mul_iff (hn : n ≠ 0) : LiouvilleWith p (n*x) ↔ LiouvilleWith p x :=
  by 
    rw [mul_commₓ, mul_nat_iff hn]

theorem nat_mul (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (n*x) :=
  by 
    rw [mul_commₓ]
    exact h.mul_nat hn

-- error in NumberTheory.Liouville.LiouvilleWith: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_rat (h : liouville_with p x) (r : exprℚ()) : liouville_with p «expr + »(x, r) :=
begin
  rcases [expr h.exists_pos, "with", "⟨", ident C, ",", ident hC₀, ",", ident hC, "⟩"],
  refine [expr ⟨«expr * »(«expr ^ »(r.denom, p), C), (tendsto_id.nsmul_at_top r.pos).frequently (hC.mono _)⟩],
  rintro [ident n, "⟨", ident hn, ",", ident m, ",", ident hne, ",", ident hlt, "⟩"],
  have [ident hr] [":", expr «expr < »((0 : exprℝ()), r.denom)] [],
  from [expr nat.cast_pos.2 r.pos],
  have [ident hn'] [":", expr «expr ≠ »((n : exprℝ()), 0)] [],
  from [expr nat.cast_ne_zero.2 (zero_lt_one.trans_le hn).ne'],
  have [] [":", expr «expr = »((«expr / »(«expr↑ »((«expr + »(«expr * »(r.denom, m), «expr * »(r.num, n)) : exprℤ())), «expr↑ »(«expr • »(r.denom, id n))) : exprℝ()), «expr + »(«expr / »(m, n), r))] [],
  by simp [] [] [] ["[", expr add_div, ",", expr hr.ne', ",", expr mul_div_mul_left, ",", expr mul_div_mul_right, ",", expr hn', ",", "<-", expr rat.cast_def, "]"] [] [],
  refine [expr ⟨«expr + »(«expr * »(r.denom, m), «expr * »(r.num, n)), _⟩],
  rw ["[", expr this, ",", expr add_sub_add_right_eq_sub, "]"] [],
  refine [expr ⟨by simpa [] [] [] [] [] [], hlt.trans_le (le_of_eq _)⟩],
  have [] [":", expr «expr ≠ »((«expr ^ »(r.denom, p) : exprℝ()), 0)] [],
  from [expr (rpow_pos_of_pos hr _).ne'],
  simp [] [] [] ["[", expr mul_rpow, ",", expr nat.cast_nonneg, ",", expr mul_div_mul_left, ",", expr this, "]"] [] []
end

@[simp]
theorem add_rat_iff : LiouvilleWith p (x+r) ↔ LiouvilleWith p x :=
  ⟨fun h =>
      by 
        simpa using h.add_rat (-r),
    fun h => h.add_rat r⟩

@[simp]
theorem rat_add_iff : LiouvilleWith p (r+x) ↔ LiouvilleWith p x :=
  by 
    rw [add_commₓ, add_rat_iff]

theorem rat_add (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r+x) :=
  add_commₓ x r ▸ h.add_rat r

@[simp]
theorem add_int_iff : LiouvilleWith p (x+m) ↔ LiouvilleWith p x :=
  by 
    rw [←Rat.cast_coe_int m, add_rat_iff]

@[simp]
theorem int_add_iff : LiouvilleWith p (m+x) ↔ LiouvilleWith p x :=
  by 
    rw [add_commₓ, add_int_iff]

@[simp]
theorem add_nat_iff : LiouvilleWith p (x+n) ↔ LiouvilleWith p x :=
  by 
    rw [←Rat.cast_coe_nat n, add_rat_iff]

@[simp]
theorem nat_add_iff : LiouvilleWith p (n+x) ↔ LiouvilleWith p x :=
  by 
    rw [add_commₓ, add_nat_iff]

theorem add_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x+m) :=
  add_int_iff.2 h

theorem int_add (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m+x) :=
  int_add_iff.2 h

theorem add_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x+n) :=
  h.add_int n

theorem nat_add (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n+x) :=
  h.int_add n

protected theorem neg (h : LiouvilleWith p x) : LiouvilleWith p (-x) :=
  by 
    rcases h with ⟨C, hC⟩
    refine' ⟨C, hC.mono _⟩
    rintro n ⟨m, hne, hlt⟩
    use -m 
    simp [neg_div, abs_sub_comm _ x]

@[simp]
theorem neg_iff : LiouvilleWith p (-x) ↔ LiouvilleWith p x :=
  ⟨fun h => neg_negₓ x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]
theorem sub_rat_iff : LiouvilleWith p (x - r) ↔ LiouvilleWith p x :=
  by 
    rw [sub_eq_add_neg, ←Rat.cast_neg, add_rat_iff]

theorem sub_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x - r) :=
  sub_rat_iff.2 h

@[simp]
theorem sub_int_iff : LiouvilleWith p (x - m) ↔ LiouvilleWith p x :=
  by 
    rw [←Rat.cast_coe_int, sub_rat_iff]

theorem sub_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x - m) :=
  sub_int_iff.2 h

@[simp]
theorem sub_nat_iff : LiouvilleWith p (x - n) ↔ LiouvilleWith p x :=
  by 
    rw [←Rat.cast_coe_nat, sub_rat_iff]

theorem sub_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x - n) :=
  sub_nat_iff.2 h

@[simp]
theorem rat_sub_iff : LiouvilleWith p (r - x) ↔ LiouvilleWith p x :=
  by 
    simp [sub_eq_add_neg]

theorem rat_sub (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r - x) :=
  rat_sub_iff.2 h

@[simp]
theorem int_sub_iff : LiouvilleWith p (m - x) ↔ LiouvilleWith p x :=
  by 
    simp [sub_eq_add_neg]

theorem int_sub (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m - x) :=
  int_sub_iff.2 h

@[simp]
theorem nat_sub_iff : LiouvilleWith p (n - x) ↔ LiouvilleWith p x :=
  by 
    simp [sub_eq_add_neg]

theorem nat_sub (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n - x) :=
  nat_sub_iff.2 h

-- error in NumberTheory.Liouville.LiouvilleWith: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ne_cast_int (h : liouville_with p x) (hp : «expr < »(1, p)) (m : exprℤ()) : «expr ≠ »(x, m) :=
begin
  rintro [ident rfl],
  rename [ident m, ident M],
  rcases [expr ((eventually_gt_at_top 0).and_frequently (h.frequently_lt_rpow_neg hp)).exists, "with", "⟨", ident n, ":", expr exprℕ(), ",", ident hn, ":", expr «expr < »(0, n), ",", ident m, ":", expr exprℤ(), ",", ident hne, ":", expr «expr ≠ »((M : exprℝ()), «expr / »(m, n)), ",", ident hlt, ":", expr «expr < »(«expr| |»((«expr - »(M, «expr / »(m, n)) : exprℝ())), «expr ^ »(n, («expr- »(1) : exprℝ()))), "⟩"],
  refine [expr hlt.not_le _],
  have [ident hn'] [":", expr «expr < »((0 : exprℝ()), n)] [],
  by simpa [] [] [] [] [] [],
  rw ["[", expr rpow_neg_one, ",", "<-", expr one_div, ",", expr sub_div' _ _ _ hn'.ne', ",", expr abs_div, ",", expr nat.abs_cast, ",", expr div_le_div_right hn', "]"] [],
  norm_cast [],
  rw ["[", "<-", expr zero_add (1 : exprℤ()), ",", expr int.add_one_le_iff, ",", expr abs_pos, ",", expr sub_ne_zero, "]"] [],
  rw ["[", expr ne.def, ",", expr eq_div_iff hn'.ne', "]"] ["at", ident hne],
  exact_mod_cast [expr hne]
end

/-- A number satisfying the Liouville condition with exponent `p > 1` is an irrational number. -/
protected theorem Irrational (h : LiouvilleWith p x) (hp : 1 < p) : Irrational x :=
  by 
    rintro ⟨r, rfl⟩
    rcases eq_or_ne r 0 with (rfl | h0)
    ·
      refine' h.ne_cast_int hp 0 _ 
      rw [Rat.cast_zero, Int.cast_zero]
    ·
      refine' (h.mul_rat (inv_ne_zero h0)).ne_cast_int hp 1 _ 
      simp [Rat.cast_ne_zero.2 h0]

end LiouvilleWith

namespace Liouville

variable {x : ℝ}

-- error in NumberTheory.Liouville.LiouvilleWith: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x` is a Liouville number, then for any `n`, for infinitely many denominators `b` there
exists a numerator `a` such that `x ≠ a / b` and `|x - a / b| < 1 / b ^ n`. -/
theorem frequently_exists_num
(hx : liouville x)
(n : exprℕ()) : «expr∃ᶠ in , »((b : exprℕ()), at_top, «expr∃ , »((a : exprℤ()), «expr ∧ »(«expr ≠ »(x, «expr / »(a, b)), «expr < »(«expr| |»(«expr - »(x, «expr / »(a, b))), «expr / »(1, «expr ^ »(b, n)))))) :=
begin
  refine [expr not_not.1 (λ H, _)],
  simp [] [] ["only"] ["[", expr liouville, ",", expr not_forall, ",", expr not_exists, ",", expr not_frequently, ",", expr not_and, ",", expr not_lt, ",", expr eventually_at_top, "]"] [] ["at", ident H],
  rcases [expr H, "with", "⟨", ident N, ",", ident hN, "⟩"],
  have [] [":", expr ∀
   b «expr > » (1 : exprℕ()), «expr∀ᶠ in , »((m : exprℕ()), at_top, ∀
    a : exprℤ(), «expr ≤ »((«expr / »(1, «expr ^ »(b, m)) : exprℝ()), «expr| |»(«expr - »(x, «expr / »(a, b)))))] [],
  { intros [ident b, ident hb],
    have [ident hb0'] [":", expr «expr ≠ »((b : exprℚ()), 0)] [":=", expr (zero_lt_one.trans (nat.one_lt_cast.2 hb)).ne'],
    replace [ident hb] [":", expr «expr < »((1 : exprℝ()), b)] [":=", expr nat.one_lt_cast.2 hb],
    have [ident hb0] [":", expr «expr < »((0 : exprℝ()), b)] [":=", expr zero_lt_one.trans hb],
    have [ident H] [":", expr tendsto (λ m, «expr / »(1, «expr ^ »(b, m)) : exprℕ() → exprℝ()) at_top (expr𝓝() 0)] [],
    { simp [] [] ["only"] ["[", expr one_div, "]"] [] [],
      exact [expr tendsto_inv_at_top_zero.comp (tendsto_pow_at_top_at_top_of_one_lt hb)] },
    refine [expr (H.eventually (hx.irrational.eventually_forall_le_dist_cast_div b)).mono _],
    exact [expr λ m hm a, hm a] },
  have [] [":", expr «expr∀ᶠ in , »((m : exprℕ()), at_top, ∀
    b «expr < » N, «expr < »(1, b) → ∀
    a : exprℤ(), «expr ≤ »((«expr / »(1, «expr ^ »(b, m)) : exprℝ()), «expr| |»(«expr - »(x, «expr / »(a, b)))))] [],
  from [expr (finite_lt_nat N).eventually_all.2 (λ b hb, eventually_imp_distrib_left.2 (this b))],
  rcases [expr (this.and (eventually_ge_at_top n)).exists, "with", "⟨", ident m, ",", ident hm, ",", ident hnm, "⟩"],
  rcases [expr hx m, "with", "⟨", ident a, ",", ident b, ",", ident hb, ",", ident hne, ",", ident hlt, "⟩"],
  lift [expr b] ["to", expr exprℕ()] ["using", expr zero_le_one.trans hb.le] [],
  norm_cast ["at", ident hb],
  push_cast [] ["at", ident hne, ident hlt],
  cases [expr le_or_lt N b] [],
  { refine [expr (hN b h a hne).not_lt (hlt.trans_le _)],
    replace [ident hb] [":", expr «expr < »((1 : exprℝ()), b)] [":=", expr nat.one_lt_cast.2 hb],
    have [ident hb0] [":", expr «expr < »((0 : exprℝ()), b)] [":=", expr zero_lt_one.trans hb],
    exact [expr one_div_le_one_div_of_le (pow_pos hb0 _) (pow_le_pow hb.le hnm)] },
  { exact [expr (hm b h hb _).not_lt hlt] }
end

/-- A Liouville number is a Liouville number with any real exponent. -/
protected theorem LiouvilleWith (hx : Liouville x) (p : ℝ) : LiouvilleWith p x :=
  by 
    suffices  : LiouvilleWith ⌈p⌉₊ x 
    exact this.mono (Nat.le_ceil p)
    refine' ⟨1, ((eventually_gt_at_top 1).and_frequently (hx.frequently_exists_num ⌈p⌉₊)).mono _⟩
    rintro b ⟨hb, a, hne, hlt⟩
    refine' ⟨a, hne, _⟩
    rwa [rpow_nat_cast]

end Liouville

/-- A number satisfies the Liouville condition with any exponent if and only if it is a Liouville
number. -/
theorem forall_liouville_with_iff {x : ℝ} : (∀ p, LiouvilleWith p x) ↔ Liouville x :=
  by 
    refine' ⟨fun H n => _, Liouville.liouville_with⟩
    rcases((eventually_gt_at_top 1).and_frequently ((H (n+1)).frequently_lt_rpow_neg (lt_add_one n))).exists with
      ⟨b, hb, a, hne, hlt⟩
    exact
      ⟨a, b,
        by 
          exactModCast hb,
        hne,
        by 
          simpa [rpow_neg] using hlt⟩

