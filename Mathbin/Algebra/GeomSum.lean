import Mathbin.Algebra.GroupWithZero.Power 
import Mathbin.Algebra.BigOperators.Order 
import Mathbin.Algebra.BigOperators.Ring 
import Mathbin.Algebra.BigOperators.Intervals 
import Mathbin.Tactic.Abel

/-!
# Partial sums of geometric series

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.

## Main definitions

* `geom_sum` defines for each $x$ in a semiring and each natural number $n$ the partial sum
  $\sum_{i=0}^{n-1} x^i$ of the geometric series.
* `geom_sum₂` defines for each $x,y$ in a semiring and each natural number $n$ the partial sum
  $\sum_{i=0}^{n-1} x^i y^{n-1-i}$ of the geometric series.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-y^{n-m}x^m}{x-y}$ in a field.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/


universe u

variable {α : Type u}

open Finset MulOpposite

open_locale BigOperators

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i$. -/
def geomSum [Semiringₓ α] (x : α) (n : ℕ) :=
  ∑i in range n, x ^ i

theorem geom_sum_def [Semiringₓ α] (x : α) (n : ℕ) : geomSum x n = ∑i in range n, x ^ i :=
  rfl

@[simp]
theorem geom_sum_zero [Semiringₓ α] (x : α) : geomSum x 0 = 0 :=
  rfl

@[simp]
theorem geom_sum_one [Semiringₓ α] (x : α) : geomSum x 1 = 1 :=
  by 
    rw [geom_sum_def, sum_range_one, pow_zeroₓ]

@[simp]
theorem one_geom_sum [Semiringₓ α] (n : ℕ) : geomSum (1 : α) n = n :=
  by 
    simp [geom_sum_def]

@[simp]
theorem op_geom_sum [Semiringₓ α] (x : α) (n : ℕ) : op (geomSum x n) = geomSum (op x) n :=
  by 
    simp [geom_sum_def]

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i y^{n-1-i}$. -/
def geomSum₂ [Semiringₓ α] (x y : α) (n : ℕ) :=
  ∑i in range n, (x ^ i)*y ^ (n - 1 - i)

theorem geom_sum₂_def [Semiringₓ α] (x y : α) (n : ℕ) : geomSum₂ x y n = ∑i in range n, (x ^ i)*y ^ (n - 1 - i) :=
  rfl

@[simp]
theorem geom_sum₂_zero [Semiringₓ α] (x y : α) : geomSum₂ x y 0 = 0 :=
  rfl

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem geom_sum₂_one [semiring α] (x y : α) : «expr = »(geom_sum₂ x y 1, 1) :=
by { have [] [":", expr «expr = »(«expr - »(«expr - »(1, 1), 0), 0)] [":=", expr rfl],
  rw ["[", expr geom_sum₂_def, ",", expr sum_range_one, ",", expr this, ",", expr pow_zero, ",", expr pow_zero, ",", expr mul_one, "]"] [] }

@[simp]
theorem op_geom_sum₂ [Semiringₓ α] (x y : α) (n : ℕ) : op (geomSum₂ x y n) = geomSum₂ (op y) (op x) n :=
  by 
    simp only [geom_sum₂_def, op_sum, op_mul, op_pow]
    rw [←sum_range_reflect]
    refine' sum_congr rfl fun j j_in => _ 
    rw [mem_range, Nat.lt_iff_add_one_le] at j_in 
    congr 
    apply tsub_tsub_cancel_of_le 
    exact le_tsub_of_add_le_right j_in

@[simp]
theorem geom_sum₂_with_one [Semiringₓ α] (x : α) (n : ℕ) : geomSum₂ x 1 n = geomSum x n :=
  sum_congr rfl
    fun i _ =>
      by 
        rw [one_pow, mul_oneₓ]

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected
theorem commute.geom_sum₂_mul_add
[semiring α]
{x y : α}
(h : commute x y)
(n : exprℕ()) : «expr = »(«expr + »(«expr * »(geom_sum₂ «expr + »(x, y) y n, x), «expr ^ »(y, n)), «expr ^ »(«expr + »(x, y), n)) :=
begin
  let [ident f] [] [":=", expr λ
   m i : exprℕ(), «expr * »(«expr ^ »(«expr + »(x, y), i), «expr ^ »(y, «expr - »(«expr - »(m, 1), i)))],
  change [expr «expr = »(«expr + »(«expr * »(«expr∑ in , »((i), range n, f n i), x), «expr ^ »(y, n)), «expr ^ »(«expr + »(x, y), n))] [] [],
  induction [expr n] [] ["with", ident n, ident ih] [],
  { rw ["[", expr range_zero, ",", expr sum_empty, ",", expr zero_mul, ",", expr zero_add, ",", expr pow_zero, ",", expr pow_zero, "]"] [] },
  { have [ident f_last] [":", expr «expr = »(f «expr + »(n, 1) n, «expr ^ »(«expr + »(x, y), n))] [":=", expr by { dsimp [] ["[", expr f, "]"] [] [],
       rw ["[", "<-", expr tsub_add_eq_tsub_tsub, ",", expr nat.add_comm, ",", expr tsub_self, ",", expr pow_zero, ",", expr mul_one, "]"] [] }],
    have [ident f_succ] [":", expr ∀
     i, «expr ∈ »(i, range n) → «expr = »(f «expr + »(n, 1) i, «expr * »(y, f n i))] [":=", expr λ
     i hi, by { dsimp [] ["[", expr f, "]"] [] [],
       have [] [":", expr commute y «expr ^ »(«expr + »(x, y), i)] [":=", expr (h.symm.add_right (commute.refl y)).pow_right i],
       rw ["[", "<-", expr mul_assoc, ",", expr this.eq, ",", expr mul_assoc, ",", "<-", expr pow_succ y «expr - »(«expr - »(n, 1), i), "]"] [],
       congr' [2] [],
       rw ["[", expr add_tsub_cancel_right, ",", "<-", expr tsub_add_eq_tsub_tsub, ",", expr add_comm 1 i, "]"] [],
       have [] [":", expr «expr = »(«expr + »(«expr + »(i, 1), «expr - »(n, «expr + »(i, 1))), n)] [":=", expr add_tsub_cancel_of_le (mem_range.mp hi)],
       rw ["[", expr add_comm «expr + »(i, 1), "]"] ["at", ident this],
       rw ["[", "<-", expr this, ",", expr add_tsub_cancel_right, ",", expr add_comm i 1, ",", "<-", expr add_assoc, ",", expr add_tsub_cancel_right, "]"] [] }],
    rw ["[", expr pow_succ «expr + »(x, y), ",", expr add_mul, ",", expr sum_range_succ_comm, ",", expr add_mul, ",", expr f_last, ",", expr add_assoc, "]"] [],
    rw [expr (((commute.refl x).add_right h).pow_right n).eq] [],
    congr' [1] [],
    rw ["[", expr sum_congr rfl f_succ, ",", "<-", expr mul_sum, ",", expr pow_succ y, ",", expr mul_assoc, ",", "<-", expr mul_add y, ",", expr ih, "]"] [] }
end

theorem geom_sum₂_self {α : Type _} [CommRingₓ α] (x : α) (n : ℕ) : geomSum₂ x x n = n*x ^ (n - 1) :=
  calc (∑i in Finset.range n, (x ^ i)*x ^ (n - 1 - i)) = ∑i in Finset.range n, x ^ i+n - 1 - i :=
    by 
      simpRw [←pow_addₓ]
    _ = ∑i in Finset.range n, x ^ (n - 1) :=
    Finset.sum_congr rfl fun i hi => congr_argₓ _$ add_tsub_cancel_of_le$ Nat.le_pred_of_lt$ Finset.mem_range.1 hi 
    _ = (Finset.range n).card • x ^ (n - 1) := Finset.sum_const _ 
    _ = n*x ^ (n - 1) :=
    by 
      rw [Finset.card_range, nsmul_eq_mul]
    

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [CommSemiringₓ α] (x y : α) (n : ℕ) : ((geomSum₂ (x+y) y n*x)+y ^ n) = (x+y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem geom_sum_mul_add
[semiring α]
(x : α)
(n : exprℕ()) : «expr = »(«expr + »(«expr * »(geom_sum «expr + »(x, 1) n, x), 1), «expr ^ »(«expr + »(x, 1), n)) :=
begin
  have [] [] [":=", expr (commute.one_right x).geom_sum₂_mul_add n],
  rw ["[", expr one_pow, ",", expr geom_sum₂_with_one, "]"] ["at", ident this],
  exact [expr this]
end

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem commute.geom_sum₂_mul
[ring α]
{x y : α}
(h : commute x y)
(n : exprℕ()) : «expr = »(«expr * »(geom_sum₂ x y n, «expr - »(x, y)), «expr - »(«expr ^ »(x, n), «expr ^ »(y, n))) :=
begin
  have [] [] [":=", expr (h.sub_left (commute.refl y)).geom_sum₂_mul_add n],
  rw ["[", expr sub_add_cancel, "]"] ["at", ident this],
  rw ["[", "<-", expr this, ",", expr add_sub_cancel, "]"] []
end

theorem Commute.mul_neg_geom_sum₂ [Ringₓ α] {x y : α} (h : Commute x y) (n : ℕ) :
  ((y - x)*geomSum₂ x y n) = y ^ n - x ^ n :=
  by 
    apply op_injective 
    simp only [op_mul, op_sub, op_geom_sum₂, op_pow]
    exact (commute.op h.symm).geom_sum₂_mul n

theorem Commute.mul_geom_sum₂ [Ringₓ α] {x y : α} (h : Commute x y) (n : ℕ) :
  ((x - y)*geomSum₂ x y n) = x ^ n - y ^ n :=
  by 
    rw [←neg_sub (y ^ n), ←h.mul_neg_geom_sum₂, ←neg_mul_eq_neg_mul_symm, neg_sub]

theorem geom_sum₂_mul [CommRingₓ α] (x y : α) (n : ℕ) : (geomSum₂ x y n*x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem geom_sum_mul
[ring α]
(x : α)
(n : exprℕ()) : «expr = »(«expr * »(geom_sum x n, «expr - »(x, 1)), «expr - »(«expr ^ »(x, n), 1)) :=
begin
  have [] [] [":=", expr (commute.one_right x).geom_sum₂_mul n],
  rw ["[", expr one_pow, ",", expr geom_sum₂_with_one, "]"] ["at", ident this],
  exact [expr this]
end

theorem mul_geom_sum [Ringₓ α] (x : α) (n : ℕ) : ((x - 1)*geomSum x n) = x ^ n - 1 :=
  op_injective$
    by 
      simpa using geom_sum_mul (op x) n

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem geom_sum_mul_neg
[ring α]
(x : α)
(n : exprℕ()) : «expr = »(«expr * »(geom_sum x n, «expr - »(1, x)), «expr - »(1, «expr ^ »(x, n))) :=
begin
  have [] [] [":=", expr congr_arg has_neg.neg (geom_sum_mul x n)],
  rw ["[", expr neg_sub, ",", "<-", expr mul_neg_eq_neg_mul_symm, ",", expr neg_sub, "]"] ["at", ident this],
  exact [expr this]
end

theorem mul_neg_geom_sum [Ringₓ α] (x : α) (n : ℕ) : ((1 - x)*geomSum x n) = 1 - x ^ n :=
  op_injective$
    by 
      simpa using geom_sum_mul_neg (op x) n

protected theorem Commute.geom_sum₂ [DivisionRing α] {x y : α} (h' : Commute x y) (h : x ≠ y) (n : ℕ) :
  geomSum₂ x y n = (x ^ n - y ^ n) / (x - y) :=
  have  : x - y ≠ 0 :=
    by 
      simp_all [-sub_eq_add_neg, sub_eq_iff_eq_add]
  by 
    rw [←h'.geom_sum₂_mul, mul_div_cancel _ this]

theorem geom₂_sum [Field α] {x y : α} (h : x ≠ y) (n : ℕ) : geomSum₂ x y n = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geomSum₂ h n

theorem geom_sum_eq [DivisionRing α] {x : α} (h : x ≠ 1) (n : ℕ) : geomSum x n = (x ^ n - 1) / (x - 1) :=
  have  : x - 1 ≠ 0 :=
    by 
      simp_all [-sub_eq_add_neg, sub_eq_iff_eq_add]
  by 
    rw [←geom_sum_mul, mul_div_cancel _ this]

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem commute.mul_geom_sum₂_Ico
[ring α]
{x y : α}
(h : commute x y)
{m n : exprℕ()}
(hmn : «expr ≤ »(m, n)) : «expr = »(«expr * »(«expr - »(x, y), «expr∑ in , »((i), finset.Ico m n, «expr * »(«expr ^ »(x, i), «expr ^ »(y, «expr - »(«expr - »(n, 1), i))))), «expr - »(«expr ^ »(x, n), «expr * »(«expr ^ »(x, m), «expr ^ »(y, «expr - »(n, m))))) :=
begin
  rw ["[", expr sum_Ico_eq_sub _ hmn, ",", "<-", expr geom_sum₂_def, "]"] [],
  have [] [":", expr «expr = »(«expr∑ in , »((k), range m, «expr * »(«expr ^ »(x, k), «expr ^ »(y, «expr - »(«expr - »(n, 1), k)))), «expr∑ in , »((k), range m, «expr * »(«expr ^ »(x, k), «expr * »(«expr ^ »(y, «expr - »(n, m)), «expr ^ »(y, «expr - »(«expr - »(m, 1), k))))))] [],
  { refine [expr sum_congr rfl (λ j j_in, _)],
    rw ["<-", expr pow_add] [],
    congr,
    rw ["[", expr mem_range, ",", expr nat.lt_iff_add_one_le, ",", expr add_comm, "]"] ["at", ident j_in],
    have [ident h'] [":", expr «expr = »(«expr + »(«expr - »(n, m), «expr - »(m, «expr + »(1, j))), «expr - »(n, «expr + »(1, j)))] [":=", expr tsub_add_tsub_cancel hmn j_in],
    rw ["[", "<-", expr tsub_add_eq_tsub_tsub m, ",", expr h', ",", "<-", expr tsub_add_eq_tsub_tsub, "]"] [] },
  rw [expr this] [],
  simp_rw [expr pow_mul_comm y «expr - »(n, m) _] [],
  simp_rw ["<-", expr mul_assoc] [],
  rw ["[", "<-", expr sum_mul, ",", "<-", expr geom_sum₂_def, ",", expr mul_sub, ",", expr h.mul_geom_sum₂, ",", "<-", expr mul_assoc, ",", expr h.mul_geom_sum₂, ",", expr sub_mul, ",", "<-", expr pow_add, ",", expr add_tsub_cancel_of_le hmn, ",", expr sub_sub_sub_cancel_right «expr ^ »(x, n) «expr * »(«expr ^ »(x, m), «expr ^ »(y, «expr - »(n, m))) «expr ^ »(y, n), "]"] []
end

protected theorem Commute.geom_sum₂_succ_eq {α : Type u} [Ringₓ α] {x y : α} (h : Commute x y) {n : ℕ} :
  geomSum₂ x y (n+1) = (x ^ n)+y*geomSum₂ x y n :=
  by 
    simpRw [geomSum₂, mul_sum, sum_range_succ_comm, Nat.add_succ_sub_one, add_zeroₓ, tsub_self, pow_zeroₓ, mul_oneₓ,
      add_right_injₓ, ←mul_assocₓ, (h.symm.pow_right _).Eq, mul_assocₓ, ←pow_succₓ]
    refine' sum_congr rfl fun i hi => _ 
    suffices  : ((n - 1 - i)+1) = n - i
    ·
      rw [this]
    cases n
    ·
      exact absurd (list.mem_range.mp hi) i.not_lt_zero
    ·
      rw [tsub_add_eq_add_tsub (Nat.le_pred_of_lt (list.mem_range.mp hi)),
        tsub_add_cancel_of_le (nat.succ_le_iff.mpr n.succ_pos)]

theorem geom_sum₂_succ_eq {α : Type u} [CommRingₓ α] (x y : α) {n : ℕ} :
  geomSum₂ x y (n+1) = (x ^ n)+y*geomSum₂ x y n :=
  (Commute.all x y).geom_sum₂_succ_eq

theorem mul_geom_sum₂_Ico [CommRingₓ α] (x y : α) {m n : ℕ} (hmn : m ≤ n) :
  ((x - y)*∑i in Finset.ico m n, (x ^ i)*y ^ (n - 1 - i)) = x ^ n - (x ^ m)*y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn

-- error in Algebra.GeomSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem commute.geom_sum₂_Ico_mul
[ring α]
{x y : α}
(h : commute x y)
{m n : exprℕ()}
(hmn : «expr ≤ »(m, n)) : «expr = »(«expr * »(«expr∑ in , »((i), finset.Ico m n, «expr * »(«expr ^ »(x, i), «expr ^ »(y, «expr - »(«expr - »(n, 1), i)))), «expr - »(x, y)), «expr - »(«expr ^ »(x, n), «expr * »(«expr ^ »(y, «expr - »(n, m)), «expr ^ »(x, m)))) :=
begin
  apply [expr op_injective],
  simp [] [] ["only"] ["[", expr op_sub, ",", expr op_mul, ",", expr op_pow, ",", expr op_sum, "]"] [] [],
  have [] [":", expr «expr = »(«expr∑ in , »((k), Ico m n, «expr * »(«expr ^ »(op y, «expr - »(«expr - »(n, 1), k)), «expr ^ »(op x, k))), «expr∑ in , »((k), Ico m n, «expr * »(«expr ^ »(op x, k), «expr ^ »(op y, «expr - »(«expr - »(n, 1), k)))))] [],
  { refine [expr sum_congr rfl (λ k k_in, _)],
    apply [expr commute.pow_pow (commute.op h.symm)] },
  rw [expr this] [],
  exact [expr (commute.op h).mul_geom_sum₂_Ico hmn]
end

theorem geom_sum_Ico_mul [Ringₓ α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  ((∑i in Finset.ico m n, x ^ i)*x - 1) = x ^ n - x ^ m :=
  by 
    rw [sum_Ico_eq_sub _ hmn, ←geom_sum_def, ←geom_sum_def, sub_mul, geom_sum_mul, geom_sum_mul,
      sub_sub_sub_cancel_right]

theorem geom_sum_Ico_mul_neg [Ringₓ α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  ((∑i in Finset.ico m n, x ^ i)*1 - x) = x ^ m - x ^ n :=
  by 
    rw [sum_Ico_eq_sub _ hmn, ←geom_sum_def, ←geom_sum_def, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg,
      sub_sub_sub_cancel_left]

protected theorem Commute.geom_sum₂_Ico [DivisionRing α] {x y : α} (h : Commute x y) (hxy : x ≠ y) {m n : ℕ}
  (hmn : m ≤ n) : (∑i in Finset.ico m n, (x ^ i)*y ^ (n - 1 - i)) = (x ^ n - (y ^ (n - m))*x ^ m) / (x - y) :=
  have  : x - y ≠ 0 :=
    by 
      simp_all [-sub_eq_add_neg, sub_eq_iff_eq_add]
  by 
    rw [←h.geom_sum₂_Ico_mul hmn, mul_div_cancel _ this]

theorem geom_sum₂_Ico [Field α] {x y : α} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
  (∑i in Finset.ico m n, (x ^ i)*y ^ (n - 1 - i)) = (x ^ n - (y ^ (n - m))*x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

theorem geom_sum_Ico [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
  (∑i in Finset.ico m n, x ^ i) = (x ^ n - x ^ m) / (x - 1) :=
  by 
    simp only [sum_Ico_eq_sub _ hmn, (geom_sum_def _ _).symm, geom_sum_eq hx, div_sub_div_same,
      sub_sub_sub_cancel_right]

theorem geom_sum_Ico' [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
  (∑i in Finset.ico m n, x ^ i) = (x ^ m - x ^ n) / (1 - x) :=
  by 
    simp only [geom_sum_Ico hx hmn]
    convert neg_div_neg_eq (x ^ m - x ^ n) (1 - x) <;> abel

theorem geom_sum_inv [DivisionRing α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
  geomSum (x⁻¹) n = (x - 1)⁻¹*x - (x⁻¹ ^ n)*x :=
  have h₁ : x⁻¹ ≠ 1 :=
    by 
      rwa [inv_eq_one_div, Ne.def, div_eq_iff_mul_eq hx0, one_mulₓ]
  have h₂ : x⁻¹ - 1 ≠ 0 := mt sub_eq_zero.1 h₁ 
  have h₃ : x - 1 ≠ 0 := mt sub_eq_zero.1 hx1 
  have h₄ : (x*(x ^ n)⁻¹) = (x ^ n)⁻¹*x :=
    Nat.recOn n
      (by 
        simp )
      fun n h =>
        by 
          rw [pow_succₓ, mul_inv_rev₀, ←mul_assocₓ, h, mul_assocₓ, mul_inv_cancel hx0, mul_assocₓ, inv_mul_cancel hx0]
  by 
    rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ←mul_right_inj' h₃, ←mul_assocₓ, ←mul_assocₓ, mul_inv_cancel h₃]
    simp [mul_addₓ, add_mulₓ, mul_inv_cancel hx0, mul_assocₓ, h₄, sub_eq_add_neg, add_commₓ, add_left_commₓ]

variable {β : Type _}

theorem RingHom.map_geom_sum [Semiringₓ α] [Semiringₓ β] (x : α) (n : ℕ) (f : α →+* β) :
  f (geomSum x n) = geomSum (f x) n :=
  by 
    simp [geom_sum_def, f.map_sum]

theorem RingHom.map_geom_sum₂ [Semiringₓ α] [Semiringₓ β] (x y : α) (n : ℕ) (f : α →+* β) :
  f (geomSum₂ x y n) = geomSum₂ (f x) (f y) n :=
  by 
    simp [geom_sum₂_def, f.map_sum]

/-! ### Geometric sum with `ℕ`-division -/


theorem Nat.pred_mul_geom_sum_le (a b n : ℕ) : ((b - 1)*∑i in range n.succ, a / b ^ i) ≤ (a*b) - a / b ^ n :=
  calc
    ((b - 1)*∑i in range n.succ, a / b ^ i) =
      ((∑i in range n, (a / b ^ i+1)*b)+a*b) - (∑i in range n, a / b ^ i)+a / b ^ n :=
    by 
      rw [tsub_mul, mul_commₓ, sum_mul, one_mulₓ, sum_range_succ', sum_range_succ, pow_zeroₓ, Nat.div_oneₓ]
    _ ≤ ((∑i in range n, a / b ^ i)+a*b) - (∑i in range n, a / b ^ i)+a / b ^ n :=
    by 
      refine' tsub_le_tsub_right (add_le_add_right (sum_le_sum$ fun i _ => _) _) _ 
      rw [pow_succ'ₓ, ←Nat.div_div_eq_div_mulₓ]
      exact Nat.div_mul_le_selfₓ _ _ 
    _ = (a*b) - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _
    

theorem Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) : (∑i in range n, a / b ^ i) ≤ (a*b) / (b - 1) :=
  by 
    refine' (Nat.le_div_iff_mul_leₓ _ _$ tsub_pos_of_lt hb).2 _ 
    cases n
    ·
      rw [sum_range_zero, zero_mul]
      exact Nat.zero_leₓ _ 
    rw [mul_commₓ]
    exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

theorem Nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) : (∑i in Ico 1 n, a / b ^ i) ≤ a / (b - 1) :=
  by 
    cases n
    ·
      rw [Ico_eq_empty_of_le zero_le_one, sum_empty]
      exact Nat.zero_leₓ _ 
    rw [←add_le_add_iff_left a]
    calc (a+∑i : ℕ in Ico 1 n.succ, a / b ^ i) = (a / b ^ 0)+∑i : ℕ in Ico 1 n.succ, a / b ^ i :=
      by 
        rw [pow_zeroₓ, Nat.div_oneₓ]_ = ∑i in range n.succ, a / b ^ i :=
      by 
        rw [range_eq_Ico, ←Nat.Ico_insert_succ_left (Nat.succ_posₓ _), sum_insert]
        exact fun h => zero_lt_one.not_le (mem_Ico.1 h).1_ ≤ (a*b) / (b - 1) :=
      Nat.geom_sum_le hb a _ _ = ((a*1)+a*b - 1) / (b - 1) :=
      by 
        rw [←mul_addₓ, add_tsub_cancel_of_le (one_le_two.trans hb)]_ = a+a / (b - 1) :=
      by 
        rw [mul_oneₓ, Nat.add_mul_div_rightₓ _ _ (tsub_pos_of_lt hb), add_commₓ]

