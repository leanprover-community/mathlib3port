import Mathbin.Data.Nat.Pow

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `nat.log b` and `nat.clog b` are respectively right and
left adjoints of `nat.pow b`. See `pow_le_iff_le_log` and `le_pow_iff_clog_le`.
-/


namespace Nat

/-! ### Floor logarithm -/


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def log (b : ℕ) : ℕ → ℕ
| n =>
  if h : b ≤ n ∧ 1 < b then
    have  : n / b < n := div_lt_self ((zero_lt_one.trans h.2).trans_le h.1) h.2
    log (n / b)+1
  else 0

theorem log_eq_zero {b n : ℕ} (hnb : n < b ∨ b ≤ 1) : log b n = 0 :=
  by 
    rw [or_iff_not_and_not, not_ltₓ, not_leₓ] at hnb 
    rw [log, ←ite_not, if_pos hnb]

theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b)+1 :=
  by 
    rw [log]
    exact if_pos ⟨hn, h⟩

theorem log_of_lt {b n : ℕ} (hnb : n < b) : log b n = 0 :=
  by 
    rw [log, if_neg fun h : b ≤ n ∧ 1 < b => h.1.not_lt hnb]

theorem log_of_left_le_one {b n : ℕ} (hb : b ≤ 1) : log b n = 0 :=
  by 
    rw [log, if_neg fun h : b ≤ n ∧ 1 < b => h.2.not_le hb]

-- error in Data.Nat.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem log_eq_zero_iff
{b n : exprℕ()} : «expr ↔ »(«expr = »(log b n, 0), «expr ∨ »(«expr < »(n, b), «expr ≤ »(b, 1))) :=
begin
  split,
  { intro [ident h_log],
    by_contra [ident h],
    push_neg ["at", ident h],
    have [] [] [":=", expr log_of_one_lt_of_le h.2 h.1],
    rw [expr h_log] ["at", ident this],
    exact [expr succ_ne_zero _ this.symm] },
  { exact [expr log_eq_zero] }
end

-- error in Data.Nat.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem log_eq_one_iff
{b
 n : exprℕ()} : «expr ↔ »(«expr = »(log b n, 1), «expr ∧ »(«expr < »(n, «expr * »(b, b)), «expr ∧ »(«expr < »(1, b), «expr ≤ »(b, n)))) :=
begin
  split,
  { intro [ident h_log],
    have [ident bound] [":", expr «expr ∧ »(«expr < »(1, b), «expr ≤ »(b, n))] [],
    { contrapose [] [ident h_log],
      rw ["[", expr not_and_distrib, ",", expr not_lt, ",", expr not_le, ",", expr or_comm, ",", "<-", expr log_eq_zero_iff, "]"] ["at", ident h_log],
      rw [expr h_log] [],
      exact [expr nat.zero_ne_one] },
    cases [expr bound] ["with", ident one_lt_b, ident b_le_n],
    refine [expr ⟨_, one_lt_b, b_le_n⟩],
    rw ["[", expr log_of_one_lt_of_le one_lt_b b_le_n, ",", expr succ_inj', ",", expr log_eq_zero_iff, ",", expr nat.div_lt_iff_lt_mul _ _ (lt_trans zero_lt_one one_lt_b), "]"] ["at", ident h_log],
    exact [expr h_log.resolve_right (λ b_small, lt_irrefl _ (lt_of_lt_of_le one_lt_b b_small))] },
  { rintros ["⟨", ident h, ",", ident one_lt_b, ",", ident b_le_n, "⟩"],
    rw ["[", expr log_of_one_lt_of_le one_lt_b b_le_n, ",", expr succ_inj', ",", expr log_eq_zero_iff, ",", expr nat.div_lt_iff_lt_mul _ _ (lt_trans zero_lt_one one_lt_b), "]"] [],
    exact [expr or.inl h] }
end

@[simp]
theorem log_zero_left (n : ℕ) : log 0 n = 0 :=
  log_of_left_le_one zero_le_one

@[simp]
theorem log_zero_right (b : ℕ) : log b 0 = 0 :=
  by 
    rw [log]
    cases b <;> rfl

@[simp]
theorem log_one_left (n : ℕ) : log 1 n = 0 :=
  log_of_left_le_one le_rfl

@[simp]
theorem log_one_right (b : ℕ) : log b 1 = 0 :=
  if h : b ≤ 1 then log_of_left_le_one h else log_of_lt (not_leₓ.mp h)

-- error in Data.Nat.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `pow b` and `log b` (almost) form a Galois connection. -/
theorem pow_le_iff_le_log
{b : exprℕ()}
(hb : «expr < »(1, b))
{x y : exprℕ()}
(hy : «expr < »(0, y)) : «expr ↔ »(«expr ≤ »(«expr ^ »(b, x), y), «expr ≤ »(x, log b y)) :=
begin
  induction [expr y] ["using", ident nat.strong_induction_on] ["with", ident y, ident ih] ["generalizing", ident x],
  cases [expr x] [],
  { exact [expr iff_of_true hy (zero_le _)] },
  rw [expr log] [],
  split_ifs [] [],
  { have [ident b_pos] [":", expr «expr < »(0, b)] [":=", expr zero_le_one.trans_lt hb],
    rw ["[", expr succ_eq_add_one, ",", expr add_le_add_iff_right, ",", "<-", expr ih «expr / »(y, b) (div_lt_self hy hb) (nat.div_pos h.1 b_pos), ",", expr le_div_iff_mul_le _ _ b_pos, ",", expr pow_succ', "]"] [] },
  { refine [expr iff_of_false (λ hby, h ⟨le_trans _ hby, hb⟩) (not_succ_le_zero _)],
    convert [] [expr pow_mono hb.le (zero_lt_succ x)] [],
    exact [expr (pow_one b).symm] }
end

theorem log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
  eq_of_forall_le_iff$
    fun z =>
      by 
        rw [←pow_le_iff_le_log hb (pow_pos (zero_lt_one.trans hb) _)]
        exact (pow_right_strict_mono hb).le_iff_le

theorem log_pos {b n : ℕ} (hb : 1 < b) (hn : b ≤ n) : 0 < log b n :=
  by 
    rwa [←succ_le_iff, ←pow_le_iff_le_log hb (hb.le.trans hn), pow_oneₓ]

theorem lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 0 < x) : x < b ^ (log b x).succ :=
  by 
    rw [←not_leₓ, pow_le_iff_le_log hb hx, not_leₓ]
    exact lt_succ_self _

theorem pow_log_le_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 0 < x) : b ^ log b x ≤ x :=
  (pow_le_iff_le_log hb hx).2 le_rfl

theorem log_le_log_of_le {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
  by 
    cases' le_or_ltₓ b 1 with hb hb
    ·
      rw [log_of_left_le_one hb]
      exact zero_le _
    ·
      cases' Nat.eq_zero_or_posₓ n with hn hn
      ·
        rw [hn, log_zero_right]
        exact zero_le _
      ·
        rw [←pow_le_iff_le_log hb (hn.trans_le h)]
        exact (pow_log_le_self hb hn).trans h

theorem log_le_log_of_left_ge {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n :=
  by 
    cases n
    ·
      simp 
    rw [←pow_le_iff_le_log hc (zero_lt_succ n)]
    calc c ^ log b n.succ ≤ b ^ log b n.succ :=
      pow_le_pow_of_le_left (le_of_ltₓ$ zero_lt_one.trans hc) hb _ _ ≤ n.succ :=
      pow_log_le_self (lt_of_lt_of_leₓ hc hb) (zero_lt_succ n)

theorem log_monotone {b : ℕ} : Monotone fun n : ℕ => log b n :=
  fun x y => log_le_log_of_le

theorem log_antitone_left {n : ℕ} : AntitoneOn (fun b => log b n) (Set.Ioi 1) :=
  fun _ hc _ _ hb => log_le_log_of_left_ge (Set.mem_Iio.1 hc) hb

private theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : ((n+b) - 1) / b < n :=
  by 
    rw [div_lt_iff_lt_mul _ _ (zero_lt_one.trans hb), ←succ_le_iff, ←pred_eq_sub_one,
      succ_pred_eq_of_pos (add_pos (zero_lt_one.trans hn) (zero_lt_one.trans hb))]
    exact add_le_mul hn hb

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def clog (b : ℕ) : ℕ → ℕ
| n =>
  if h : 1 < b ∧ 1 < n then
    have  : ((n+b) - 1) / b < n := add_pred_div_lt h.1 h.2
    clog (((n+b) - 1) / b)+1
  else 0

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 :=
  by 
    rw [clog, if_neg fun h : 1 < b ∧ 1 < n => h.1.not_le hb]

theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 :=
  by 
    rw [clog, if_neg fun h : 1 < b ∧ 1 < n => h.2.not_le hn]

@[simp]
theorem clog_zero_left (n : ℕ) : clog 0 n = 0 :=
  clog_of_left_le_one zero_le_one _

@[simp]
theorem clog_zero_right (b : ℕ) : clog b 0 = 0 :=
  clog_of_right_le_one zero_le_one _

@[simp]
theorem clog_one_left (n : ℕ) : clog 1 n = 0 :=
  clog_of_left_le_one le_rfl _

@[simp]
theorem clog_one_right (b : ℕ) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _

theorem clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : clog b n = clog b (((n+b) - 1) / b)+1 :=
  by 
    rw [clog, if_pos (⟨hb, hn⟩ : 1 < b ∧ 1 < n)]

theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : 0 < clog b n :=
  by 
    rw [clog_of_two_le hb hn]
    exact zero_lt_succ _

-- error in Data.Nat.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem clog_eq_one {b n : exprℕ()} (hn : «expr ≤ »(2, n)) (h : «expr ≤ »(n, b)) : «expr = »(clog b n, 1) :=
begin
  rw ["[", expr clog_of_two_le (hn.trans h) hn, ",", expr clog_of_right_le_one, "]"] [],
  have [ident n_pos] [":", expr «expr < »(0, n)] [":=", expr zero_lt_two.trans_le hn],
  rw ["[", "<-", expr lt_succ_iff, ",", expr nat.div_lt_iff_lt_mul _ _ (n_pos.trans_le h), ",", "<-", expr succ_le_iff, ",", "<-", expr pred_eq_sub_one, ",", expr succ_pred_eq_of_pos (add_pos n_pos (n_pos.trans_le h)), ",", expr succ_mul, ",", expr one_mul, "]"] [],
  exact [expr add_le_add_right h _]
end

-- error in Data.Nat.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--`clog b` and `pow b` form a Galois connection. -/
theorem le_pow_iff_clog_le
{b : exprℕ()}
(hb : «expr < »(1, b))
{x y : exprℕ()} : «expr ↔ »(«expr ≤ »(x, «expr ^ »(b, y)), «expr ≤ »(clog b x, y)) :=
begin
  induction [expr x] ["using", ident nat.strong_induction_on] ["with", ident x, ident ih] ["generalizing", ident y],
  cases [expr y] [],
  { rw ["[", expr pow_zero, "]"] [],
    refine [expr ⟨λ h, (clog_of_right_le_one h b).le, _⟩],
    simp_rw ["<-", expr not_lt] [],
    contrapose ["!"] [],
    exact [expr clog_pos hb] },
  have [ident b_pos] [":", expr «expr < »(0, b)] [":=", expr zero_lt_two.trans_le hb],
  rw [expr clog] [],
  split_ifs [] [],
  { rw ["[", expr succ_eq_add_one, ",", expr add_le_add_iff_right, ",", "<-", expr ih «expr / »(«expr - »(«expr + »(x, b), 1), b) (add_pred_div_lt hb h.2), ",", expr nat.div_le_iff_le_mul_add_pred b_pos, ",", "<-", expr pow_succ, ",", expr add_tsub_assoc_of_le (nat.succ_le_of_lt b_pos), ",", expr add_le_add_iff_right, "]"] [] },
  { exact [expr iff_of_true «expr $ »((not_lt.1 (not_and.1 h hb)).trans, «expr $ »(succ_le_of_lt, pow_pos b_pos _)) (zero_le _)] }
end

theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff$
    fun z =>
      by 
        rw [←le_pow_iff_clog_le hb]
        exact (pow_right_strict_mono hb).le_iff_le

theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) : b ^ (clog b x).pred < x :=
  by 
    rw [←not_leₓ, le_pow_iff_clog_le hb, not_leₓ]
    exact pred_lt (clog_pos hb hx).ne'

theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (le_pow_iff_clog_le hb).2 le_rfl

theorem clog_le_clog_of_le (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m :=
  by 
    cases' le_or_ltₓ b 1 with hb hb
    ·
      rw [clog_of_left_le_one hb]
      exact zero_le _
    ·
      obtain rfl | hn := n.eq_zero_or_pos
      ·
        rw [clog_zero_right]
        exact zero_le _
      ·
        rw [←le_pow_iff_clog_le hb]
        exact h.trans (le_pow_clog hb _)

theorem clog_le_clog_of_left_ge {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n :=
  by 
    cases n
    ·
      simp 
    rw [←le_pow_iff_clog_le (lt_of_lt_of_leₓ hc hb)]
    calc n.succ ≤ c ^ clog c n.succ := le_pow_clog hc _ _ ≤ b ^ clog c n.succ :=
      pow_le_pow_of_le_left (le_of_ltₓ$ zero_lt_one.trans hc) hb _

theorem clog_monotone (b : ℕ) : Monotone (clog b) :=
  fun x y => clog_le_clog_of_le _

theorem clog_antitone_left {n : ℕ} : AntitoneOn (fun b : ℕ => clog b n) (Set.Ioi 1) :=
  fun _ hc _ _ hb => clog_le_clog_of_left_ge (Set.mem_Iio.1 hc) hb

theorem log_le_clog (b n : ℕ) : log b n ≤ clog b n :=
  by 
    obtain hb | hb := le_or_ltₓ b 1
    ·
      rw [log_of_left_le_one hb]
      exact zero_le _ 
    cases n
    ·
      rw [log_zero_right]
      exact zero_le _ 
    exact (pow_right_strict_mono hb).le_iff_le.1 ((pow_log_le_self hb$ succ_pos _).trans$ le_pow_clog hb _)

end Nat

