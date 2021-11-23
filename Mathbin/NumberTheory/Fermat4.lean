import Mathbin.NumberTheory.PythagoreanTriples 
import Mathbin.RingTheory.Coprime.Lemmas

/-!
# Fermat's Last Theorem for the case n = 4
There are no non-zero integers `a`, `b` and `c` such that `a ^ 4 + b ^ 4 = c ^ 4`.
-/


noncomputable theory

open_locale Classical

/-- Shorthand for three non-zero integers `a`, `b`, and `c` satisfying `a ^ 4 + b ^ 4 = c ^ 2`.
We will show that no integers satisfy this equation. Clearly Fermat's Last theorem for n = 4
follows. -/
def Fermat42 (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ ((a^4)+b^4) = (c^2)

namespace Fermat42

theorem comm {a b c : ℤ} : Fermat42 a b c ↔ Fermat42 b a c :=
  by 
    delta' Fermat42 
    rw [add_commₓ]
    tauto

theorem mul {a b c k : ℤ} (hk0 : k ≠ 0) : Fermat42 a b c ↔ Fermat42 (k*a) (k*b) ((k^2)*c) :=
  by 
    delta' Fermat42 
    split 
    ·
      intro f42 
      split 
      ·
        exact mul_ne_zero hk0 f42.1
      split 
      ·
        exact mul_ne_zero hk0 f42.2.1
      ·
        calc (((k*a)^4)+(k*b)^4) = (k^4)*(a^4)+b^4 :=
          by 
            ring _ = (k^4)*c^2 :=
          by 
            rw [f42.2.2]_ = (((k^2)*c)^2) :=
          by 
            ring
    ·
      intro f42 
      split 
      ·
        exact right_ne_zero_of_mul f42.1
      split 
      ·
        exact right_ne_zero_of_mul f42.2.1
      apply (mul_right_inj' (pow_ne_zero 4 hk0)).mp
      ·
        calc ((k^4)*(a^4)+b^4) = ((k*a)^4)+(k*b)^4 :=
          by 
            ring _ = (((k^2)*c)^2) :=
          by 
            rw [f42.2.2]_ = (k^4)*c^2 :=
          by 
            ring

theorem ne_zero {a b c : ℤ} (h : Fermat42 a b c) : c ≠ 0 :=
  by 
    apply
      ne_zero_pow
        (by 
          decide :
        2 ≠ 0)
    apply ne_of_gtₓ 
    rw [←h.2.2,
      (by 
        ring :
      ((a^4)+b^4) = ((a^2)^2)+(b^2)^2)]
    exact add_pos (sq_pos_of_ne_zero _ (pow_ne_zero 2 h.1)) (sq_pos_of_ne_zero _ (pow_ne_zero 2 h.2.1))

/-- We say a solution to `a ^ 4 + b ^ 4 = c ^ 2` is minimal if there is no other solution with
a smaller `c` (in absolute value). -/
def minimal (a b c : ℤ) : Prop :=
  Fermat42 a b c ∧ ∀ a1 b1 c1 : ℤ, Fermat42 a1 b1 c1 → Int.natAbs c ≤ Int.natAbs c1

-- error in NumberTheory.Fermat4: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- if we have a solution to `a ^ 4 + b ^ 4 = c ^ 2` then there must be a minimal one. -/
theorem exists_minimal {a b c : exprℤ()} (h : fermat_42 a b c) : «expr∃ , »((a0 b0 c0), minimal a0 b0 c0) :=
begin
  let [ident S] [":", expr set exprℕ()] [":=", expr {n | «expr∃ , »((s : «expr × »(exprℤ(), «expr × »(exprℤ(), exprℤ()))), «expr ∧ »(fermat_42 s.1 s.2.1 s.2.2, «expr = »(n, int.nat_abs s.2.2)))}],
  have [ident S_nonempty] [":", expr S.nonempty] [],
  { use [expr int.nat_abs c],
    rw [expr set.mem_set_of_eq] [],
    use [expr ⟨a, ⟨b, c⟩⟩],
    tauto [] },
  let [ident m] [":", expr exprℕ()] [":=", expr nat.find S_nonempty],
  have [ident m_mem] [":", expr «expr ∈ »(m, S)] [":=", expr nat.find_spec S_nonempty],
  rcases [expr m_mem, "with", "⟨", ident s0, ",", ident hs0, ",", ident hs1, "⟩"],
  use ["[", expr s0.1, ",", expr s0.2.1, ",", expr s0.2.2, ",", expr hs0, "]"],
  intros [ident a1, ident b1, ident c1, ident h1],
  rw ["<-", expr hs1] [],
  apply [expr nat.find_min'],
  use [expr ⟨a1, ⟨b1, c1⟩⟩],
  tauto []
end

-- error in NumberTheory.Fermat4: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` must have `a` and `b` coprime. -/
theorem coprime_of_minimal {a b c : exprℤ()} (h : minimal a b c) : is_coprime a b :=
begin
  apply [expr int.gcd_eq_one_iff_coprime.mp],
  by_contradiction [ident hab],
  obtain ["⟨", ident p, ",", ident hp, ",", ident hpa, ",", ident hpb, "⟩", ":=", expr nat.prime.not_coprime_iff_dvd.mp hab],
  obtain ["⟨", ident a1, ",", ident rfl, "⟩", ":=", expr int.coe_nat_dvd_left.mpr hpa],
  obtain ["⟨", ident b1, ",", ident rfl, "⟩", ":=", expr int.coe_nat_dvd_left.mpr hpb],
  have [ident hpc] [":", expr «expr ∣ »(«expr ^ »((p : exprℤ()), 2), c)] [],
  { apply [expr (int.pow_dvd_pow_iff (exprdec_trivial() : «expr < »(0, 2))).mp],
    rw ["<-", expr h.1.2.2] [],
    apply [expr dvd.intro «expr + »(«expr ^ »(a1, 4), «expr ^ »(b1, 4))],
    ring [] },
  obtain ["⟨", ident c1, ",", ident rfl, "⟩", ":=", expr hpc],
  have [ident hf] [":", expr fermat_42 a1 b1 c1] [],
  exact [expr (fermat_42.mul (int.coe_nat_ne_zero.mpr (nat.prime.ne_zero hp))).mpr h.1],
  apply [expr nat.le_lt_antisymm (h.2 _ _ _ hf)],
  rw ["[", expr int.nat_abs_mul, ",", expr lt_mul_iff_one_lt_left, ",", expr int.nat_abs_pow, ",", expr int.nat_abs_of_nat, "]"] [],
  { exact [expr nat.one_lt_pow _ _ (show «expr < »(0, 2), from exprdec_trivial()) (nat.prime.one_lt hp)] },
  { exact [expr nat.pos_of_ne_zero (int.nat_abs_ne_zero_of_ne_zero (ne_zero hf))] }
end

/-- We can swap `a` and `b` in a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2`. -/
theorem minimal_comm {a b c : ℤ} : minimal a b c → minimal b a c :=
  fun ⟨h1, h2⟩ => ⟨Fermat42.comm.mp h1, h2⟩

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has positive `c`. -/
theorem neg_of_minimal {a b c : ℤ} : minimal a b c → minimal a b (-c) :=
  by 
    rintro ⟨⟨ha, hb, heq⟩, h2⟩
    split 
    ·
      apply And.intro ha (And.intro hb _)
      rw [HEq]
      exact (neg_sq c).symm 
    rwa [Int.nat_abs_neg c]

-- error in NumberTheory.Fermat4: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has `a` odd. -/
theorem exists_odd_minimal
{a b c : exprℤ()}
(h : fermat_42 a b c) : «expr∃ , »((a0 b0 c0), «expr ∧ »(minimal a0 b0 c0, «expr = »(«expr % »(a0, 2), 1))) :=
begin
  obtain ["⟨", ident a0, ",", ident b0, ",", ident c0, ",", ident hf, "⟩", ":=", expr exists_minimal h],
  cases [expr int.mod_two_eq_zero_or_one a0] ["with", ident hap, ident hap],
  { cases [expr int.mod_two_eq_zero_or_one b0] ["with", ident hbp, ident hbp],
    { exfalso,
      have [ident h1] [":", expr «expr ∣ »(2, (int.gcd a0 b0 : exprℤ()))] [],
      { exact [expr int.dvd_gcd (int.dvd_of_mod_eq_zero hap) (int.dvd_of_mod_eq_zero hbp)] },
      rw [expr int.gcd_eq_one_iff_coprime.mpr (coprime_of_minimal hf)] ["at", ident h1],
      revert [ident h1],
      norm_num [] [] },
    { exact [expr ⟨b0, ⟨a0, ⟨c0, minimal_comm hf, hbp⟩⟩⟩] } },
  exact [expr ⟨a0, ⟨b0, ⟨c0, hf, hap⟩⟩⟩]
end

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has
`a` odd and `c` positive. -/
theorem exists_pos_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) : ∃ a0 b0 c0, minimal a0 b0 c0 ∧ a0 % 2 = 1 ∧ 0 < c0 :=
  by 
    obtain ⟨a0, b0, c0, hf, hc⟩ := exists_odd_minimal h 
    rcases lt_trichotomyₓ 0 c0 with (h1 | rfl | h1)
    ·
      use a0, b0, c0 
      tauto
    ·
      exfalso 
      exact ne_zero hf.1 rfl
    ·
      use a0, b0, -c0, neg_of_minimal hf, hc 
      exact neg_pos.mpr h1

end Fermat42

theorem Int.coprime_of_sq_sum {r s : ℤ} (h2 : IsCoprime s r) : IsCoprime ((r^2)+s^2) r :=
  by 
    rw [sq, sq]
    exact (IsCoprime.mul_left h2 h2).mul_add_left_left r

theorem Int.coprime_of_sq_sum' {r s : ℤ} (h : IsCoprime r s) : IsCoprime ((r^2)+s^2) (r*s) :=
  by 
    apply IsCoprime.mul_right (Int.coprime_of_sq_sum (is_coprime_comm.mp h))
    rw [add_commₓ]
    apply Int.coprime_of_sq_sum h

namespace Fermat42

-- error in NumberTheory.Fermat4: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem not_minimal
{a b c : exprℤ()}
(h : minimal a b c)
(ha2 : «expr = »(«expr % »(a, 2), 1))
(hc : «expr < »(0, c)) : false :=
begin
  have [ident ht] [":", expr pythagorean_triple «expr ^ »(a, 2) «expr ^ »(b, 2) c] [],
  { calc
      «expr = »(«expr + »(«expr * »(«expr ^ »(a, 2), «expr ^ »(a, 2)), «expr * »(«expr ^ »(b, 2), «expr ^ »(b, 2))), «expr + »(«expr ^ »(a, 4), «expr ^ »(b, 4))) : by ring []
      «expr = »(..., «expr ^ »(c, 2)) : by rw [expr h.1.2.2] []
      «expr = »(..., «expr * »(c, c)) : by rw [expr sq] [] },
  have [ident h2] [":", expr «expr = »(int.gcd «expr ^ »(a, 2) «expr ^ »(b, 2), 1)] [":=", expr int.gcd_eq_one_iff_coprime.mpr (coprime_of_minimal h).pow],
  have [ident ha22] [":", expr «expr = »(«expr % »(«expr ^ »(a, 2), 2), 1)] [],
  { rw ["[", expr sq, ",", expr int.mul_mod, ",", expr ha2, "]"] [],
    norm_num [] [] },
  obtain ["⟨", ident m, ",", ident n, ",", ident ht1, ",", ident ht2, ",", ident ht3, ",", ident ht4, ",", ident ht5, ",", ident ht6, "⟩", ":=", expr pythagorean_triple.coprime_classification' ht h2 ha22 hc],
  have [ident htt] [":", expr pythagorean_triple a n m] [],
  { delta [ident pythagorean_triple] [],
    rw ["[", "<-", expr sq, ",", "<-", expr sq, ",", "<-", expr sq, "]"] [],
    exact [expr add_eq_of_eq_sub ht1] },
  have [ident h3] [":", expr «expr = »(int.gcd a n, 1)] [],
  { apply [expr int.gcd_eq_one_iff_coprime.mpr],
    apply [expr @is_coprime.of_mul_left_left _ _ _ a],
    rw ["[", "<-", expr sq, ",", expr ht1, ",", expr (by ring [] : «expr = »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), «expr + »(«expr ^ »(m, 2), «expr * »(«expr- »(n), n)))), "]"] [],
    exact [expr (int.gcd_eq_one_iff_coprime.mp ht4).pow_left.add_mul_right_left «expr- »(n)] },
  have [ident hb20] [":", expr «expr ≠ »(«expr ^ »(b, 2), 0)] [":=", expr mt pow_eq_zero h.1.2.1],
  have [ident h4] [":", expr «expr < »(0, m)] [],
  { apply [expr lt_of_le_of_ne ht6],
    rintro [ident rfl],
    revert [ident hb20],
    rw [expr ht2] [],
    simp [] [] [] [] [] [] },
  obtain ["⟨", ident r, ",", ident s, ",", ident htt1, ",", ident htt2, ",", ident htt3, ",", ident htt4, ",", ident htt5, ",", ident htt6, "⟩", ":=", expr pythagorean_triple.coprime_classification' htt h3 ha2 h4],
  have [ident hcp] [":", expr «expr = »(int.gcd m «expr * »(r, s), 1)] [],
  { rw [expr htt3] [],
    exact [expr int.gcd_eq_one_iff_coprime.mpr (int.coprime_of_sq_sum' (int.gcd_eq_one_iff_coprime.mp htt4))] },
  have [ident hb2] [":", expr «expr ∣ »(2, b)] [],
  { apply [expr @int.prime.dvd_pow' _ 2 _ (by norm_num [] [] : nat.prime 2)],
    rw ["[", expr ht2, ",", expr mul_assoc, "]"] [],
    exact [expr dvd_mul_right 2 «expr * »(m, n)] },
  cases [expr hb2] ["with", ident b', ident hb2'],
  have [ident hs] [":", expr «expr = »(«expr ^ »(b', 2), «expr * »(m, «expr * »(r, s)))] [],
  { apply [expr (mul_right_inj' (by norm_num [] [] : «expr ≠ »((4 : exprℤ()), 0))).mp],
    calc
      «expr = »(«expr * »(4, «expr ^ »(b', 2)), «expr * »(«expr * »(2, b'), «expr * »(2, b'))) : by ring []
      «expr = »(..., «expr * »(«expr * »(2, m), «expr * »(«expr * »(2, r), s))) : by rw ["[", "<-", expr hb2', ",", "<-", expr sq, ",", expr ht2, ",", expr htt2, "]"] []
      «expr = »(..., «expr * »(4, «expr * »(m, «expr * »(r, s)))) : by ring [] },
  have [ident hrsz] [":", expr «expr ≠ »(«expr * »(r, s), 0)] [],
  { by_contradiction [ident hrsz],
    revert [ident hb20],
    rw ["[", expr ht2, ",", expr htt2, ",", expr mul_assoc, ",", expr @mul_assoc _ _ _ r s, ",", expr hrsz, "]"] [],
    simp [] [] [] [] [] [] },
  have [ident h2b0] [":", expr «expr ≠ »(b', 0)] [],
  { apply [expr ne_zero_pow (exprdec_trivial() : «expr ≠ »(2, 0))],
    rw [expr hs] [],
    apply [expr mul_ne_zero],
    { exact [expr ne_of_gt h4] },
    { exact [expr hrsz] } },
  obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr int.sq_of_gcd_eq_one hcp hs.symm],
  have [ident hi'] [":", expr «expr¬ »(«expr = »(m, «expr- »(«expr ^ »(i, 2))))] [],
  { by_contradiction [ident h1],
    have [ident hit] [":", expr «expr ≤ »(«expr- »(«expr ^ »(i, 2)), 0)] [],
    apply [expr neg_nonpos.mpr (sq_nonneg i)],
    rw ["<-", expr h1] ["at", ident hit],
    apply [expr absurd h4 (not_lt.mpr hit)] },
  replace [ident hi] [":", expr «expr = »(m, «expr ^ »(i, 2))] [],
  { apply [expr or.resolve_right hi hi'] },
  rw [expr mul_comm] ["at", ident hs],
  rw ["[", expr int.gcd_comm, "]"] ["at", ident hcp],
  obtain ["⟨", ident d, ",", ident hd, "⟩", ":=", expr int.sq_of_gcd_eq_one hcp hs.symm],
  have [ident hd'] [":", expr «expr¬ »(«expr = »(«expr * »(r, s), «expr- »(«expr ^ »(d, 2))))] [],
  { by_contradiction [ident h1],
    rw [expr h1] ["at", ident hs],
    have [ident h2] [":", expr «expr ≤ »(«expr ^ »(b', 2), 0)] [],
    { rw ["[", expr hs, ",", expr (by ring [] : «expr = »(«expr * »(«expr- »(«expr ^ »(d, 2)), m), «expr- »(«expr * »(«expr ^ »(d, 2), m)))), "]"] [],
      exact [expr neg_nonpos.mpr ((zero_le_mul_right h4).mpr (sq_nonneg d))] },
    have [ident h2'] [":", expr «expr ≤ »(0, «expr ^ »(b', 2))] [],
    { apply [expr sq_nonneg b'] },
    exact [expr absurd (lt_of_le_of_ne h2' (ne.symm (pow_ne_zero _ h2b0))) (not_lt.mpr h2)] },
  replace [ident hd] [":", expr «expr = »(«expr * »(r, s), «expr ^ »(d, 2))] [],
  { apply [expr or.resolve_right hd hd'] },
  obtain ["⟨", ident j, ",", ident hj, "⟩", ":=", expr int.sq_of_gcd_eq_one htt4 hd],
  have [ident hj0] [":", expr «expr ≠ »(j, 0)] [],
  { intro [ident h0],
    rw ["[", expr h0, ",", expr zero_pow (exprdec_trivial() : «expr < »(0, 2)), ",", expr neg_zero, ",", expr or_self, "]"] ["at", ident hj],
    apply [expr left_ne_zero_of_mul hrsz hj] },
  rw [expr mul_comm] ["at", ident hd],
  rw ["[", expr int.gcd_comm, "]"] ["at", ident htt4],
  obtain ["⟨", ident k, ",", ident hk, "⟩", ":=", expr int.sq_of_gcd_eq_one htt4 hd],
  have [ident hk0] [":", expr «expr ≠ »(k, 0)] [],
  { intro [ident h0],
    rw ["[", expr h0, ",", expr zero_pow (exprdec_trivial() : «expr < »(0, 2)), ",", expr neg_zero, ",", expr or_self, "]"] ["at", ident hk],
    apply [expr right_ne_zero_of_mul hrsz hk] },
  have [ident hj2] [":", expr «expr = »(«expr ^ »(r, 2), «expr ^ »(j, 4))] [],
  { cases [expr hj] ["with", ident hjp, ident hjp]; { rw [expr hjp] [],
      ring [] } },
  have [ident hk2] [":", expr «expr = »(«expr ^ »(s, 2), «expr ^ »(k, 4))] [],
  { cases [expr hk] ["with", ident hkp, ident hkp]; { rw [expr hkp] [],
      ring [] } },
  have [ident hh] [":", expr «expr = »(«expr ^ »(i, 2), «expr + »(«expr ^ »(j, 4), «expr ^ »(k, 4)))] [],
  { rw ["[", "<-", expr hi, ",", expr htt3, ",", expr hj2, ",", expr hk2, "]"] [] },
  have [ident hn] [":", expr «expr ≠ »(n, 0)] [],
  { rw [expr ht2] ["at", ident hb20],
    apply [expr right_ne_zero_of_mul hb20] },
  have [ident hic] [":", expr «expr < »(int.nat_abs i, int.nat_abs c)] [],
  { apply [expr int.coe_nat_lt.mp],
    rw ["<-", expr int.eq_nat_abs_of_zero_le (le_of_lt hc)] [],
    apply [expr gt_of_gt_of_ge _ (int.abs_le_self_sq i)],
    rw ["[", "<-", expr hi, ",", expr ht3, "]"] [],
    apply [expr gt_of_gt_of_ge _ (int.le_self_sq m)],
    exact [expr lt_add_of_pos_right «expr ^ »(m, 2) (sq_pos_of_ne_zero n hn)] },
  have [ident hic'] [":", expr «expr ≤ »(int.nat_abs c, int.nat_abs i)] [],
  { apply [expr h.2 j k i],
    exact [expr ⟨hj0, hk0, hh.symm⟩] },
  apply [expr absurd (not_le_of_lt hic) (not_not.mpr hic')]
end

end Fermat42

theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : ((a^4)+b^4) ≠ (c^2) :=
  by 
    intro h 
    obtain ⟨a0, b0, c0, ⟨hf, h2, hp⟩⟩ := Fermat42.exists_pos_odd_minimal (And.intro ha (And.intro hb h))
    apply Fermat42.not_minimal hf h2 hp

theorem not_fermat_4 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : ((a^4)+b^4) ≠ (c^4) :=
  by 
    intro heq 
    apply @not_fermat_42 _ _ (c^2) ha hb 
    rw [HEq]
    ring

