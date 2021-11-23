import Mathbin.NumberTheory.ClassNumber.AdmissibleAbsoluteValue 
import Mathbin.Analysis.SpecialFunctions.Pow 
import Mathbin.RingTheory.Ideal.LocalRing 
import Mathbin.Data.Polynomial.Degree.CardPowDegree

/-!
# Admissible absolute values on polynomials
This file defines an admissible absolute value
`polynomial.card_pow_degree_is_admissible` which we use to show the class number
of the ring of integers of a function field is finite.

## Main results

* `polynomial.card_pow_degree_is_admissible` shows `card_pow_degree`,
  mapping `p : polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/


namespace Polynomial

open AbsoluteValue Real

variable{Fq : Type _}[Field Fq][Fintype Fq]

-- error in NumberTheory.ClassNumber.AdmissibleCardPowDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `A` is a family of enough low-degree polynomials over a finite field, there is a
pair of equal elements in `A`. -/
theorem exists_eq_polynomial
{d : exprℕ()}
{m : exprℕ()}
(hm : «expr ≤ »(«expr ^ »(fintype.card Fq, d), m))
(b : polynomial Fq)
(hb : «expr ≤ »(nat_degree b, d))
(A : fin m.succ → polynomial Fq)
(hA : ∀
 i, «expr < »(degree (A i), degree b)) : «expr∃ , »((i₀ i₁), «expr ∧ »(«expr ≠ »(i₀, i₁), «expr = »(A i₁, A i₀))) :=
begin
  set [] [ident f] [":", expr fin m.succ → fin d → Fq] [":="] [expr λ i j, (A i).coeff j] [],
  have [] [":", expr «expr < »(fintype.card (fin d → Fq), fintype.card (fin m.succ))] [],
  { simpa [] [] [] [] [] ["using", expr lt_of_le_of_lt hm (nat.lt_succ_self m)] },
  obtain ["⟨", ident i₀, ",", ident i₁, ",", ident i_ne, ",", ident i_eq, "⟩", ":=", expr fintype.exists_ne_map_eq_of_card_lt f this],
  use ["[", expr i₀, ",", expr i₁, ",", expr i_ne, "]"],
  ext [] [ident j] [],
  by_cases [expr hbj, ":", expr «expr ≤ »(degree b, j)],
  { rw ["[", expr coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj), ",", expr coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj), "]"] [] },
  rw [expr not_le] ["at", ident hbj],
  apply [expr congr_fun i_eq.symm ⟨j, _⟩],
  exact [expr lt_of_lt_of_le (coe_lt_degree.mp hbj) hb]
end

-- error in NumberTheory.ClassNumber.AdmissibleCardPowDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that their difference has small degree. -/
theorem exists_approx_polynomial_aux
{d : exprℕ()}
{m : exprℕ()}
(hm : «expr ≤ »(«expr ^ »(fintype.card Fq, d), m))
(b : polynomial Fq)
(A : fin m.succ → polynomial Fq)
(hA : ∀
 i, «expr < »(degree (A i), degree b)) : «expr∃ , »((i₀
  i₁), «expr ∧ »(«expr ≠ »(i₀, i₁), «expr < »(degree «expr - »(A i₁, A i₀), «expr↑ »(«expr - »(nat_degree b, d))))) :=
begin
  have [ident hb] [":", expr «expr ≠ »(b, 0)] [],
  { rintro [ident rfl],
    specialize [expr hA 0],
    rw [expr degree_zero] ["at", ident hA],
    exact [expr not_lt_of_le bot_le hA] },
  set [] [ident f] [":", expr fin m.succ → fin d → Fq] [":="] [expr λ
   i j, (A i).coeff «expr - »(nat_degree b, j.succ)] [],
  have [] [":", expr «expr < »(fintype.card (fin d → Fq), fintype.card (fin m.succ))] [],
  { simpa [] [] [] [] [] ["using", expr lt_of_le_of_lt hm (nat.lt_succ_self m)] },
  obtain ["⟨", ident i₀, ",", ident i₁, ",", ident i_ne, ",", ident i_eq, "⟩", ":=", expr fintype.exists_ne_map_eq_of_card_lt f this],
  use ["[", expr i₀, ",", expr i₁, ",", expr i_ne, "]"],
  refine [expr (degree_lt_iff_coeff_zero _ _).mpr (λ j hj, _)],
  by_cases [expr hbj, ":", expr «expr ≤ »(degree b, j)],
  { refine [expr coeff_eq_zero_of_degree_lt (lt_of_lt_of_le _ hbj)],
    exact [expr lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hA _) (hA _))] },
  rw ["[", expr coeff_sub, ",", expr sub_eq_zero, "]"] [],
  rw ["[", expr not_le, ",", expr degree_eq_nat_degree hb, ",", expr with_bot.coe_lt_coe, "]"] ["at", ident hbj],
  have [ident hj] [":", expr «expr < »(«expr - »(nat_degree b, j.succ), d)] [],
  { by_cases [expr hd, ":", expr «expr < »(nat_degree b, d)],
    { exact [expr lt_of_le_of_lt tsub_le_self hd] },
    { rw [expr not_lt] ["at", ident hd],
      have [] [] [":=", expr lt_of_le_of_lt hj (nat.lt_succ_self j)],
      rwa ["[", expr tsub_lt_iff_tsub_lt hd hbj, "]"] ["at", ident this] } },
  have [] [":", expr «expr = »(j, «expr - »(b.nat_degree, «expr - »(nat_degree b, j.succ).succ))] [],
  { rw ["[", "<-", expr nat.succ_sub hbj, ",", expr nat.succ_sub_succ, ",", expr tsub_tsub_cancel_of_le hbj.le, "]"] [] },
  convert [] [expr congr_fun i_eq.symm ⟨«expr - »(nat_degree b, j.succ), hj⟩] []
end

-- error in NumberTheory.ClassNumber.AdmissibleCardPowDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that the difference of their remainders is close together. -/
theorem exists_approx_polynomial
{b : polynomial Fq}
(hb : «expr ≠ »(b, 0))
{ε : exprℝ()}
(hε : «expr < »(0, ε))
(A : fin «expr ^ »(fintype.card Fq, «expr⌈ ⌉₊»(«expr / »(«expr- »(log ε), log (fintype.card Fq)))).succ → polynomial Fq) : «expr∃ , »((i₀
  i₁), «expr ∧ »(«expr ≠ »(i₀, i₁), «expr < »((card_pow_degree «expr - »(«expr % »(A i₁, b), «expr % »(A i₀, b)) : exprℝ()), «expr • »(card_pow_degree b, ε)))) :=
begin
  have [ident hbε] [":", expr «expr < »(0, «expr • »(card_pow_degree b, ε))] [],
  { rw ["[", expr algebra.smul_def, ",", expr ring_hom.eq_int_cast, "]"] [],
    exact [expr mul_pos (int.cast_pos.mpr (absolute_value.pos _ hb)) hε] },
  have [ident one_lt_q] [":", expr «expr < »(1, fintype.card Fq)] [":=", expr fintype.one_lt_card],
  have [ident one_lt_q'] [":", expr «expr < »((1 : exprℝ()), fintype.card Fq)] [],
  { assumption_mod_cast },
  have [ident q_pos] [":", expr «expr < »(0, fintype.card Fq)] [],
  { linarith [] [] [] },
  have [ident q_pos'] [":", expr «expr < »((0 : exprℝ()), fintype.card Fq)] [],
  { assumption_mod_cast },
  by_cases [expr le_b, ":", expr «expr ≤ »(b.nat_degree, «expr⌈ ⌉₊»(«expr / »(«expr- »(log ε), log (fintype.card Fq))))],
  { obtain ["⟨", ident i₀, ",", ident i₁, ",", ident i_ne, ",", ident mod_eq, "⟩", ":=", expr exists_eq_polynomial le_rfl b le_b (λ
      i, «expr % »(A i, b)) (λ i, euclidean_domain.mod_lt (A i) hb)],
    refine [expr ⟨i₀, i₁, i_ne, _⟩],
    simp [] [] ["only"] [] [] ["at", ident mod_eq],
    rwa ["[", expr mod_eq, ",", expr sub_self, ",", expr absolute_value.map_zero, ",", expr int.cast_zero, "]"] [] },
  rw [expr not_le] ["at", ident le_b],
  obtain ["⟨", ident i₀, ",", ident i₁, ",", ident i_ne, ",", ident deg_lt, "⟩", ":=", expr exists_approx_polynomial_aux le_rfl b (λ
    i, «expr % »(A i, b)) (λ i, euclidean_domain.mod_lt (A i) hb)],
  simp [] [] ["only"] [] [] ["at", ident deg_lt],
  use ["[", expr i₀, ",", expr i₁, ",", expr i_ne, "]"],
  by_cases [expr h, ":", expr «expr = »(«expr % »(A i₁, b), «expr % »(A i₀, b))],
  { rwa ["[", expr h, ",", expr sub_self, ",", expr absolute_value.map_zero, ",", expr int.cast_zero, "]"] [] },
  have [ident h'] [":", expr «expr ≠ »(«expr - »(«expr % »(A i₁, b), «expr % »(A i₀, b)), 0)] [":=", expr mt sub_eq_zero.mp h],
  suffices [] [":", expr «expr < »((nat_degree «expr - »(«expr % »(A i₁, b), «expr % »(A i₀, b)) : exprℝ()), «expr + »(b.nat_degree, «expr / »(log ε, log (fintype.card Fq))))],
  { rwa ["[", "<-", expr real.log_lt_log_iff (int.cast_pos.mpr (card_pow_degree.pos h')) hbε, ",", expr card_pow_degree_nonzero _ h', ",", expr card_pow_degree_nonzero _ hb, ",", expr algebra.smul_def, ",", expr ring_hom.eq_int_cast, ",", expr int.cast_pow, ",", expr int.cast_coe_nat, ",", expr int.cast_pow, ",", expr int.cast_coe_nat, ",", expr log_mul (pow_ne_zero _ q_pos'.ne') hε.ne', ",", "<-", expr rpow_nat_cast, ",", "<-", expr rpow_nat_cast, ",", expr log_rpow q_pos', ",", expr log_rpow q_pos', ",", "<-", expr lt_div_iff (log_pos one_lt_q'), ",", expr add_div, ",", expr mul_div_cancel _ (log_pos one_lt_q').ne', "]"] [] },
  refine [expr lt_of_lt_of_le (nat.cast_lt.mpr (with_bot.coe_lt_coe.mp _)) _],
  swap,
  { convert [] [expr deg_lt] [],
    rw [expr degree_eq_nat_degree h'] [] },
  rw ["[", "<-", expr sub_neg_eq_add, ",", expr neg_div, "]"] [],
  refine [expr le_trans _ (sub_le_sub_left (nat.le_ceil _) (b.nat_degree : exprℝ()))],
  rw ["<-", expr neg_div] [],
  exact [expr le_of_eq (nat.cast_sub le_b.le)]
end

-- error in NumberTheory.ClassNumber.AdmissibleCardPowDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x` is close to `y` and `y` is close to `z`, then `x` and `z` are at least as close. -/
theorem card_pow_degree_anti_archimedean
{x y z : polynomial Fq}
{a : exprℤ()}
(hxy : «expr < »(card_pow_degree «expr - »(x, y), a))
(hyz : «expr < »(card_pow_degree «expr - »(y, z), a)) : «expr < »(card_pow_degree «expr - »(x, z), a) :=
begin
  have [ident ha] [":", expr «expr < »(0, a)] [":=", expr lt_of_le_of_lt (absolute_value.nonneg _ _) hxy],
  by_cases [expr hxy', ":", expr «expr = »(x, y)],
  { rwa [expr hxy'] [] },
  by_cases [expr hyz', ":", expr «expr = »(y, z)],
  { rwa ["<-", expr hyz'] [] },
  by_cases [expr hxz', ":", expr «expr = »(x, z)],
  { rwa ["[", expr hxz', ",", expr sub_self, ",", expr absolute_value.map_zero, "]"] [] },
  rw ["[", "<-", expr ne.def, ",", "<-", expr sub_ne_zero, "]"] ["at", ident hxy', ident hyz', ident hxz'],
  refine [expr lt_of_le_of_lt _ (max_lt hxy hyz)],
  rw ["[", expr card_pow_degree_nonzero _ hxz', ",", expr card_pow_degree_nonzero _ hxy', ",", expr card_pow_degree_nonzero _ hyz', "]"] [],
  have [] [":", expr «expr ≤ »((1 : exprℤ()), fintype.card Fq)] [],
  { exact_mod_cast [expr (@fintype.one_lt_card Fq _ _).le] },
  simp [] [] ["only"] ["[", expr int.cast_pow, ",", expr int.cast_coe_nat, ",", expr le_max_iff, "]"] [] [],
  refine [expr or.imp (pow_le_pow this) (pow_le_pow this) _],
  rw ["[", expr nat_degree_le_iff_degree_le, ",", expr nat_degree_le_iff_degree_le, ",", "<-", expr le_max_iff, ",", "<-", expr degree_eq_nat_degree hxy', ",", "<-", expr degree_eq_nat_degree hyz', "]"] [],
  convert [] [expr degree_add_le «expr - »(x, y) «expr - »(y, z)] ["using", 2],
  exact [expr (sub_add_sub_cancel _ _ _).symm]
end

-- error in NumberTheory.ClassNumber.AdmissibleCardPowDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A slightly stronger version of `exists_partition` on which we perform induction on `n`:
for all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into equivalence classes, where the equivalence(!) relation is "closer than `ε`". -/
theorem exists_partition_polynomial_aux
(n : exprℕ())
{ε : exprℝ()}
(hε : «expr < »(0, ε))
{b : polynomial Fq}
(hb : «expr ≠ »(b, 0))
(A : fin n → polynomial Fq) : «expr∃ , »((t : fin n → fin «expr ^ »(fintype.card Fq, «expr⌈ ⌉₊»(«expr / »(«expr- »(log ε), log (fintype.card Fq))))), ∀
 i₀
 i₁ : fin n, «expr ↔ »(«expr = »(t i₀, t i₁), «expr < »((card_pow_degree «expr - »(«expr % »(A i₁, b), «expr % »(A i₀, b)) : exprℝ()), «expr • »(card_pow_degree b, ε)))) :=
begin
  have [ident hbε] [":", expr «expr < »(0, «expr • »(card_pow_degree b, ε))] [],
  { rw ["[", expr algebra.smul_def, ",", expr ring_hom.eq_int_cast, "]"] [],
    exact [expr mul_pos (int.cast_pos.mpr (absolute_value.pos _ hb)) hε] },
  induction [expr n] [] ["with", ident n, ident ih] [],
  { refine [expr ⟨fin_zero_elim, fin_zero_elim⟩] },
  have [ident anti_archim'] [":", expr ∀
   {i j k}
   {ε : exprℝ()}, «expr < »((card_pow_degree «expr - »(«expr % »(A i, b), «expr % »(A j, b)) : exprℝ()), ε) → «expr < »((card_pow_degree «expr - »(«expr % »(A j, b), «expr % »(A k, b)) : exprℝ()), ε) → «expr < »((card_pow_degree «expr - »(«expr % »(A i, b), «expr % »(A k, b)) : exprℝ()), ε)] [],
  { intros [ident i, ident j, ident k, ident ε],
    simp_rw ["[", "<-", expr int.lt_ceil, "]"] [],
    exact [expr card_pow_degree_anti_archimedean] },
  obtain ["⟨", ident t', ",", ident ht', "⟩", ":=", expr ih (fin.tail A)],
  suffices [] [":", expr «expr∃ , »((j), ∀
    i, «expr ↔ »(«expr = »(t' i, j), «expr < »((card_pow_degree «expr - »(«expr % »(A 0, b), «expr % »(A i.succ, b)) : exprℝ()), «expr • »(card_pow_degree b, ε))))],
  { obtain ["⟨", ident j, ",", ident hj, "⟩", ":=", expr this],
    refine [expr ⟨fin.cons j t', λ i₀ i₁, _⟩],
    refine [expr fin.cases _ (λ i₀, _) i₀]; refine [expr fin.cases _ (λ i₁, _) i₁],
    { simpa [] [] [] [] [] ["using", expr hbε] },
    { rw ["[", expr fin.cons_succ, ",", expr fin.cons_zero, ",", expr eq_comm, ",", expr absolute_value.map_sub, "]"] [],
      exact [expr hj i₁] },
    { rw ["[", expr fin.cons_succ, ",", expr fin.cons_zero, "]"] [],
      exact [expr hj i₀] },
    { rw ["[", expr fin.cons_succ, ",", expr fin.cons_succ, "]"] [],
      exact [expr ht' i₀ i₁] } },
  obtain ["⟨", ident j, ",", ident hj, "⟩", ":", expr «expr∃ , »((j), ∀
    i : fin n, «expr = »(t' i, j) → «expr < »((card_pow_degree «expr - »(«expr % »(A 0, b), «expr % »(A i.succ, b)) : exprℝ()), «expr • »(card_pow_degree b, ε)))],
  { by_contra [ident this],
    push_neg ["at", ident this],
    obtain ["⟨", ident j₀, ",", ident j₁, ",", ident j_ne, ",", ident approx, "⟩", ":=", expr exists_approx_polynomial hb hε (fin.cons (A 0) (λ
       j, A (fin.succ (classical.some (this j)))))],
    revert [ident j_ne, ident approx],
    refine [expr fin.cases _ (λ j₀, _) j₀]; refine [expr fin.cases (λ j_ne approx, _) (λ j₁ j_ne approx, _) j₁],
    { exact [expr absurd rfl j_ne] },
    { rw ["[", expr fin.cons_succ, ",", expr fin.cons_zero, ",", "<-", expr not_le, ",", expr absolute_value.map_sub, "]"] ["at", ident approx],
      have [] [] [":=", expr (classical.some_spec (this j₁)).2],
      contradiction },
    { rw ["[", expr fin.cons_succ, ",", expr fin.cons_zero, ",", "<-", expr not_le, "]"] ["at", ident approx],
      have [] [] [":=", expr (classical.some_spec (this j₀)).2],
      contradiction },
    { rw ["[", expr fin.cons_succ, ",", expr fin.cons_succ, "]"] ["at", ident approx],
      rw ["[", expr ne.def, ",", expr fin.succ_inj, "]"] ["at", ident j_ne],
      have [] [":", expr «expr = »(j₀, j₁)] [":=", expr (classical.some_spec (this j₀)).1.symm.trans (((ht' (classical.some (this j₀)) (classical.some (this j₁))).mpr approx).trans (classical.some_spec (this j₁)).1)],
      contradiction } },
  by_cases [expr exists_nonempty_j, ":", expr «expr∃ , »((j), «expr ∧ »(«expr∃ , »((i), «expr = »(t' i, j)), ∀
     i, «expr = »(t' i, j) → «expr < »((card_pow_degree «expr - »(«expr % »(A 0, b), «expr % »(A i.succ, b)) : exprℝ()), «expr • »(card_pow_degree b, ε))))],
  { obtain ["⟨", ident j, ",", "⟨", ident i, ",", ident hi, "⟩", ",", ident hj, "⟩", ":=", expr exists_nonempty_j],
    refine [expr ⟨j, λ i', ⟨hj i', λ hi', trans ((ht' _ _).mpr _) hi⟩⟩],
    apply [expr anti_archim' _ hi'],
    rw [expr absolute_value.map_sub] [],
    exact [expr hj _ hi] },
  refine [expr ⟨j, λ i, ⟨hj i, λ hi, _⟩⟩],
  have [] [] [":=", expr exists_nonempty_j ⟨t' i, ⟨i, rfl⟩, λ i' hi', anti_archim' hi ((ht' _ _).mp hi')⟩],
  contradiction
end

/-- For all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into classes, where all remainders in a class are close together. -/
theorem exists_partition_polynomial (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : Polynomial Fq} (hb : b ≠ 0)
  (A : Finₓ n → Polynomial Fq) :
  ∃ t : Finₓ n → Finₓ (Fintype.card Fq^⌈-log ε / log (Fintype.card Fq)⌉₊),
    ∀ i₀ i₁ : Finₓ n, t i₀ = t i₁ → (card_pow_degree (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree b • ε :=
  by 
    obtain ⟨t, ht⟩ := exists_partition_polynomial_aux n hε hb A 
    exact ⟨t, fun i₀ i₁ hi => (ht i₀ i₁).mp hi⟩

/-- `λ p, fintype.card Fq ^ degree p` is an admissible absolute value.
We set `q ^ degree 0 = 0`. -/
noncomputable def card_pow_degree_is_admissible : is_admissible (card_pow_degree : AbsoluteValue (Polynomial Fq) ℤ) :=
  { @card_pow_degree_is_euclidean Fq _ _ with card := fun ε => Fintype.card Fq^⌈-log ε / log (Fintype.card Fq)⌉₊,
    exists_partition' := fun n ε hε b hb => exists_partition_polynomial n hε hb }

end Polynomial

