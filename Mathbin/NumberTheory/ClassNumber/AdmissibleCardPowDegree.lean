import Mathbin.Data.Polynomial.Degree.CardPowDegree 
import Mathbin.FieldTheory.Finite.Basic 
import Mathbin.NumberTheory.ClassNumber.AdmissibleAbsoluteValue

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

/-- If `A` is a family of enough low-degree polynomials over a finite field, there is a
pair of equal elements in `A`. -/
theorem exists_eq_polynomial {d : ℕ} {m : ℕ} (hm : (Fintype.card Fq^d) ≤ m) (b : Polynomial Fq) (hb : nat_degree b ≤ d)
  (A : Finₓ m.succ → Polynomial Fq) (hA : ∀ i, degree (A i) < degree b) : ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀ :=
  by 
    set f : Finₓ m.succ → Finₓ d → Fq := fun i j => (A i).coeff j 
    have  : Fintype.card (Finₓ d → Fq) < Fintype.card (Finₓ m.succ)
    ·
      simpa using lt_of_le_of_ltₓ hm (Nat.lt_succ_selfₓ m)
    obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this 
    use i₀, i₁, i_ne 
    ext j 
    byCases' hbj : degree b ≤ j
    ·
      rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_leₓ (hA _) hbj),
        coeff_eq_zero_of_degree_lt (lt_of_lt_of_leₓ (hA _) hbj)]
    rw [not_leₓ] at hbj 
    apply congr_funₓ i_eq.symm ⟨j, _⟩
    exact lt_of_lt_of_leₓ (coe_lt_degree.mp hbj) hb

/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that their difference has small degree. -/
theorem exists_approx_polynomial_aux {d : ℕ} {m : ℕ} (hm : (Fintype.card Fq^d) ≤ m) (b : Polynomial Fq)
  (A : Finₓ m.succ → Polynomial Fq) (hA : ∀ i, degree (A i) < degree b) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < «expr↑ » (nat_degree b - d) :=
  by 
    have hb : b ≠ 0
    ·
      rintro rfl 
      specialize hA 0
      rw [degree_zero] at hA 
      exact not_lt_of_le bot_le hA 
    set f : Finₓ m.succ → Finₓ d → Fq := fun i j => (A i).coeff (nat_degree b - j.succ)
    have  : Fintype.card (Finₓ d → Fq) < Fintype.card (Finₓ m.succ)
    ·
      simpa using lt_of_le_of_ltₓ hm (Nat.lt_succ_selfₓ m)
    obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this 
    use i₀, i₁, i_ne 
    refine' (degree_lt_iff_coeff_zero _ _).mpr fun j hj => _ 
    byCases' hbj : degree b ≤ j
    ·
      refine' coeff_eq_zero_of_degree_lt (lt_of_lt_of_leₓ _ hbj)
      exact lt_of_le_of_ltₓ (degree_sub_le _ _) (max_ltₓ (hA _) (hA _))
    rw [coeff_sub, sub_eq_zero]
    rw [not_leₓ, degree_eq_nat_degree hb, WithBot.coe_lt_coe] at hbj 
    have hj : nat_degree b - j.succ < d
    ·
      byCases' hd : nat_degree b < d
      ·
        exact lt_of_le_of_ltₓ tsub_le_self hd
      ·
        rw [not_ltₓ] at hd 
        have  := lt_of_le_of_ltₓ hj (Nat.lt_succ_selfₓ j)
        rwa [tsub_lt_iff_tsub_lt hd hbj] at this 
    have  : j = b.nat_degree - (nat_degree b - j.succ).succ
    ·
      rw [←Nat.succ_subₓ hbj, Nat.succ_sub_succ, tsub_tsub_cancel_of_le hbj.le]
    convert congr_funₓ i_eq.symm ⟨nat_degree b - j.succ, hj⟩

/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that the difference of their remainders is close together. -/
theorem exists_approx_polynomial {b : Polynomial Fq} (hb : b ≠ 0) {ε : ℝ} (hε : 0 < ε)
  (A : Finₓ (Fintype.card Fq^⌈-log ε / log (Fintype.card Fq)⌉₊).succ → Polynomial Fq) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ (card_pow_degree (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree b • ε :=
  by 
    have hbε : 0 < card_pow_degree b • ε
    ·
      rw [Algebra.smul_def, RingHom.eq_int_cast]
      exact mul_pos (int.cast_pos.mpr (AbsoluteValue.pos _ hb)) hε 
    have one_lt_q : 1 < Fintype.card Fq := Fintype.one_lt_card 
    have one_lt_q' : (1 : ℝ) < Fintype.card Fq
    ·
      assumptionModCast 
    have q_pos : 0 < Fintype.card Fq
    ·
      linarith 
    have q_pos' : (0 : ℝ) < Fintype.card Fq
    ·
      assumptionModCast 
    byCases' le_b : b.nat_degree ≤ ⌈-log ε / log (Fintype.card Fq)⌉₊
    ·
      obtain ⟨i₀, i₁, i_ne, mod_eq⟩ :=
        exists_eq_polynomial le_rfl b le_b (fun i => A i % b) fun i => EuclideanDomain.mod_lt (A i) hb 
      refine' ⟨i₀, i₁, i_ne, _⟩
      simp only  at mod_eq 
      rwa [mod_eq, sub_self, AbsoluteValue.map_zero, Int.cast_zero]
    rw [not_leₓ] at le_b 
    obtain ⟨i₀, i₁, i_ne, deg_lt⟩ :=
      exists_approx_polynomial_aux le_rfl b (fun i => A i % b) fun i => EuclideanDomain.mod_lt (A i) hb 
    simp only  at deg_lt 
    use i₀, i₁, i_ne 
    byCases' h : A i₁ % b = A i₀ % b
    ·
      rwa [h, sub_self, AbsoluteValue.map_zero, Int.cast_zero]
    have h' : A i₁ % b - A i₀ % b ≠ 0 := mt sub_eq_zero.mp h 
    suffices  : (nat_degree (A i₁ % b - A i₀ % b) : ℝ) < b.nat_degree+log ε / log (Fintype.card Fq)
    ·
      rwa [←Real.log_lt_log_iff (int.cast_pos.mpr (card_pow_degree.pos h')) hbε, card_pow_degree_nonzero _ h',
        card_pow_degree_nonzero _ hb, Algebra.smul_def, RingHom.eq_int_cast, Int.cast_pow, Int.cast_coe_nat,
        Int.cast_pow, Int.cast_coe_nat, log_mul (pow_ne_zero _ q_pos'.ne') hε.ne', ←rpow_nat_cast, ←rpow_nat_cast,
        log_rpow q_pos', log_rpow q_pos', ←lt_div_iff (log_pos one_lt_q'), add_div,
        mul_div_cancel _ (log_pos one_lt_q').ne']
    refine' lt_of_lt_of_leₓ (nat.cast_lt.mpr (with_bot.coe_lt_coe.mp _)) _ 
    swap
    ·
      convert deg_lt 
      rw [degree_eq_nat_degree h']
    rw [←sub_neg_eq_add, neg_div]
    refine' le_transₓ _ (sub_le_sub_left (Nat.le_ceil _) (b.nat_degree : ℝ))
    rw [←neg_div]
    exact le_of_eqₓ (Nat.cast_sub le_b.le)

/-- If `x` is close to `y` and `y` is close to `z`, then `x` and `z` are at least as close. -/
theorem card_pow_degree_anti_archimedean {x y z : Polynomial Fq} {a : ℤ} (hxy : card_pow_degree (x - y) < a)
  (hyz : card_pow_degree (y - z) < a) : card_pow_degree (x - z) < a :=
  by 
    have ha : 0 < a := lt_of_le_of_ltₓ (AbsoluteValue.nonneg _ _) hxy 
    byCases' hxy' : x = y
    ·
      rwa [hxy']
    byCases' hyz' : y = z
    ·
      rwa [←hyz']
    byCases' hxz' : x = z
    ·
      rwa [hxz', sub_self, AbsoluteValue.map_zero]
    rw [←Ne.def, ←sub_ne_zero] at hxy' hyz' hxz' 
    refine' lt_of_le_of_ltₓ _ (max_ltₓ hxy hyz)
    rw [card_pow_degree_nonzero _ hxz', card_pow_degree_nonzero _ hxy', card_pow_degree_nonzero _ hyz']
    have  : (1 : ℤ) ≤ Fintype.card Fq
    ·
      exactModCast (@Fintype.one_lt_card Fq _ _).le 
    simp only [Int.cast_pow, Int.cast_coe_nat, le_max_iff]
    refine' Or.imp (pow_le_pow this) (pow_le_pow this) _ 
    rw [nat_degree_le_iff_degree_le, nat_degree_le_iff_degree_le, ←le_max_iff, ←degree_eq_nat_degree hxy',
      ←degree_eq_nat_degree hyz']
    convert degree_add_le (x - y) (y - z) using 2 
    exact (sub_add_sub_cancel _ _ _).symm

-- error in NumberTheory.ClassNumber.AdmissibleCardPowDegree: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

