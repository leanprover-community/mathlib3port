import Mathbin.Data.Fin.Tuple 
import Mathbin.Data.Real.Basic 
import Mathbin.Combinatorics.Pigeonhole 
import Mathbin.Algebra.Order.EuclideanAbsoluteValue

/-!
# Admissible absolute values
This file defines a structure `absolute_value.is_admissible` which we use to show the class number
of the ring of integers of a global field is finite.

## Main definitions

 * `absolute_value.is_admissible abv` states the absolute value `abv : R → ℤ`
   respects the Euclidean domain structure on `R`, and that a large enough set
   of elements of `R^n` contains a pair of elements whose remainders are
   pointwise close together.

## Main results

 * `absolute_value.abs_is_admissible` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is admissible.
 * `polynomial.card_pow_degree_is_admissible` shows `card_pow_degree`,
   mapping `p : polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/


local infixl:50 " ≺ " => EuclideanDomain.R

namespace AbsoluteValue

variable {R : Type _} [EuclideanDomain R]

variable (abv : AbsoluteValue R ℤ)

/-- An absolute value `R → ℤ` is admissible if it respects the Euclidean domain
structure and a large enough set of elements in `R^n` will contain a pair of
elements whose remainders are pointwise close together. -/
structure is_admissible extends is_euclidean abv where 
  card : ℝ → ℕ 
  exists_partition' :
  ∀ n : ℕ {ε : ℝ} hε : 0 < ε {b : R} hb : b ≠ 0 A : Finₓ n → R,
    ∃ t : Finₓ n → Finₓ (card ε), ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε

attribute [protected] is_admissible.card

namespace IsAdmissible

variable {abv}

/-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
theorem exists_partition {ι : Type _} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0) (A : ι → R)
  (h : abv.is_admissible) :
  ∃ t : ι → Finₓ (h.card ε), ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε :=
  by 
    let e := Fintype.equivFin ι 
    obtain ⟨t, ht⟩ := h.exists_partition' (Fintype.card ι) hε hb (A ∘ e.symm)
    refine' ⟨t ∘ e, fun i₀ i₁ h => _⟩
    convert ht (e i₀) (e i₁) h <;> simp only [e.symm_apply_apply]

-- error in NumberTheory.ClassNumber.AdmissibleAbsoluteValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise. -/
theorem exists_approx_aux
(n : exprℕ())
(h : abv.is_admissible) : ∀
{ε : exprℝ()}
(hε : «expr < »(0, ε))
{b : R}
(hb : «expr ≠ »(b, 0))
(A : fin «expr ^ »(h.card ε, n).succ → fin n → R), «expr∃ , »((i₀
  i₁), «expr ∧ »(«expr ≠ »(i₀, i₁), ∀
  k, «expr < »((abv «expr - »(«expr % »(A i₁ k, b), «expr % »(A i₀ k, b)) : exprℝ()), «expr • »(abv b, ε)))) :=
begin
  haveI [] [] [":=", expr classical.dec_eq R],
  induction [expr n] [] ["with", ident n, ident ih] [],
  { intros [ident ε, ident hε, ident b, ident hb, ident A],
    refine [expr ⟨0, 1, _, _⟩],
    { simp [] [] [] [] [] [] },
    rintros ["⟨", ident i, ",", "⟨", "⟩", "⟩"] },
  intros [ident ε, ident hε, ident b, ident hb, ident A],
  set [] [ident M] [] [":="] [expr h.card ε] ["with", ident hM],
  obtain ["⟨", ident s, ",", ident s_inj, ",", ident hs, "⟩", ":", expr «expr∃ , »((s : fin «expr ^ »(M, n).succ → fin «expr ^ »(M, n.succ).succ), «expr ∧ »(function.injective s, ∀
     i₀
     i₁, «expr < »((abv «expr - »(«expr % »(A (s i₁) 0, b), «expr % »(A (s i₀) 0, b)) : exprℝ()), «expr • »(abv b, ε))))],
  { obtain ["⟨", ident t, ",", ident ht, "⟩", ":", expr «expr∃ , »((t : fin «expr ^ »(M, n.succ).succ → fin M), ∀
      i₀
      i₁, «expr = »(t i₀, t i₁) → «expr < »((abv «expr - »(«expr % »(A i₁ 0, b), «expr % »(A i₀ 0, b)) : exprℝ()), «expr • »(abv b, ε))), ":=", expr h.exists_partition hε hb (λ
      x, A x 0)],
    obtain ["⟨", ident s, ",", ident hs, "⟩", ":=", expr @fintype.exists_lt_card_fiber_of_mul_lt_card _ _ _ _ _ t «expr ^ »(M, n) (by simpa [] [] ["only"] ["[", expr fintype.card_fin, ",", expr pow_succ, "]"] [] ["using", expr nat.lt_succ_self «expr ^ »(M, n.succ)])],
    refine [expr ⟨λ i, (finset.univ.filter (λ x, «expr = »(t x, s))).to_list.nth_le i _, _, λ i₀ i₁, ht _ _ _⟩],
    { refine [expr i.2.trans_le _],
      rwa [expr finset.length_to_list] [] },
    { intros [ident i, ident j, ident h],
      ext [] [] [],
      exact [expr list.nodup_iff_nth_le_inj.mp (finset.nodup_to_list _) _ _ _ _ h] },
    have [] [":", expr ∀
     i
     h, «expr ∈ »((finset.univ.filter (λ
        x, «expr = »(t x, s))).to_list.nth_le i h, finset.univ.filter (λ x, «expr = »(t x, s)))] [],
    { intros [ident i, ident h],
      exact [expr (finset.mem_to_list _).mp (list.nth_le_mem _ _ _)] },
    obtain ["⟨", "_", ",", ident h₀, "⟩", ":=", expr finset.mem_filter.mp (this i₀ _)],
    obtain ["⟨", "_", ",", ident h₁, "⟩", ":=", expr finset.mem_filter.mp (this i₁ _)],
    exact [expr h₀.trans h₁.symm] },
  obtain ["⟨", ident k₀, ",", ident k₁, ",", ident hk, ",", ident h, "⟩", ":=", expr ih hε hb (λ
    x, fin.tail (A (s x)))],
  refine [expr ⟨s k₀, s k₁, λ h, hk (s_inj h), λ i, fin.cases _ (λ i, _) i⟩],
  { exact [expr hs k₀ k₁] },
  { exact [expr h i] }
end

/-- Any large enough family of vectors in `R^ι` has a pair of elements
whose remainders are close together, pointwise. -/
theorem exists_approx {ι : Type _} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0) (h : abv.is_admissible)
  (A : Finₓ (h.card ε ^ Fintype.card ι).succ → ι → R) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε :=
  by 
    let e := Fintype.equivFin ι 
    obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y => A x (e.symm y)
    refine' ⟨i₀, i₁, Ne, fun k => _⟩
    convert h (e k) <;> simp only [e.symm_apply_apply]

end IsAdmissible

end AbsoluteValue

