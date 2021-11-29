import Mathbin.Analysis.BoxIntegral.DivergenceTheorem 
import Mathbin.Analysis.BoxIntegral.Integrability

/-!
# Divergence theorem for Bochner integral

In this file we prove the Divergence theorem for Bochner integral on a box in
`ℝⁿ⁺¹ = fin (n + 1) → ℝ`. More precisely, we prove the following theorem.

Let `E` be a complete normed space with second countably topology. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is
differentiable on a rectangular box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, with derivative
`f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the divergence `λ x, ∑ i, f' x eᵢ i` is integrable on `[a, b]`,
where `eᵢ = pi.single i 1` is the `i`-th basis vector, then its integral is equal to the sum of
integrals of `f` over the faces of `[a, b]`, taken with appropriat signs. Moreover, the same is true
if the function is not differentiable but continuous at countably many points of `[a, b]`.

## Notations

We use the following local notation to make the statement more readable. Note that the documentation
website shows the actual terms, not those abbreviated using local notations.

* `ℝⁿ`, `ℝⁿ⁺¹`, `Eⁿ⁺¹`: `fin n → ℝ`, `fin (n + 1) → ℝ`, `fin (n + 1) → E`;
* `face i`: the `i`-th face of the box `[a, b]` as a closed segment in `ℝⁿ`, namely `[a ∘
  fin.succ_above i, b ∘ fin.succ_above i]`;
* `e i` : `i`-th basis vector `pi.single i 1`;
* `front_face i`, `back_face i`: embeddings `ℝⁿ → ℝⁿ⁺¹` corresponding to the front face
  `{x | x i = b i}` and back face `{x | x i = a i}` of the box `[a, b]`, respectively.
  They are given by `fin.insert_nth i (b i)` and `fin.insert_nth i (a i)`.

## TODO

* Deduce corollaries about integrals in `ℝ × ℝ` and interval integral.
* Add a version that assumes existence and integrability of partial derivatives.

## Tags

divergence theorem, Bochner integral
-/


open Set Finset TopologicalSpace Function BoxIntegral

open_locale BigOperators Classical

namespace MeasureTheory

universe u

variable {E : Type u} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [second_countable_topology E]
  [CompleteSpace E]

section 

variable {n : ℕ}

local notation "ℝⁿ" => Finₓ n → ℝ

local notation "ℝⁿ⁺¹" => Finₓ (n+1) → ℝ

local notation "Eⁿ⁺¹" => Finₓ (n+1) → E

variable (a b : ℝⁿ⁺¹)

local notation "face" i => Set.Icc (a ∘ Finₓ.succAbove i) (b ∘ Finₓ.succAbove i)

local notation "e" i => Pi.single i 1

local notation "front_face" i:2000 => Finₓ.insertNth i (b i)

local notation "back_face" i:2000 => Finₓ.insertNth i (a i)

-- error in MeasureTheory.Integral.DivergenceTheorem: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Divergence theorem** for Bochner integral. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is differentiable on a
rectangular box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, with derivative `f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the
divergence `λ x, ∑ i, f' x eᵢ i` is integrable on `[a, b]`, where `eᵢ = pi.single i 1` is the `i`-th
basis vector, then its integral is equal to the sum of integrals of `f` over the faces of `[a, b]`,
taken with appropriat signs.

Moreover, the same is true if the function is not differentiable but continuous at countably many
points of `[a, b]`.

We represent both faces `x i = a i` and `x i = b i` as the box
`face i = [a ∘ fin.succ_above i, b ∘ fin.succ_above i]` in `ℝⁿ`, where
`fin.succ_above : fin n ↪o fin (n + 1)` is the order embedding with range `{i}ᶜ`. The restrictions
of `f : ℝⁿ⁺¹ → Eⁿ⁺¹` to these faces are given by `f ∘ back_face i` and `f ∘ front_face i`, where
`back_face i = fin.insert_nth i (a i)` and `front_face i = fin.insert_nth i (b i)` are embeddings
`ℝⁿ → ℝⁿ⁺¹` that take `y : ℝⁿ` and insert `a i` (resp., `b i`) as `i`-th coordinate. -/
theorem integral_divergence_of_has_fderiv_within_at_off_countable
(hle : «expr ≤ »(a, b))
(f : «exprℝⁿ⁺¹»() → «exprEⁿ⁺¹»())
(f' : «exprℝⁿ⁺¹»() → «expr →L[ ] »(«exprℝⁿ⁺¹»(), exprℝ(), «exprEⁿ⁺¹»()))
(s : set «exprℝⁿ⁺¹»())
(hs : countable s)
(Hc : ∀ x «expr ∈ » s, continuous_within_at f (Icc a b) x)
(Hd : ∀ x «expr ∈ » «expr \ »(Icc a b, s), has_fderiv_within_at f (f' x) (Icc a b) x)
(Hi : integrable_on (λ
  x, «expr∑ , »((i), f' x (pi.single i 1) i)) (Icc a b)) : «expr = »(«expr∫ in , »((x), Icc a b, «expr∑ , »((i), f' x «expre »(i) i)), «expr∑ , »((i : fin «expr + »(n, 1)), «expr - »(«expr∫ in , »((x), «exprface »(i), f («exprfront_face »(i) x) i), «expr∫ in , »((x), «exprface »(i), f («exprback_face »(i) x) i)))) :=
begin
  simp [] [] ["only"] ["[", expr volume_pi, ",", "<-", expr set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc, "]"] [] [],
  by_cases [expr heq, ":", expr «expr∃ , »((i), «expr = »(a i, b i))],
  { rcases [expr heq, "with", "⟨", ident i, ",", ident hi, "⟩"],
    have [ident hi'] [":", expr «expr = »(Ioc (a i) (b i), «expr∅»())] [":=", expr Ioc_eq_empty hi.not_lt],
    have [] [":", expr «expr = »(pi set.univ (λ j, Ioc (a j) (b j)), «expr∅»())] [],
    from [expr univ_pi_eq_empty hi'],
    rw ["[", expr this, ",", expr integral_empty, ",", expr sum_eq_zero, "]"] [],
    rintro [ident j, "-"],
    rcases [expr eq_or_ne i j, "with", ident rfl, "|", ident hne],
    { simp [] [] [] ["[", expr hi, "]"] [] [] },
    { rcases [expr fin.exists_succ_above_eq hne, "with", "⟨", ident i, ",", ident rfl, "⟩"],
      have [] [":", expr «expr = »(pi set.univ (λ
         k : fin n, Ioc «expr $ »(a, j.succ_above k) «expr $ »(b, j.succ_above k)), «expr∅»())] [],
      from [expr univ_pi_eq_empty hi'],
      rw ["[", expr this, ",", expr integral_empty, ",", expr integral_empty, ",", expr sub_self, "]"] [] } },
  { push_neg ["at", ident heq],
    obtain ["⟨", ident I, ",", ident rfl, ",", ident rfl, "⟩", ":", expr «expr∃ , »((I : box_integral.box (fin «expr + »(n, 1))), «expr ∧ »(«expr = »(I.lower, a), «expr = »(I.upper, b)))],
    from [expr ⟨⟨a, b, λ i, (hle i).lt_of_ne (heq i)⟩, rfl, rfl⟩],
    simp [] [] ["only"] ["[", "<-", expr box.coe_eq_pi, ",", "<-", expr box.face_lower, ",", "<-", expr box.face_upper, "]"] [] [],
    have [ident A] [] [":=", expr (Hi.mono_set box.coe_subset_Icc).has_box_integral «expr⊥»() rfl],
    have [ident B] [] [":=", expr has_integral_bot_divergence_of_forall_has_deriv_within_at I f f' s hs Hc Hd],
    have [ident Hc] [":", expr continuous_on f I.Icc] [],
    { intros [ident x, ident hx],
      by_cases [expr hxs, ":", expr «expr ∈ »(x, s)],
      exacts ["[", expr Hc x hxs, ",", expr (Hd x ⟨hx, hxs⟩).continuous_within_at, "]"] },
    rw [expr continuous_on_pi] ["at", ident Hc],
    refine [expr (A.unique B).trans «expr $ »(sum_congr rfl, λ i hi, _)],
    refine [expr congr_arg2 has_sub.sub _ _],
    { have [] [] [":=", expr box.continuous_on_face_Icc (Hc i) (set.right_mem_Icc.2 (hle i))],
      have [] [] [":=", expr (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc],
      exact [expr (this.has_box_integral «expr⊥»() rfl).integral_eq],
      apply_instance },
    { have [] [] [":=", expr box.continuous_on_face_Icc (Hc i) (set.left_mem_Icc.2 (hle i))],
      have [] [] [":=", expr (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc],
      exact [expr (this.has_box_integral «expr⊥»() rfl).integral_eq],
      apply_instance } }
end

end 

end MeasureTheory

