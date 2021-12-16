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

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » «expr \ »(Icc a b, s))
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
theorem integral_divergence_of_has_fderiv_within_at_off_countable (hle : a ≤ b) (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
  (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : Set ℝⁿ⁺¹) (hs : countable s) (Hc : ∀ x _ : x ∈ s, ContinuousWithinAt f (Icc a b) x)
  (Hd : ∀ x _ : x ∈ Icc a b \ s, HasFderivWithinAt f (f' x) (Icc a b) x)
  (Hi : integrable_on (fun x => ∑ i, f' x (Pi.single i 1) i) (Icc a b)) :
  (∫ x in Icc a b, ∑ i, f' x (e i) i) =
    ∑ i : Finₓ (n+1), (∫ x in face i, f ((front_face(i)) x) i) - ∫ x in face i, f ((back_face(i)) x) i :=
  by 
    simp only [volume_pi, ←set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc]
    byCases' heq : ∃ i, a i = b i
    ·
      rcases HEq with ⟨i, hi⟩
      have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt 
      have  : (pi Set.Univ fun j => Ioc (a j) (b j)) = ∅
      exact univ_pi_eq_empty hi' 
      rw [this, integral_empty, sum_eq_zero]
      rintro j -
      rcases eq_or_ne i j with (rfl | hne)
      ·
        simp [hi]
      ·
        rcases Finₓ.exists_succ_above_eq hne with ⟨i, rfl⟩
        have  : (pi Set.Univ fun k : Finₓ n => Ioc (a$ j.succ_above k) (b$ j.succ_above k)) = ∅
        exact univ_pi_eq_empty hi' 
        rw [this, integral_empty, integral_empty, sub_self]
    ·
      pushNeg  at heq 
      obtain ⟨I, rfl, rfl⟩ : ∃ I : BoxIntegral.Box (Finₓ (n+1)), I.lower = a ∧ I.upper = b 
      exact ⟨⟨a, b, fun i => (hle i).lt_of_ne (HEq i)⟩, rfl, rfl⟩
      simp only [←box.coe_eq_pi, ←box.face_lower, ←box.face_upper]
      have A := (Hi.mono_set box.coe_subset_Icc).has_box_integral ⊥ rfl 
      have B := has_integral_bot_divergence_of_forall_has_deriv_within_at I f f' s hs Hc Hd 
      have Hc : ContinuousOn f I.Icc
      ·
        intro x hx 
        byCases' hxs : x ∈ s 
        exacts[Hc x hxs, (Hd x ⟨hx, hxs⟩).ContinuousWithinAt]
      rw [continuous_on_pi] at Hc 
      refine' (A.unique B).trans (sum_congr rfl$ fun i hi => _)
      refine' congr_arg2ₓ Sub.sub _ _
      ·
        have  := box.continuous_on_face_Icc (Hc i) (Set.right_mem_Icc.2 (hle i))
        have  := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc 
        exact (this.has_box_integral ⊥ rfl).integral_eq 
        infer_instance
      ·
        have  := box.continuous_on_face_Icc (Hc i) (Set.left_mem_Icc.2 (hle i))
        have  := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc 
        exact (this.has_box_integral ⊥ rfl).integral_eq 
        infer_instance

end 

end MeasureTheory

