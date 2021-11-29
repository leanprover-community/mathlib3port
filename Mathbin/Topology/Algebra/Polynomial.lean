import Mathbin.Analysis.NormedSpace.Basic 
import Mathbin.Data.Polynomial.AlgebraMap 
import Mathbin.Data.Polynomial.Inductions

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `polynomial.continuous_eval₂: `polynomial.eval₂` defines a continuous function.
* `polynomial.continuous_aeval: `polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `polynomial.continuous_at_aeval`,
  `polynomial.continuous_within_at_aeval`, `polynomial.continuous_on_aeval`.
* `polynomial.continuous`:  `polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `polynomial.continuous_at`, `polynomial.continuous_within_at`,
  `polynomial.continuous_on`.
* `polynomial.tendsto_norm_at_top`: `λ x, ∥polynomial.eval (z x) p∥` tends to infinity provided that
  `λ x, ∥z x∥` tends to infinity and `0 < degree p`;
* `polynomial.tendsto_abv_eval₂_at_top`, `polynomial.tendsto_abv_at_top`,
  `polynomial.tendsto_abv_aeval_at_top`: a few versions of the previous statement for
  `is_absolute_value abv` instead of norm.

## Tags

polynomial, continuity
-/


open IsAbsoluteValue Filter

namespace Polynomial

section TopologicalRing

variable{R S : Type _}[Semiringₓ R][TopologicalSpace R][TopologicalRing R](p : Polynomial R)

@[continuity]
protected theorem continuous_eval₂ [Semiringₓ S] (p : Polynomial S) (f : S →+* R) : Continuous fun x => p.eval₂ f x :=
  by 
    dsimp only [eval₂_eq_sum, Finsupp.sum]
    exact continuous_finset_sum _ fun c hc => continuous_const.mul (continuous_pow _)

@[continuity]
protected theorem Continuous : Continuous fun x => p.eval x :=
  p.continuous_eval₂ _

protected theorem ContinuousAt {a : R} : ContinuousAt (fun x => p.eval x) a :=
  p.continuous.continuous_at

protected theorem ContinuousWithinAt {s a} : ContinuousWithinAt (fun x => p.eval x) s a :=
  p.continuous.continuous_within_at

protected theorem ContinuousOn {s} : ContinuousOn (fun x => p.eval x) s :=
  p.continuous.continuous_on

end TopologicalRing

section TopologicalAlgebra

variable{R A :
    Type _}[CommSemiringₓ R][Semiringₓ A][Algebra R A][TopologicalSpace A][TopologicalRing A](p : Polynomial R)

-- error in Topology.Algebra.Polynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[continuity #[]] protected theorem continuous_aeval : continuous (λ x : A, aeval x p) := p.continuous_eval₂ _

-- error in Topology.Algebra.Polynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected theorem continuous_at_aeval {a : A} : continuous_at (λ x : A, aeval x p) a := p.continuous_aeval.continuous_at

-- error in Topology.Algebra.Polynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected theorem continuous_within_at_aeval {s a} : continuous_within_at (λ x : A, aeval x p) s a :=
p.continuous_aeval.continuous_within_at

-- error in Topology.Algebra.Polynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected theorem continuous_on_aeval {s} : continuous_on (λ x : A, aeval x p) s := p.continuous_aeval.continuous_on

end TopologicalAlgebra

theorem tendsto_abv_eval₂_at_top {R S k α : Type _} [Semiringₓ R] [Ringₓ S] [LinearOrderedField k] (f : R →+* S)
  (abv : S → k) [IsAbsoluteValue abv] (p : Polynomial R) (hd : 0 < degree p) (hf : f p.leading_coeff ≠ 0) {l : Filter α}
  {z : α → S} (hz : tendsto (abv ∘ z) l at_top) : tendsto (fun x => abv (p.eval₂ f (z x))) l at_top :=
  by 
    revert hf 
    refine' degree_pos_induction_on p hd _ _ _ <;> clear hd p
    ·
      rintro c - hc 
      rw [leading_coeff_mul_X, leading_coeff_C] at hc 
      simpa [abv_mul abv] using hz.const_mul_at_top ((abv_pos abv).2 hc)
    ·
      intro p hpd ihp hf 
      rw [leading_coeff_mul_X] at hf 
      simpa [abv_mul abv] using (ihp hf).at_top_mul_at_top hz
    ·
      intro p a hd ihp hf 
      rw [add_commₓ, leading_coeff_add_of_degree_lt (degree_C_le.trans_lt hd)] at hf 
      refine' tendsto_at_top_of_add_const_right (abv (-f a)) _ 
      refine' tendsto_at_top_mono (fun _ => abv_add abv _ _) _ 
      simpa using ihp hf

theorem tendsto_abv_at_top {R k α : Type _} [Ringₓ R] [LinearOrderedField k] (abv : R → k) [IsAbsoluteValue abv]
  (p : Polynomial R) (h : 0 < degree p) {l : Filter α} {z : α → R} (hz : tendsto (abv ∘ z) l at_top) :
  tendsto (fun x => abv (p.eval (z x))) l at_top :=
  tendsto_abv_eval₂_at_top _ _ _ h (mt leading_coeff_eq_zero.1$ ne_zero_of_degree_gt h) hz

theorem tendsto_abv_aeval_at_top {R A k α : Type _} [CommSemiringₓ R] [Ringₓ A] [Algebra R A] [LinearOrderedField k]
  (abv : A → k) [IsAbsoluteValue abv] (p : Polynomial R) (hd : 0 < degree p) (h₀ : algebraMap R A p.leading_coeff ≠ 0)
  {l : Filter α} {z : α → A} (hz : tendsto (abv ∘ z) l at_top) : tendsto (fun x => abv (aeval (z x) p)) l at_top :=
  tendsto_abv_eval₂_at_top _ abv p hd h₀ hz

variable{α R : Type _}[NormedRing R][IsAbsoluteValue (norm : R → ℝ)]

theorem tendsto_norm_at_top (p : Polynomial R) (h : 0 < degree p) {l : Filter α} {z : α → R}
  (hz : tendsto (fun x => ∥z x∥) l at_top) : tendsto (fun x => ∥p.eval (z x)∥) l at_top :=
  p.tendsto_abv_at_top norm h hz

theorem exists_forall_norm_le [ProperSpace R] (p : Polynomial R) : ∃ x, ∀ y, ∥p.eval x∥ ≤ ∥p.eval y∥ :=
  if hp0 : 0 < degree p then p.continuous.norm.exists_forall_le$ p.tendsto_norm_at_top hp0 tendsto_norm_cocompact_at_top
  else
    ⟨p.coeff 0,
      by 
        rw [eq_C_of_degree_le_zero (le_of_not_gtₓ hp0)] <;> simp ⟩

end Polynomial

