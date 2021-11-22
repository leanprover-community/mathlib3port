import Mathbin.MeasureTheory.Function.ConditionalExpectation 
import Mathbin.MeasureTheory.Decomposition.RadonNikodym

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|hm]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|hm]` for a measure `P` is defined in
  measure_theory.function.conditional_expectation.
- `X =ₐₛ Y`: `X =ᵐ[volume] Y`
- `X ≤ₐₛ Y`: `X ≤ᵐ[volume] Y`
- `∂P/∂Q = P.rn_deriv Q`
We note that the notation `∂P/∂Q` applies to three different cases, namely,
`measure_theory.measure.rn_deriv`, `measure_theory.signed_measure.rn_deriv` and
`measure_theory.complex_measure.rn_deriv`.

TODO: define the notation `ℙ s` for the probability of a set `s`, and decide whether it should be a
value in `ℝ`, `ℝ≥0` or `ℝ≥0∞`.
-/


open MeasureTheory

localized [ProbabilityTheory] notation "𝔼[" X "|" hm "]" => MeasureTheory.condexp hm MeasureTheory.Measure.volume X

localized [ProbabilityTheory] notation P "[" X "]" => ∫x, X x ∂P

localized [ProbabilityTheory] notation "𝔼[" X "]" => ∫a, X a

localized [ProbabilityTheory] notation:50 X "=ₐₛ" Y:50 => X =ᵐ[MeasureTheory.Measure.volume] Y

localized [ProbabilityTheory] notation:50 X "≤ₐₛ" Y:50 => X ≤ᵐ[MeasureTheory.Measure.volume] Y

localized [ProbabilityTheory] notation "∂" P "/∂" Q:50 => P.rn_deriv Q

