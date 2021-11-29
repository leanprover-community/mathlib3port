import Mathbin.Analysis.SpecialFunctions.Exp 
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# The circle

This file defines `circle` to be the metric sphere (`metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `exp_map_circle` to be the natural map `λ t, exp (t * I)` from `ℝ` to
`circle`, and show that this map is a group homomorphism.

## Implementation notes

Because later (in `geometry.manifold.instances.sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | norm_sq z = 1}`, which
is the kernel of the homomorphism `complex.norm_sq` from `ℂ` to `ℝ`.

-/


noncomputable theory

open Complex Metric

open_locale ComplexConjugate

/-- The unit circle in `ℂ`, here given the structure of a submonoid of `ℂ`. -/
def circle : Submonoid ℂ :=
  { Carrier := sphere (0 : ℂ) 1,
    one_mem' :=
      by 
        simp ,
    mul_mem' :=
      fun a b =>
        by 
          simp only [norm_eq_abs, mem_sphere_zero_iff_norm]
          intro ha hb 
          simp [ha, hb] }

@[simp]
theorem mem_circle_iff_abs (z : ℂ) : z ∈ circle ↔ abs z = 1 :=
  mem_sphere_zero_iff_norm

theorem circle_def : «expr↑ » circle = { z:ℂ | abs z = 1 } :=
  by 
    ext 
    simp 

@[simp]
theorem abs_eq_of_mem_circle (z : circle) : abs z = 1 :=
  by 
    convert z.2
    simp 

@[simp]
theorem norm_sq_eq_of_mem_circle (z : circle) : norm_sq z = 1 :=
  by 
    simp [norm_sq_eq_abs]

theorem nonzero_of_mem_circle (z : circle) : (z : ℂ) ≠ 0 :=
  nonzero_of_mem_unit_sphere z

instance  : Groupₓ circle :=
  { circle.toMonoid with
    inv :=
      fun z =>
        ⟨conj (z : ℂ),
          by 
            simp ⟩,
    mul_left_inv :=
      fun z =>
        Subtype.ext$
          by 
            simp [HasInv.inv, ←norm_sq_eq_conj_mul_self, ←mul_self_abs] }

theorem coe_inv_circle_eq_conj (z : circle) : «expr↑ » (z⁻¹) = (conj : RingAut ℂ) z :=
  rfl

@[simp]
theorem coe_inv_circle (z : circle) : «expr↑ » (z⁻¹) = (z : ℂ)⁻¹ :=
  by 
    rw [coe_inv_circle_eq_conj]
    apply eq_inv_of_mul_right_eq_one 
    rw [mul_commₓ, ←Complex.norm_sq_eq_conj_mul_self]
    simp 

@[simp]
theorem coe_div_circle (z w : circle) : «expr↑ » (z / w) = (z : ℂ) / w :=
  show «expr↑ » (z*w⁻¹) = (z : ℂ)*w⁻¹by 
    simp 

instance  : CompactSpace circle :=
  Metric.Sphere.compact_space _ _

-- error in Analysis.Complex.Circle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance : topological_group circle :=
{ continuous_mul := let h : continuous (λ x : circle, (x : exprℂ())) := continuous_subtype_coe in
  continuous_induced_rng (continuous_mul.comp (h.prod_map h)),
  continuous_inv := «expr $ »(continuous_induced_rng, complex.conj_cle.continuous.comp continuous_subtype_coe) }

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def expMapCircle : C(ℝ, circle) :=
  { toFun :=
      fun t =>
        ⟨exp (t*I),
          by 
            simp [exp_mul_I, abs_cos_add_sin_mul_I]⟩ }

@[simp]
theorem exp_map_circle_apply (t : ℝ) : «expr↑ » (expMapCircle t) = Complex.exp (t*Complex.i) :=
  rfl

@[simp]
theorem exp_map_circle_zero : expMapCircle 0 = 1 :=
  Subtype.ext$
    by 
      rw [exp_map_circle_apply, of_real_zero, zero_mul, exp_zero, Submonoid.coe_one]

@[simp]
theorem exp_map_circle_add (x y : ℝ) : expMapCircle (x+y) = expMapCircle x*expMapCircle y :=
  Subtype.ext$
    by 
      simp only [exp_map_circle_apply, Submonoid.coe_mul, of_real_add, add_mulₓ, Complex.exp_add]

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`, considered as a homomorphism of
groups. -/
def expMapCircleHom : ℝ →+ Additive circle :=
  { toFun := Additive.ofMul ∘ expMapCircle, map_zero' := exp_map_circle_zero, map_add' := exp_map_circle_add }

@[simp]
theorem exp_map_circle_sub (x y : ℝ) : expMapCircle (x - y) = expMapCircle x / expMapCircle y :=
  expMapCircleHom.map_sub x y

