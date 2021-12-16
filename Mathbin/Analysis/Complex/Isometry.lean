import Mathbin.Analysis.Complex.Circle

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `linear_isometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/


noncomputable section 

open Complex

open_locale ComplexConjugate

local notation "|" x "|" => Complex.abs x

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. This is an auxiliary construction; use `rotation`, which has more structure, by
preference. -/
def rotationAux (a : circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  { toFun := fun z => a*z, map_add' := mul_addₓ (↑a),
    map_smul' :=
      fun t z =>
        by 
          simp only [real_smul, RingHom.id_apply]
          ring,
    invFun := fun z => a⁻¹*z,
    left_inv :=
      fun z =>
        by 
          fieldSimp [nonzero_of_mem_circle]
          ring,
    right_inv :=
      fun z =>
        by 
          fieldSimp [nonzero_of_mem_circle]
          ring,
    norm_map' :=
      by 
        simp  }

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. -/
def rotation : circle →* ℂ ≃ₗᵢ[ℝ] ℂ :=
  { toFun := rotationAux,
    map_one' :=
      by 
        ext1 
        simp [rotationAux],
    map_mul' :=
      fun a b =>
        by 
          ext1 
          simp [rotationAux] }

@[simp]
theorem rotation_apply (a : circle) (z : ℂ) : rotation a z = a*z :=
  rfl

theorem LinearIsometryEquiv.congr_fun {R E F} [Semiringₓ R] [SemiNormedGroup E] [SemiNormedGroup F] [Module R E]
  [Module R F] {f g : E ≃ₗᵢ[R] F} (h : f = g) (x : E) : f x = g x :=
  congr_argₓ _ h

theorem rotation_ne_conj_lie (a : circle) : rotation a ≠ conj_lie :=
  by 
    intro h 
    have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
    have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I 
    rw [rotation_apply, RingEquiv.map_one, mul_oneₓ] at h1 
    rw [rotation_apply, conj_I, ←neg_one_mul, mul_left_inj' I_ne_zero, h1, eq_neg_self_iff] at hI 
    exact one_ne_zero hI

/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
def rotationOf (e : ℂ ≃ₗᵢ[ℝ] ℂ) : circle :=
  ⟨e 1 / Complex.abs (e 1),
    by 
      simp ⟩

@[simp]
theorem rotation_of_rotation (a : circle) : rotationOf (rotation a) = a :=
  Subtype.ext$
    by 
      simp 

theorem rotation_injective : Function.Injective rotation :=
  Function.LeftInverse.injective rotation_of_rotation

theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ) (h₃ : ∀ z, (z+conj z) = f z+conj (f z)) (z : ℂ) :
  (f z).re = z.re :=
  by 
    simpa [ext_iff, add_re, add_im, conj_re, conj_im, ←two_mul,
      show (2 : ℝ) ≠ 0 by 
        simp [two_ne_zero']] using
      (h₃ z).symm

theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) :
  (f z).im = z.im ∨ (f z).im = -z.im :=
  by 
    have h₁ := f.norm_map z 
    simp only [Complex.abs, norm_eq_abs] at h₁ 
    rwa [Real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z, h₂,
      add_left_cancel_iffₓ, mul_self_eq_mul_self_iff] at h₁

theorem LinearIsometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (z+conj z) = f z+conj (f z) :=
  by 
    have  : ∥f z - 1∥ = ∥z - 1∥ :=
      by 
        rw [←f.norm_map (z - 1), f.map_sub, h]
    applyFun fun x => x^2  at this 
    simp only [norm_eq_abs, ←norm_sq_eq_abs] at this 
    rw [←of_real_inj, ←mul_conj, ←mul_conj] at this 
    rw [RingEquiv.map_sub, RingEquiv.map_sub] at this 
    simp only [sub_mul, mul_sub, one_mulₓ, mul_oneₓ] at this 
    rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs, LinearIsometry.norm_map] at this 
    rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs] at this 
    simp only [sub_sub, sub_right_inj, mul_oneₓ, of_real_pow, RingEquiv.map_one, norm_eq_abs] at this 
    simp only [add_sub, sub_left_inj] at this 
    rw [add_commₓ, ←this, add_commₓ]

theorem LinearIsometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re :=
  by 
    apply LinearIsometry.re_apply_eq_re_of_add_conj_eq 
    intro z 
    apply LinearIsometry.im_apply_eq_im h

theorem linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) : f = LinearIsometryEquiv.refl ℝ ℂ ∨ f = conj_lie :=
  by 
    have h0 : f I = I ∨ f I = -I
    ·
      have  : |f I| = 1 :=
        by 
          simpa using f.norm_map Complex.i 
      simp only [ext_iff, ←and_or_distrib_left, neg_re, I_re, neg_im, neg_zero]
      constructor
      ·
        rw [←I_re]
        exact @LinearIsometry.re_apply_eq_re f.to_linear_isometry h I
      ·
        apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.to_linear_isometry 
        intro z 
        rw [@LinearIsometry.re_apply_eq_re f.to_linear_isometry h]
    refine' h0.imp (fun h' : f I = I => _) fun h' : f I = -I => _ <;>
      ·
        apply LinearIsometryEquiv.to_linear_equiv_injective 
        apply complex.basis_one_I.ext' 
        intro i 
        finCases i <;> simp [h, h']

theorem linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) : ∃ a : circle, f = rotation a ∨ f = conj_lie.trans (rotation a) :=
  by 
    let a : circle :=
      ⟨f 1,
        by 
          simpa using f.norm_map 1⟩
    use a 
    have  : (f.trans (rotation a).symm) 1 = 1
    ·
      simpa using rotation_apply (a⁻¹) (f 1)
    refine' (linear_isometry_complex_aux this).imp (fun h₁ => _) fun h₂ => _
    ·
      simpa using eq_mul_of_inv_mul_eq h₁
    ·
      exact eq_mul_of_inv_mul_eq h₂

