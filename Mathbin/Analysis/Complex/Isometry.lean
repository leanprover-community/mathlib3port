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


noncomputable theory

open Complex

open_locale ComplexConjugate

local notation "|" x "|" => Complex.abs x

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. This is an auxiliary construction; use `rotation`, which has more structure, by
preference. -/
def rotationAux (a : circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  { toFun := fun z => a*z, map_add' := mul_addₓ («expr↑ » a),
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

-- error in Analysis.Complex.Isometry: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rotation_ne_conj_lie (a : circle) : «expr ≠ »(rotation a, conj_lie) :=
begin
  intro [ident h],
  have [ident h1] [":", expr «expr = »(rotation a 1, exprconj() 1)] [":=", expr linear_isometry_equiv.congr_fun h 1],
  have [ident hI] [":", expr «expr = »(rotation a I, exprconj() I)] [":=", expr linear_isometry_equiv.congr_fun h I],
  rw ["[", expr rotation_apply, ",", expr ring_equiv.map_one, ",", expr mul_one, "]"] ["at", ident h1],
  rw ["[", expr rotation_apply, ",", expr conj_I, ",", "<-", expr neg_one_mul, ",", expr mul_left_inj' I_ne_zero, ",", expr h1, ",", expr eq_neg_self_iff, "]"] ["at", ident hI],
  exact [expr one_ne_zero hI]
end

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

-- error in Analysis.Complex.Isometry: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re
{f : «expr →ₗᵢ[ ] »(exprℂ(), exprℝ(), exprℂ())}
(h₂ : ∀ z, «expr = »((f z).re, z.re))
(z : exprℂ()) : «expr ∨ »(«expr = »((f z).im, z.im), «expr = »((f z).im, «expr- »(z.im))) :=
begin
  have [ident h₁] [] [":=", expr f.norm_map z],
  simp [] [] ["only"] ["[", expr complex.abs, ",", expr norm_eq_abs, "]"] [] ["at", ident h₁],
  rwa ["[", expr real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), ",", expr norm_sq_apply (f z), ",", expr norm_sq_apply z, ",", expr h₂, ",", expr add_left_cancel_iff, ",", expr mul_self_eq_mul_self_iff, "]"] ["at", ident h₁]
end

-- error in Analysis.Complex.Isometry: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_isometry.im_apply_eq_im
{f : «expr →ₗᵢ[ ] »(exprℂ(), exprℝ(), exprℂ())}
(h : «expr = »(f 1, 1))
(z : exprℂ()) : «expr = »(«expr + »(z, exprconj() z), «expr + »(f z, exprconj() (f z))) :=
begin
  have [] [":", expr «expr = »(«expr∥ ∥»(«expr - »(f z, 1)), «expr∥ ∥»(«expr - »(z, 1)))] [":=", expr by rw ["[", "<-", expr f.norm_map «expr - »(z, 1), ",", expr f.map_sub, ",", expr h, "]"] []],
  apply_fun [expr λ x, «expr ^ »(x, 2)] ["at", ident this] [],
  simp [] [] ["only"] ["[", expr norm_eq_abs, ",", "<-", expr norm_sq_eq_abs, "]"] [] ["at", ident this],
  rw ["[", "<-", expr of_real_inj, ",", "<-", expr mul_conj, ",", "<-", expr mul_conj, "]"] ["at", ident this],
  rw ["[", expr ring_equiv.map_sub, ",", expr ring_equiv.map_sub, "]"] ["at", ident this],
  simp [] [] ["only"] ["[", expr sub_mul, ",", expr mul_sub, ",", expr one_mul, ",", expr mul_one, "]"] [] ["at", ident this],
  rw ["[", expr mul_conj, ",", expr norm_sq_eq_abs, ",", "<-", expr norm_eq_abs, ",", expr linear_isometry.norm_map, "]"] ["at", ident this],
  rw ["[", expr mul_conj, ",", expr norm_sq_eq_abs, ",", "<-", expr norm_eq_abs, "]"] ["at", ident this],
  simp [] [] ["only"] ["[", expr sub_sub, ",", expr sub_right_inj, ",", expr mul_one, ",", expr of_real_pow, ",", expr ring_equiv.map_one, ",", expr norm_eq_abs, "]"] [] ["at", ident this],
  simp [] [] ["only"] ["[", expr add_sub, ",", expr sub_left_inj, "]"] [] ["at", ident this],
  rw ["[", expr add_comm, ",", "<-", expr this, ",", expr add_comm, "]"] []
end

theorem LinearIsometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re :=
  by 
    apply LinearIsometry.re_apply_eq_re_of_add_conj_eq 
    intro z 
    apply LinearIsometry.im_apply_eq_im h

-- error in Analysis.Complex.Isometry: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_isometry_complex_aux
{f : «expr ≃ₗᵢ[ ] »(exprℂ(), exprℝ(), exprℂ())}
(h : «expr = »(f 1, 1)) : «expr ∨ »(«expr = »(f, linear_isometry_equiv.refl exprℝ() exprℂ()), «expr = »(f, conj_lie)) :=
begin
  have [ident h0] [":", expr «expr ∨ »(«expr = »(f I, I), «expr = »(f I, «expr- »(I)))] [],
  { have [] [":", expr «expr = »(«expr| |»(f I), 1)] [":=", expr by simpa [] [] [] [] [] ["using", expr f.norm_map complex.I]],
    simp [] [] ["only"] ["[", expr ext_iff, ",", "<-", expr and_or_distrib_left, ",", expr neg_re, ",", expr I_re, ",", expr neg_im, ",", expr neg_zero, "]"] [] [],
    split,
    { rw ["<-", expr I_re] [],
      exact [expr @linear_isometry.re_apply_eq_re f.to_linear_isometry h I] },
    { apply [expr @linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.to_linear_isometry],
      intro [ident z],
      rw [expr @linear_isometry.re_apply_eq_re f.to_linear_isometry h] [] } },
  refine [expr h0.imp (λ
    h' : «expr = »(f I, I), _) (λ
    h' : «expr = »(f I, «expr- »(I)), _)]; { apply [expr linear_isometry_equiv.to_linear_equiv_injective],
    apply [expr complex.basis_one_I.ext'],
    intros [ident i],
    fin_cases [ident i] []; simp [] [] [] ["[", expr h, ",", expr h', "]"] [] [] }
end

-- error in Analysis.Complex.Isometry: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_isometry_complex
(f : «expr ≃ₗᵢ[ ] »(exprℂ(), exprℝ(), exprℂ())) : «expr∃ , »((a : circle), «expr ∨ »(«expr = »(f, rotation a), «expr = »(f, conj_lie.trans (rotation a)))) :=
begin
  let [ident a] [":", expr circle] [":=", expr ⟨f 1, by simpa [] [] [] [] [] ["using", expr f.norm_map 1]⟩],
  use [expr a],
  have [] [":", expr «expr = »(f.trans (rotation a).symm 1, 1)] [],
  { simpa [] [] [] [] [] ["using", expr rotation_apply «expr ⁻¹»(a) (f 1)] },
  refine [expr (linear_isometry_complex_aux this).imp (λ h₁, _) (λ h₂, _)],
  { simpa [] [] [] [] [] ["using", expr eq_mul_of_inv_mul_eq h₁] },
  { exact [expr eq_mul_of_inv_mul_eq h₂] }
end

