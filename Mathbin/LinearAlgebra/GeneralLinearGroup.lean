import Mathbin.LinearAlgebra.Matrix.NonsingularInverse 
import Mathbin.LinearAlgebra.SpecialLinearGroup

/-!
# The General Linear group $GL(n, R)$
This file defines the elements of the General Linear group `general_linear_group n R`,
consisting of all invertible `n` by `n` `R`-matrices.
## Main definitions
* `matrix.general_linear_group` is the type of matrices over R which are units in the matrix ring.
* `matrix.GL_pos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).
## Tags
matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open_locale Matrix

open LinearMap

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices-/
abbrev general_linear_group (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [CommRingₓ R] : Type _ :=
  Units (Matrix n n R)

notation "GL" => general_linear_group

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRingₓ R]

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
def det : GL n R →* Units R :=
  { toFun :=
      fun A =>
        { val := («expr↑ » A : Matrix n n R).det, inv := («expr↑ » (A⁻¹) : Matrix n n R).det,
          val_inv :=
            by 
              rw [←det_mul, ←mul_eq_mul, A.mul_inv, det_one],
          inv_val :=
            by 
              rw [←det_mul, ←mul_eq_mul, A.inv_mul, det_one] },
    map_one' := Units.ext det_one, map_mul' := fun A B => Units.ext$ det_mul _ _ }

/--The `GL n R` and `general_linear_group R n` groups are multiplicatively equivalent-/
def to_lin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv to_lin_alg_equiv'.toMulEquiv

/--Given a matrix with invertible determinant we get an element of `GL n R`-/
def mk' (A : Matrix n n R) (h : Invertible (Matrix.det A)) : GL n R :=
  unit_of_det_invertible A

/--Given a matrix with unit determinant we get an element of `GL n R`-/
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsing_inv_unit A h

instance coe_fun : CoeFun (GL n R) fun _ => n → n → R :=
  { coe := fun A => A.val }

theorem ext_iff (A B : GL n R) : A = B ↔ ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
  Units.ext$ Matrix.ext h

section CoeLemmas

variable (A B : GL n R)

@[simp]
theorem coe_fn_eq_coe : «expr⇑ » A = («expr↑ » A : Matrix n n R) :=
  rfl

@[simp]
theorem coe_mul : «expr↑ » (A*B) = («expr↑ » A : Matrix n n R) ⬝ («expr↑ » B : Matrix n n R) :=
  rfl

@[simp]
theorem coe_one : «expr↑ » (1 : GL n R) = (1 : Matrix n n R) :=
  rfl

-- error in LinearAlgebra.GeneralLinearGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_inv : «expr = »(«expr↑ »(«expr ⁻¹»(A)), «expr ⁻¹»((«expr↑ »(A) : matrix n n R))) :=
begin
  letI [] [] [":=", expr A.invertible],
  exact [expr inv_of_eq_nonsing_inv («expr↑ »(A) : matrix n n R)]
end

end CoeLemmas

end GeneralLinearGroup

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRingₓ R]

instance has_coe_to_general_linear_group : Coe (special_linear_group n R) (GL n R) :=
  ⟨fun A => ⟨«expr↑ » A, «expr↑ » (A⁻¹), congr_argₓ coeₓ (mul_right_invₓ A), congr_argₓ coeₓ (mul_left_invₓ A)⟩⟩

end SpecialLinearGroup

section 

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]

section 

variable (n R)

/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
def GL_pos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap general_linear_group.det

end 

@[simp]
theorem mem_GL_pos (A : GL n R) : A ∈ GL_pos n R ↔ 0 < (A.det : R) :=
  Iff.rfl

end 

section Neg

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R] [Fact (Even (Fintype.card n))]

-- error in LinearAlgebra.GeneralLinearGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/ instance : has_neg (GL_pos n R) :=
⟨λ
 g, ⟨«expr- »(g), begin
    simp [] [] ["only"] ["[", expr mem_GL_pos, ",", expr general_linear_group.coe_det_apply, ",", expr units.coe_neg, "]"] [] [],
    have [] [] [":=", expr det_smul g «expr- »(1)],
    simp [] [] ["only"] ["[", expr general_linear_group.coe_fn_eq_coe, ",", expr one_smul, ",", expr coe_fn_coe_base', ",", expr neg_smul, "]"] [] ["at", ident this],
    rw [expr this] [],
    simp [] [] [] ["[", expr nat.neg_one_pow_of_even (fact.out (even (fintype.card n))), "]"] [] [],
    have [ident gdet] [] [":=", expr g.property],
    simp [] [] ["only"] ["[", expr mem_GL_pos, ",", expr general_linear_group.coe_det_apply, ",", expr subtype.val_eq_coe, "]"] [] ["at", ident gdet],
    exact [expr gdet]
  end⟩⟩

@[simp]
theorem GL_pos_coe_neg (g : GL_pos n R) : «expr↑ » (-g) = -(«expr↑ » g : Matrix n n R) :=
  rfl

@[simp]
theorem GL_pos_neg_elt (g : GL_pos n R) : ∀ i j, («expr↑ » (-g) : Matrix n n R) i j = -g i j :=
  by 
    simp [coe_fn_coe_base']

end Neg

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [LinearOrderedCommRing R]

/-- `special_linear_group n R` embeds into `GL_pos n R` -/
def to_GL_pos : special_linear_group n R →* GL_pos n R :=
  { toFun := fun A => ⟨(A : GL n R), show 0 < («expr↑ » A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩,
    map_one' := Subtype.ext$ Units.ext$ rfl, map_mul' := fun A₁ A₂ => Subtype.ext$ Units.ext$ rfl }

instance : Coe (special_linear_group n R) (GL_pos n R) :=
  ⟨to_GL_pos⟩

theorem coe_eq_to_GL_pos : (coeₓ : special_linear_group n R → GL_pos n R) = to_GL_pos :=
  rfl

theorem to_GL_pos_injective : Function.Injective (to_GL_pos : special_linear_group n R → GL_pos n R) :=
  (show Function.Injective ((coeₓ : GL_pos n R → Matrix n n R) ∘ to_GL_pos) from Subtype.coe_injective).of_comp

end SpecialLinearGroup

end Matrix

