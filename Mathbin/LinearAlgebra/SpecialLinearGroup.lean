import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `special_linear_group n R` and the embedding into the general linear group
`general_linear_group R (n → R)`.

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.to_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = fin m`, in the locale `matrix_groups`.

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `matrix.special_linear_group.has_coe_to_fun` for convenience, but do not state any
lemmas about it, and use `matrix.special_linear_group.coe_fn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open_locale Matrix

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRingₓ R]

/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def special_linear_group :=
  { A : Matrix n n R // A.det = 1 }

end

localized [MatrixGroups] notation "SL(" n "," R ")" => Matrix.SpecialLinearGroup (Finₓ n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRingₓ R]

instance has_coe_to_matrix : Coe (special_linear_group n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩

local prefix:1024 "↑ₘ" => @coe _ (Matrix n n R) _

theorem ext_iff (A B : special_linear_group n R) : A = B ↔ ∀ i j, ↑ₘA i j = ↑ₘB i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]
theorem ext (A B : special_linear_group n R) : (∀ i j, ↑ₘA i j = ↑ₘB i j) → A = B :=
  (special_linear_group.ext_iff A B).mpr

instance HasInv : HasInv (special_linear_group n R) :=
  ⟨fun A =>
    ⟨adjugate A, by
      rw [det_adjugate, A.prop, one_pow]⟩⟩

instance Mul : Mul (special_linear_group n R) :=
  ⟨fun A B =>
    ⟨A.1 ⬝ B.1, by
      erw [det_mul, A.2, B.2, one_mulₓ]⟩⟩

instance One : One (special_linear_group n R) :=
  ⟨⟨1, det_one⟩⟩

instance : Inhabited (special_linear_group n R) :=
  ⟨1⟩

section CoeLemmas

variable (A B : special_linear_group n R)

@[simp]
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : special_linear_group n R) = A :=
  rfl

@[simp]
theorem coe_inv : ↑ₘ(A⁻¹) = adjugate A :=
  rfl

@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA ⬝ ↑ₘB :=
  rfl

@[simp]
theorem coe_one : ↑ₘ(1 : special_linear_group n R) = (1 : Matrix n n R) :=
  rfl

@[simp]
theorem det_coe : det ↑ₘA = 1 :=
  A.2

theorem det_ne_zero [Nontrivial R] (g : special_linear_group n R) : det ↑ₘg ≠ 0 := by
  rw [g.det_coe]
  norm_num

theorem row_ne_zero [Nontrivial R] (g : special_linear_group n R) (i : n) : ↑ₘg i ≠ 0 := fun h =>
  g.det_ne_zero $
    det_eq_zero_of_row_eq_zero i $ by
      simp [h]

end CoeLemmas

instance : Monoidₓ (special_linear_group n R) :=
  Function.Injective.monoid coe Subtype.coe_injective coe_one coe_mul

instance : Groupₓ (special_linear_group n R) :=
  { special_linear_group.monoid, special_linear_group.has_inv with
    mul_left_inv := fun A => by
      ext1
      simp [adjugate_mul] }

/-- A version of `matrix.to_lin' A` that produces linear equivalences. -/
def to_lin' : special_linear_group n R →* (n → R) ≃ₗ[R] n → R where
  toFun := fun A =>
    LinearEquiv.ofLinear (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘ(A⁻¹))
      (by
        rw [← to_lin'_mul, ← coe_mul, mul_right_invₓ, coe_one, to_lin'_one])
      (by
        rw [← to_lin'_mul, ← coe_mul, mul_left_invₓ, coe_one, to_lin'_one])
  map_one' := LinearEquiv.to_linear_map_injective Matrix.to_lin'_one
  map_mul' := fun A B => LinearEquiv.to_linear_map_injective $ Matrix.to_lin'_mul A B

theorem to_lin'_apply (A : special_linear_group n R) (v : n → R) :
    special_linear_group.to_lin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl

theorem to_lin'_to_linear_map (A : special_linear_group n R) : ↑special_linear_group.to_lin' A = Matrix.toLin' ↑ₘA :=
  rfl

theorem to_lin'_symm_apply (A : special_linear_group n R) (v : n → R) : A.to_lin'.symm v = Matrix.toLin' (↑ₘ(A⁻¹)) v :=
  rfl

theorem to_lin'_symm_to_linear_map (A : special_linear_group n R) : ↑A.to_lin'.symm = Matrix.toLin' ↑ₘ(A⁻¹) :=
  rfl

theorem to_lin'_injective : Function.Injective (⇑(to_lin' : special_linear_group n R →* (n → R) ≃ₗ[R] n → R)) :=
  fun A B h => Subtype.coe_injective $ Matrix.toLin'.Injective $ LinearEquiv.to_linear_map_injective.eq_iff.mpr h

/-- `to_GL` is the map from the special linear group to the general linear group -/
def to_GL : special_linear_group n R →* general_linear_group R (n → R) :=
  (general_linear_group.general_linear_equiv _ _).symm.toMonoidHom.comp to_lin'

theorem coe_to_GL (A : special_linear_group n R) : ↑A.to_GL = A.to_lin'.to_linear_map :=
  rfl

variable {S : Type _} [CommRingₓ S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`special_linear_group n R` to `special_linear_group n S`. -/
@[simps]
def map (f : R →+* S) : special_linear_group n R →* special_linear_group n S where
  toFun := fun g =>
    ⟨f.map_matrix (↑g), by
      rw [← f.map_det]
      simp [g.2]⟩
  map_one' := Subtype.ext $ f.map_matrix.map_one
  map_mul' := fun x y => Subtype.ext $ f.map_matrix.map_mul x y

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
instance : Coe (special_linear_group n ℤ) (special_linear_group n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

@[simp]
theorem coe_matrix_coe (g : special_linear_group n ℤ) :
    ↑(g : special_linear_group n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on special linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (special_linear_group n R) :=
  ⟨fun g =>
    ⟨-g, by
      simpa [Nat.neg_one_pow_of_even (Fact.out (Even (Fintype.card n))), g.det_coe] using det_smul (↑ₘg) (-1)⟩⟩

@[simp]
theorem coe_neg (g : special_linear_group n R) : ↑(-g) = -(↑g : Matrix n n R) :=
  rfl

@[simp]
theorem coe_int_neg (g : special_linear_group n ℤ) : ↑(-g) = (-↑g : special_linear_group n R) :=
  Subtype.ext $ (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg (↑g)

end Neg

section CoeFnInstance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : CoeFun (special_linear_group n R) fun _ => n → n → R where
  coe := fun A => A.val

@[simp]
theorem coe_fn_eq_coe (s : special_linear_group n R) : ⇑s = ↑ₘs :=
  rfl

end CoeFnInstance

end SpecialLinearGroup

end Matrix

