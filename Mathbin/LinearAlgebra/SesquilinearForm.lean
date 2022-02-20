/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import Mathbin.Algebra.Module.LinearMap
import Mathbin.LinearAlgebra.BilinearMap
import Mathbin.LinearAlgebra.Matrix.Basis

/-!
# Sesquilinear form

This files provides properties about sesquilinear forms. The maps considered are of the form
`M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁` and `M₂` is a module over `R₂`.
Sesquilinear forms are the special case that `M₁ = M₂`, `R₁ = R₂ = R`, and `I₁ = ring_hom.id R`.
Taking additionally `I₂ = ring_hom.id R`, then one obtains bilinear forms.

These forms are a special case of the bilinear maps defined in `bilinear_map.lean` and all basic
lemmas about construction and elementary calculations are found there.

## Main declarations

* `is_ortho`: states that two vectors are orthogonal with respect to a sesquilinear form
* `is_symm`, `is_alt`: states that a sesquilinear form is symmetric and alternating, respectively
* `orthogonal_bilin`: provides the orthogonal complement with respect to sesquilinear form

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/


open_locale BigOperators

variable {R R₁ R₂ R₃ M M₁ M₂ K K₁ K₂ V V₁ V₂ n : Type _}

namespace LinearMap

/-! ### Orthogonal vectors -/


section CommRingₓ

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable [CommSemiringₓ R] [CommSemiringₓ R₁] [AddCommMonoidₓ M₁] [Module R₁ M₁] [CommSemiringₓ R₂] [AddCommMonoidₓ M₂]
  [Module R₂ M₂] {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def IsOrtho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) x y : Prop :=
  B x y = 0

theorem is_ortho_def {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} {x y} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

theorem is_ortho_zero_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) x : IsOrtho B (0 : M₁) x := by
  dunfold is_ortho
  rw [map_zero B, zero_apply]

theorem is_ortho_zero_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) x : IsOrtho B x (0 : M₂) :=
  map_zero (B x)

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`bilin_form.is_ortho` -/
def IsOrthoₓ {n : Type _} (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R) (v : n → M₁) : Prop :=
  Pairwise (B.IsOrtho on v)

theorem is_Ortho_def {n : Type _} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R} {v : n → M₁} :
    B.IsOrtho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl

end CommRingₓ

section Field

variable [Field K] [Field K₁] [AddCommGroupₓ V₁] [Module K₁ V₁] [Field K₂] [AddCommGroupₓ V₂] [Module K₂ V₂]
  {I₁ : K₁ →+* K} {I₂ : K₂ →+* K} {I₁' : K₁ →+* K} {J₁ : K →+* K} {J₂ : K →+* K}

-- todo: this also holds for [comm_ring R] [is_domain R] when J₁ is invertible
theorem ortho_smul_left {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] K} {x y} {a : K₁} (ha : a ≠ 0) :
    IsOrtho B x y ↔ IsOrtho B (a • x) y := by
  dunfold is_ortho
  constructor <;> intro H
  · rw [map_smulₛₗ₂, H, smul_zero]
    
  · rw [map_smulₛₗ₂, smul_eq_zero] at H
    cases H
    · rw [I₁.map_eq_zero] at H
      trivial
      
    · exact H
      
    

-- todo: this also holds for [comm_ring R] [is_domain R] when J₂ is invertible
theorem ortho_smul_right {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] K} {x y} {a : K₂} {ha : a ≠ 0} :
    IsOrtho B x y ↔ IsOrtho B x (a • y) := by
  dunfold is_ortho
  constructor <;> intro H
  · rw [map_smulₛₗ, H, smul_zero]
    
  · rw [map_smulₛₗ, smul_eq_zero] at H
    cases H
    · simp at H
      exfalso
      exact ha H
      
    · exact H
      
    

/-- A set of orthogonal vectors `v` with respect to some sesquilinear form `B` is linearly
  independent if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem linear_independent_of_is_Ortho {B : V₁ →ₛₗ[I₁] V₁ →ₛₗ[I₁'] K} {v : n → V₁} (hv₁ : B.IsOrtho v)
    (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K₁ v := by
  classical
  rw [linear_independent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by
    rw [hs, map_zero, zero_apply]
  have hsum : (s.sum fun j : n => I₁ (w j) * B (v j) (v i)) = I₁ (w i) * B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j hj hij
    rw [is_Ortho_def.1 hv₁ _ _ hij, mul_zero]
  simp_rw [B.map_sum₂, map_smulₛₗ₂, smul_eq_mul, hsum]  at this
  apply I₁.map_eq_zero.mp
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this

end Field

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [CommRingₓ R₁] [AddCommGroupₓ M₁] [Module R₁ M₁] {I : R →+* R}
  {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R} {B' : M →ₗ[R] M →ₛₗ[I] R}

/-! ### Reflexive bilinear forms -/


/-- The proposition that a sesquilinear form is reflexive -/
def IsRefl (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Prop :=
  ∀ x y, B x y = 0 → B y x = 0

namespace IsRefl

variable (H : B.IsRefl)

theorem eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := fun x y => H x y

theorem ortho_comm {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩

end IsRefl

/-! ### Symmetric bilinear forms -/


/-- The proposition that a sesquilinear form is symmetric -/
def IsSymm (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ x y, I (B x y) = B y x

namespace IsSymm

variable (H : B'.IsSymm)

include H

protected theorem eq x y : I (B' x y) = B' y x :=
  H x y

theorem is_refl : B'.IsRefl := fun x y H1 => by
  rw [← H]
  simp [H1]

theorem ortho_comm {x y} : IsOrtho B' x y ↔ IsOrtho B' y x :=
  H.IsRefl.ortho_comm

end IsSymm

/-! ### Alternating bilinear forms -/


/-- The proposition that a sesquilinear form is alternating -/
def IsAlt (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Prop :=
  ∀ x, B x x = 0

namespace IsAlt

variable (H : B.IsAlt)

include H

theorem self_eq_zero x : B x x = 0 :=
  H x

theorem neg x y : -B x y = B y x := by
  have H1 : B (y + x) (y + x) = 0 := self_eq_zero H (y + x)
  simp [map_add, self_eq_zero H] at H1
  rw [add_eq_zero_iff_neg_eq] at H1
  exact H1

theorem is_refl : B.IsRefl := by
  intro x y h
  rw [← neg H, h, neg_zero]

theorem ortho_comm {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.IsRefl.ortho_comm

end IsAlt

end LinearMap

namespace Submodule

/-! ### The orthogonal complement -/


variable [CommRingₓ R] [CommRingₓ R₁] [AddCommGroupₓ M₁] [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R}
  {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R}

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonalBilin (N : Submodule R₁ M₁) (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Submodule R₁ M₁ where
  Carrier := { m | ∀, ∀ n ∈ N, ∀, B.IsOrtho n m }
  zero_mem' := fun x _ => B.is_ortho_zero_right x
  add_mem' := fun x y hx hy n hn => by
    rw [LinearMap.IsOrtho, map_add, show B n x = 0 from hx n hn, show B n y = 0 from hy n hn, zero_addₓ]
  smul_mem' := fun c x hx n hn => by
    rw [LinearMap.IsOrtho, LinearMap.map_smulₛₗ, show B n x = 0 from hx n hn, smul_zero]

variable {N L : Submodule R₁ M₁}

@[simp]
theorem mem_orthogonal_bilin_iff {m : M₁} : m ∈ N.orthogonalBilin B ↔ ∀, ∀ n ∈ N, ∀, B.IsOrtho n m :=
  Iff.rfl

theorem orthogonal_bilin_le (h : N ≤ L) : L.orthogonalBilin B ≤ N.orthogonalBilin B := fun _ hn l hl => hn l (h hl)

theorem le_orthogonal_bilin_orthogonal_bilin (b : B.IsRefl) : N ≤ (N.orthogonalBilin B).orthogonalBilin B :=
  fun n hn m hm => b _ _ (hm n hn)

end Submodule

namespace LinearMap

section Orthogonal

variable [Field K] [AddCommGroupₓ V] [Module K V] [Field K₁] [AddCommGroupₓ V₁] [Module K₁ V₁] {J : K →+* K}
  {J₁ : K₁ →+* K} {J₁' : K₁ →+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot (B : V₁ →ₛₗ[J₁] V₁ →ₛₗ[J₁'] K) (x : V₁) (hx : ¬B.IsOrtho x x) :
    (K₁∙x)⊓Submodule.orthogonalBilin (K₁∙x) B = ⊥ := by
  rw [← Finset.coe_singleton]
  refine' eq_bot_iff.2 fun y h => _
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩
  have := h.2 x _
  · rw [Finset.sum_singleton] at this⊢
    suffices hμzero : μ x = 0
    · rw [hμzero, zero_smul, Submodule.mem_bot]
      
    change B x (μ x • x) = 0 at this
    rw [map_smulₛₗ, smul_eq_mul] at this
    exact
      Or.elim (zero_eq_mul.mp this.symm)
        (fun y => by
          simp at y
          exact y)
        fun hfalse => False.elim <| hx hfalse
    
  · rw [Submodule.mem_span] <;> exact fun _ hp => hp <| Finset.mem_singleton_self _
    

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_to_lin_ker {B : V →ₗ[K] V →ₛₗ[J] K} (x : V) :
    Submodule.orthogonalBilin (K∙x) B = (B x).ker := by
  ext y
  simp_rw [Submodule.mem_orthogonal_bilin_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
    
  · rintro h _ ⟨z, rfl⟩
    rw [is_ortho, map_smulₛₗ₂, smul_eq_zero]
    exact Or.intro_rightₓ _ h
    

-- todo: Generalize this to sesquilinear maps
theorem span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : ¬B.IsOrtho x x) :
    (K∙x)⊔Submodule.orthogonalBilin (K∙x) B = ⊤ := by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact (B x).span_singleton_sup_ker_eq_top hx

/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
-- todo: Generalize this to sesquilinear maps
theorem is_compl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K∙x) (Submodule.orthogonalBilin (K∙x) B) :=
  { inf_le_bot := eq_bot_iff.1 <| span_singleton_inf_orthogonal_eq_bot B x hx,
    top_le_sup := eq_top_iff.1 <| span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

end LinearMap

