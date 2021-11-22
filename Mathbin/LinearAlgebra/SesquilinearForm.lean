import Mathbin.RingTheory.RingInvo 
import Mathbin.Algebra.Module.LinearMap 
import Mathbin.Tactic.Abel

/-!
# Sesquilinear form

This file defines a sesquilinear form over a module. The definition requires a ring antiautomorphism
on the scalar ring. Basic ideas such as
orthogonality are also introduced.

A sesquilinear form on an `R`-module `M`, is a function from `M × M` to `R`, that is linear in the
first argument and antilinear in the second, with respect to an antiautomorphism on `R` (an
antiisomorphism from `R` to `R`).

## Notations

Given any term `S` of type `sesq_form`, due to a coercion, can use the notation `S x y` to
refer to the function field, ie. `S x y = S.sesq x y`.

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/


open_locale BigOperators

universe u v w

/-- A sesquilinear form over a module  -/
structure SesqForm(R : Type u)(M : Type v)[Ringₓ R](I : R ≃+* «expr ᵒᵖ» R)[AddCommGroupₓ M][Module R M] where 
  sesq : M → M → R 
  sesq_add_left : ∀ x y z : M, sesq (x+y) z = sesq x z+sesq y z 
  sesq_smul_left : ∀ a : R x y : M, sesq (a • x) y = a*sesq x y 
  sesq_add_right : ∀ x y z : M, sesq x (y+z) = sesq x y+sesq x z 
  sesq_smul_right : ∀ a : R x y : M, sesq x (a • y) = (I a).unop*sesq x y

namespace SesqForm

section GeneralRing

variable{R : Type u}{M : Type v}[Ringₓ R][AddCommGroupₓ M][Module R M]

variable{I : R ≃+* «expr ᵒᵖ» R}{S : SesqForm R M I}

instance  : CoeFun (SesqForm R M I) fun _ => M → M → R :=
  ⟨sesq⟩

theorem add_left (x y z : M) : S (x+y) z = S x z+S y z :=
  sesq_add_left S x y z

theorem smul_left (a : R) (x y : M) : S (a • x) y = a*S x y :=
  sesq_smul_left S a x y

theorem add_right (x y z : M) : S x (y+z) = S x y+S x z :=
  sesq_add_right S x y z

theorem smul_right (a : R) (x y : M) : S x (a • y) = (I a).unop*S x y :=
  sesq_smul_right S a x y

theorem zero_left (x : M) : S 0 x = 0 :=
  by 
    rw [←zero_smul R (0 : M), smul_left, zero_mul]

theorem zero_right (x : M) : S x 0 = 0 :=
  by 
    rw [←zero_smul R (0 : M), smul_right]
    simp 

theorem neg_left (x y : M) : S (-x) y = -S x y :=
  by 
    rw [←@neg_one_smul R _ _, smul_left, neg_one_mul]

theorem neg_right (x y : M) : S x (-y) = -S x y :=
  by 
    rw [←@neg_one_smul R _ _, smul_right]
    simp 

theorem sub_left (x y z : M) : S (x - y) z = S x z - S y z :=
  by 
    simp only [sub_eq_add_neg, add_left, neg_left]

theorem sub_right (x y z : M) : S x (y - z) = S x y - S x z :=
  by 
    simp only [sub_eq_add_neg, add_right, neg_right]

variable{D : SesqForm R M I}

@[ext]
theorem ext (H : ∀ x y : M, S x y = D x y) : S = D :=
  by 
    cases S 
    cases D 
    congr 
    funext 
    exact H _ _

instance  : Add (SesqForm R M I) :=
  ⟨fun S D =>
      { sesq := fun x y => S x y+D x y,
        sesq_add_left :=
          fun x y z =>
            by 
              rw [add_left]
              rw [add_left]
              abel,
        sesq_smul_left :=
          fun a x y =>
            by 
              rw [smul_left, smul_left, mul_addₓ],
        sesq_add_right :=
          fun x y z =>
            by 
              rw [add_right]
              rw [add_right]
              abel,
        sesq_smul_right :=
          fun a x y =>
            by 
              rw [smul_right, smul_right, mul_addₓ] }⟩

instance  : HasZero (SesqForm R M I) :=
  ⟨{ sesq := fun x y => 0, sesq_add_left := fun x y z => (add_zeroₓ 0).symm,
      sesq_smul_left := fun a x y => (mul_zero a).symm, sesq_add_right := fun x y z => (zero_addₓ 0).symm,
      sesq_smul_right := fun a x y => (mul_zero (I a).unop).symm }⟩

instance  : Neg (SesqForm R M I) :=
  ⟨fun S =>
      { sesq := fun x y => -S.1 x y,
        sesq_add_left :=
          fun x y z =>
            by 
              rw [sesq_add_left, neg_add],
        sesq_smul_left :=
          fun a x y =>
            by 
              rw [sesq_smul_left, mul_neg_eq_neg_mul_symm],
        sesq_add_right :=
          fun x y z =>
            by 
              rw [sesq_add_right, neg_add],
        sesq_smul_right :=
          fun a x y =>
            by 
              rw [sesq_smul_right, mul_neg_eq_neg_mul_symm] }⟩

instance  : AddCommGroupₓ (SesqForm R M I) :=
  { add := ·+·,
    add_assoc :=
      by 
        intros 
        ext 
        unfold coeFn CoeFun.coe sesq coeFn CoeFun.coe sesq 
        rw [add_assocₓ],
    zero := 0,
    zero_add :=
      by 
        intros 
        ext 
        unfold coeFn CoeFun.coe sesq 
        rw [zero_addₓ],
    add_zero :=
      by 
        intros 
        ext 
        unfold coeFn CoeFun.coe sesq 
        rw [add_zeroₓ],
    neg := Neg.neg,
    add_left_neg :=
      by 
        intros 
        ext 
        unfold coeFn CoeFun.coe sesq 
        rw [neg_add_selfₓ],
    add_comm :=
      by 
        intros 
        ext 
        unfold coeFn CoeFun.coe sesq 
        rw [add_commₓ] }

instance  : Inhabited (SesqForm R M I) :=
  ⟨0⟩

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho (S : SesqForm R M I) (x y : M) : Prop :=
  S x y = 0

theorem ortho_zero (x : M) : is_ortho S (0 : M) x :=
  zero_left x

/-- For fixed `y : M`, the `R`-linear map sending `x : M` to `S x y`, where `S` is a
sesquilinear form. -/
@[simps]
def linear_map_left (S : SesqForm R M I) (x : M) : M →ₗ[R] R :=
  { toFun := fun z => S z x, map_add' := fun z y => sesq_add_left S _ _ _,
    map_smul' := fun r m => sesq_smul_left S _ _ _ }

/-- For fixed `x : M`, the `add_monoid_hom` sending `y : M` to `S x y`, where `S` is a
sesquilinear form. -/
@[simps]
def add_monoid_hom_right (S : SesqForm R M I) (x : M) : M →+ R :=
  { toFun := fun z => S x z, map_zero' := zero_right x, map_add' := fun z y => sesq_add_right S _ _ _ }

theorem sum_left {α : Type _} (S : SesqForm R M I) (t : Finset α) (g : α → M) (w : M) :
  S (∑i in t, g i) w = ∑i in t, S (g i) w :=
  (linear_map_left S w).map_sum

theorem sum_right {α : Type _} (S : SesqForm R M I) (t : Finset α) (g : α → M) (w : M) :
  S w (∑i in t, g i) = ∑i in t, S w (g i) :=
  (add_monoid_hom_right S w).map_sum _ t

variable{M₂ : Type w}[AddCommGroupₓ M₂][Module R M₂]

/-- Apply the linear maps `f` and `g` to the left and right arguments of the sesquilinear form. -/
def comp (S : SesqForm R M I) (f g : M₂ →ₗ[R] M) : SesqForm R M₂ I :=
  { sesq := fun x y => S (f x) (g y),
    sesq_add_left :=
      by 
        simp [add_left],
    sesq_smul_left :=
      by 
        simp [smul_left],
    sesq_add_right :=
      by 
        simp [add_right],
    sesq_smul_right :=
      by 
        simp [smul_right] }

/-- Apply the linear map `f` to the left argument of the sesquilinear form. -/
def comp_left (S : SesqForm R M I) (f : M →ₗ[R] M) : SesqForm R M I :=
  S.comp f LinearMap.id

/-- Apply the linear map `f` to the right argument of the sesquilinear form. -/
def comp_right (S : SesqForm R M I) (f : M →ₗ[R] M) : SesqForm R M I :=
  S.comp LinearMap.id f

theorem comp_left_comp_right (S : SesqForm R M I) (f g : M →ₗ[R] M) : (S.comp_left f).compRight g = S.comp f g :=
  rfl

theorem comp_right_comp_left (S : SesqForm R M I) (f g : M →ₗ[R] M) : (S.comp_right g).compLeft f = S.comp f g :=
  rfl

theorem comp_comp {M₃ : Type _} [AddCommGroupₓ M₃] [Module R M₃] (S : SesqForm R M₃ I) (l r : M →ₗ[R] M₂)
  (l' r' : M₂ →ₗ[R] M₃) : (S.comp l' r').comp l r = S.comp (l'.comp l) (r'.comp r) :=
  rfl

@[simp]
theorem comp_apply (S : SesqForm R M₂ I) (l r : M →ₗ[R] M₂) (v w : M) : S.comp l r v w = S (l v) (r w) :=
  rfl

@[simp]
theorem comp_left_apply (S : SesqForm R M I) (f : M →ₗ[R] M) (v w : M) : S.comp_left f v w = S (f v) w :=
  rfl

@[simp]
theorem comp_right_apply (S : SesqForm R M I) (f : M →ₗ[R] M) (v w : M) : S.comp_right f v w = S v (f w) :=
  rfl

/-- Let `l`, `r` be surjective linear maps, then two sesquilinear forms are equal if and only if
  the sesquilinear forms resulting from composition with `l` and `r` are equal. -/
theorem comp_injective (S₁ S₂ : SesqForm R M₂ I) {l r : M →ₗ[R] M₂} (hl : Function.Surjective l)
  (hr : Function.Surjective r) : S₁.comp l r = S₂.comp l r ↔ S₁ = S₂ :=
  by 
    split  <;> intro h
    ·
      ext 
      rcases hl x with ⟨x', rfl⟩
      rcases hr y with ⟨y', rfl⟩
      rw [←comp_apply, ←comp_apply, h]
    ·
      rw [h]

end GeneralRing

section CommRingₓ

variable{R :
    Type _}[CommRingₓ R]{M : Type v}[AddCommGroupₓ M][Module R M]{J : R ≃+* «expr ᵒᵖ» R}(F : SesqForm R M J)(f : M → M)

instance to_module : Module R (SesqForm R M J) :=
  { smul :=
      fun c S =>
        { sesq := fun x y => c*S x y,
          sesq_add_left :=
            fun x y z =>
              by 
                unfold coeFn CoeFun.coe sesq 
                rw [sesq_add_left, left_distrib],
          sesq_smul_left :=
            fun a x y =>
              by 
                unfold coeFn CoeFun.coe sesq 
                rw [sesq_smul_left, ←mul_assocₓ, mul_commₓ c, mul_assocₓ],
          sesq_add_right :=
            fun x y z =>
              by 
                unfold coeFn CoeFun.coe sesq 
                rw [sesq_add_right, left_distrib],
          sesq_smul_right :=
            fun a x y =>
              by 
                unfold coeFn CoeFun.coe sesq 
                rw [sesq_smul_right, ←mul_assocₓ, mul_commₓ c, mul_assocₓ]
                rfl },
    smul_add :=
      fun c S D =>
        by 
          ext 
          unfold coeFn CoeFun.coe sesq 
          rw [left_distrib],
    add_smul :=
      fun c S D =>
        by 
          ext 
          unfold coeFn CoeFun.coe sesq 
          rw [right_distrib],
    mul_smul :=
      fun a c D =>
        by 
          ext 
          unfold coeFn CoeFun.coe sesq 
          rw [mul_assocₓ],
    one_smul :=
      fun S =>
        by 
          ext 
          unfold coeFn CoeFun.coe sesq 
          rw [one_mulₓ],
    zero_smul :=
      fun S =>
        by 
          ext 
          unfold coeFn CoeFun.coe sesq 
          rw [zero_mul],
    smul_zero :=
      fun S =>
        by 
          ext 
          unfold coeFn CoeFun.coe sesq 
          rw [mul_zero] }

end CommRingₓ

section IsDomain

variable{R :
    Type _}[Ringₓ R][IsDomain R]{M : Type v}[AddCommGroupₓ M][Module R M]{K : R ≃+* «expr ᵒᵖ» R}{G : SesqForm R M K}

theorem ortho_smul_left {x y : M} {a : R} (ha : a ≠ 0) : is_ortho G x y ↔ is_ortho G (a • x) y :=
  by 
    dunfold is_ortho 
    split  <;> intro H
    ·
      rw [smul_left, H, mul_zero]
    ·
      rw [smul_left, mul_eq_zero] at H 
      cases H
      ·
        trivial
      ·
        exact H

theorem ortho_smul_right {x y : M} {a : R} (ha : a ≠ 0) : is_ortho G x y ↔ is_ortho G x (a • y) :=
  by 
    dunfold is_ortho 
    split  <;> intro H
    ·
      rw [smul_right, H, mul_zero]
    ·
      rw [smul_right, mul_eq_zero] at H 
      cases H
      ·
        exFalso 
        simp only [Opposite.unop_eq_zero_iff] at H 
        exact ha (K.map_eq_zero_iff.mp H)
      ·
        exact H

end IsDomain

variable{R : Type _}{M : Type _}[Ringₓ R][AddCommGroupₓ M][Module R M]

variable{I : R ≃+* «expr ᵒᵖ» R}{S : SesqForm R M I}

/-- The proposition that a sesquilinear form is reflexive -/
def IsRefl (S : SesqForm R M I) : Prop :=
  ∀ x y : M, S x y = 0 → S y x = 0

namespace IsRefl

variable(H : S.is_refl)

theorem eq_zero : ∀ {x y : M}, S x y = 0 → S y x = 0 :=
  fun x y => H x y

theorem ortho_comm {x y : M} : is_ortho S x y ↔ is_ortho S y x :=
  ⟨eq_zero H, eq_zero H⟩

end IsRefl

/-- The proposition that a sesquilinear form is symmetric -/
def IsSymm (S : SesqForm R M I) : Prop :=
  ∀ x y : M, (I (S x y)).unop = S y x

namespace IsSymm

variable(H : S.is_symm)

include H

protected theorem Eq (x y : M) : (I (S x y)).unop = S y x :=
  H x y

theorem IsRefl : S.is_refl :=
  fun x y H1 =>
    by 
      rw [←H]
      simp [H1]

theorem ortho_comm {x y : M} : is_ortho S x y ↔ is_ortho S y x :=
  H.is_refl.ortho_comm

end IsSymm

/-- The proposition that a sesquilinear form is alternating -/
def is_alt (S : SesqForm R M I) : Prop :=
  ∀ x : M, S x x = 0

namespace IsAlt

variable(H : S.is_alt)

include H

theorem self_eq_zero (x : M) : S x x = 0 :=
  H x

theorem neg (x y : M) : -S x y = S y x :=
  by 
    have H1 : S (x+y) (x+y) = 0
    ·
      exact self_eq_zero H (x+y)
    rw [add_left, add_right, add_right, self_eq_zero H, self_eq_zero H, Ringₓ.zero_add, Ringₓ.add_zero,
      add_eq_zero_iff_neg_eq] at H1 
    exact H1

theorem IsRefl : S.is_refl :=
  by 
    intro x y h 
    rw [←neg H, h, neg_zero]

theorem ortho_comm {x y : M} : is_ortho S x y ↔ is_ortho S y x :=
  H.is_refl.ortho_comm

end IsAlt

end SesqForm

