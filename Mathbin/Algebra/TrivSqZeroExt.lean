import Mathbin.Algebra.Algebra.Basic

/-!
# Trivial Square-Zero Extension

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/


universe u v w

/--
"Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
@[nolint has_inhabited_instance]
def TrivSqZeroExt (R : Type u) (M : Type v) :=
  R × M

local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Basic

variable {R : Type u} {M : Type v}

/-- The canonical inclusion `R → triv_sq_zero_ext R M`. -/
def inl [HasZero M] (r : R) : tsze R M :=
  (r, 0)

/-- The canonical inclusion `M → triv_sq_zero_ext R M`. -/
def inr [HasZero R] (m : M) : tsze R M :=
  (0, m)

/-- The canonical projection `triv_sq_zero_ext R M → R`. -/
def fst (x : tsze R M) : R :=
  x.1

/-- The canonical projection `triv_sq_zero_ext R M → M`. -/
def snd (x : tsze R M) : M :=
  x.2

@[ext]
theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.extₓ h1 h2

@[simp]
theorem fst_inl [HasZero M] (r : R) : (inl r : tsze R M).fst = r :=
  rfl

@[simp]
theorem snd_inl [HasZero M] (r : R) : (inl r : tsze R M).snd = 0 :=
  rfl

@[simp]
theorem fst_inr [HasZero R] (m : M) : (inr m : tsze R M).fst = 0 :=
  rfl

@[simp]
theorem snd_inr [HasZero R] (m : M) : (inr m : tsze R M).snd = m :=
  rfl

theorem inl_injective [HasZero M] : Function.Injective (inl : R → tsze R M) :=
  Function.LeftInverse.injective fst_inl

theorem inr_injective [HasZero R] : Function.Injective (inr : M → tsze R M) :=
  Function.LeftInverse.injective snd_inr

end Basic

section Add

variable (R : Type u) (M : Type v)

instance [HasZero R] [HasZero M] : HasZero (tsze R M) :=
  Prod.hasZero

@[simp]
theorem fst_zero [HasZero R] [HasZero M] : (0 : tsze R M).fst = 0 :=
  rfl

@[simp]
theorem snd_zero [HasZero R] [HasZero M] : (0 : tsze R M).snd = 0 :=
  rfl

@[simp]
theorem inl_zero [HasZero R] [HasZero M] : (inl 0 : tsze R M) = 0 :=
  rfl

@[simp]
theorem inr_zero [HasZero R] [HasZero M] : (inr 0 : tsze R M) = 0 :=
  rfl

instance [Add R] [Add M] : Add (tsze R M) :=
  Prod.hasAdd

@[simp]
theorem fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁+x₂).fst = x₁.fst+x₂.fst :=
  rfl

@[simp]
theorem snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁+x₂).snd = x₁.snd+x₂.snd :=
  rfl

instance [Neg R] [Neg M] : Neg (tsze R M) :=
  Prod.hasNeg

@[simp]
theorem fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst :=
  rfl

@[simp]
theorem snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd :=
  rfl

instance [AddSemigroupₓ R] [AddSemigroupₓ M] : AddSemigroupₓ (tsze R M) :=
  Prod.addSemigroup

instance [AddMonoidₓ R] [AddMonoidₓ M] : AddMonoidₓ (tsze R M) :=
  Prod.addMonoid

@[simp]
theorem inl_add [Add R] [AddMonoidₓ M] (r₁ r₂ : R) : (inl (r₁+r₂) : tsze R M) = inl r₁+inl r₂ :=
  ext rfl (add_zeroₓ 0).symm

@[simp]
theorem inr_add [AddMonoidₓ R] [Add M] (m₁ m₂ : M) : (inr (m₁+m₂) : tsze R M) = inr m₁+inr m₂ :=
  ext (add_zeroₓ 0).symm rfl

theorem inl_fst_add_inr_snd_eq [AddMonoidₓ R] [AddMonoidₓ M] (x : tsze R M) : (inl x.fst+inr x.snd) = x :=
  ext (add_zeroₓ x.1) (zero_addₓ x.2)

instance [AddGroupₓ R] [AddGroupₓ M] : AddGroupₓ (tsze R M) :=
  Prod.addGroup

@[simp]
theorem inl_neg [Neg R] [AddGroupₓ M] (r : R) : (inl (-r) : tsze R M) = -inl r :=
  ext rfl neg_zero.symm

@[simp]
theorem inr_neg [AddGroupₓ R] [Neg M] (m : M) : (inr (-m) : tsze R M) = -inr m :=
  ext neg_zero.symm rfl

instance [AddCommSemigroupₓ R] [AddCommSemigroupₓ M] : AddCommSemigroupₓ (tsze R M) :=
  Prod.addCommSemigroup

instance [AddCommMonoidₓ R] [AddCommMonoidₓ M] : AddCommMonoidₓ (tsze R M) :=
  Prod.addCommMonoid

instance [AddCommGroupₓ R] [AddCommGroupₓ M] : AddCommGroupₓ (tsze R M) :=
  Prod.addCommGroup

end Add

section Smul

variable (R : Type u) (M : Type v)

instance [Mul R] [HasScalar R M] : HasScalar R (tsze R M) :=
  ⟨fun r x => (r*x.1, r • x.2)⟩

@[simp]
theorem fst_smul [Mul R] [HasScalar R M] (r : R) (x : tsze R M) : (r • x).fst = r*x.fst :=
  rfl

@[simp]
theorem snd_smul [Mul R] [HasScalar R M] (r : R) (x : tsze R M) : (r • x).snd = r • x.snd :=
  rfl

@[simp]
theorem inr_smul [MulZeroClass R] [HasScalar R M] (r : R) (m : M) : (inr (r • m) : tsze R M) = r • inr m :=
  ext (mul_zero _).symm rfl

instance [Monoidₓ R] [MulAction R M] : MulAction R (tsze R M) :=
  { one_smul := fun x => ext (one_mulₓ x.1) (one_smul R x.2),
    mul_smul := fun r₁ r₂ x => ext (mul_assocₓ r₁ r₂ x.1) (mul_smul r₁ r₂ x.2) }

instance [Semiringₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R (tsze R M) :=
  { smul_add := fun r x₁ x₂ => ext (mul_addₓ r x₁.1 x₂.1) (smul_add r x₁.2 x₂.2),
    smul_zero := fun r => ext (mul_zero r) (smul_zero r) }

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module R (tsze R M) :=
  { add_smul := fun r₁ r₂ x => ext (add_mulₓ r₁ r₂ x.1) (add_smul r₁ r₂ x.2),
    zero_smul := fun x => ext (zero_mul x.1) (zero_smul R x.2) }

/-- The canonical `R`-linear inclusion `M → triv_sq_zero_ext R M`. -/
@[simps apply]
def inr_hom [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : M →ₗ[R] tsze R M :=
  { toFun := inr, map_add' := inr_add R M, map_smul' := inr_smul R M }

end Smul

section Mul

variable (R : Type u) (M : Type v)

instance [HasOne R] [HasZero M] : HasOne (tsze R M) :=
  ⟨(1, 0)⟩

@[simp]
theorem fst_one [HasOne R] [HasZero M] : (1 : tsze R M).fst = 1 :=
  rfl

@[simp]
theorem snd_one [HasOne R] [HasZero M] : (1 : tsze R M).snd = 0 :=
  rfl

@[simp]
theorem inl_one [HasOne R] [HasZero M] : (inl 1 : tsze R M) = 1 :=
  rfl

instance [Mul R] [Add M] [HasScalar R M] : Mul (tsze R M) :=
  ⟨fun x y => (x.1*y.1, (x.1 • y.2)+y.1 • x.2)⟩

@[simp]
theorem fst_mul [Mul R] [Add M] [HasScalar R M] (x₁ x₂ : tsze R M) : (x₁*x₂).fst = x₁.fst*x₂.fst :=
  rfl

@[simp]
theorem snd_mul [Mul R] [Add M] [HasScalar R M] (x₁ x₂ : tsze R M) : (x₁*x₂).snd = (x₁.fst • x₂.snd)+x₂.fst • x₁.snd :=
  rfl

@[simp]
theorem inl_mul [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] (r₁ r₂ : R) :
  (inl (r₁*r₂) : tsze R M) = inl r₁*inl r₂ :=
  ext rfl$
    show (0 : M) = (r₁ • 0)+r₂ • 0 by 
      rw [smul_zero, zero_addₓ, smul_zero]

theorem inl_mul_inl [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] (r₁ r₂ : R) :
  (inl r₁*inl r₂ : tsze R M) = inl (r₁*r₂) :=
  (inl_mul R M r₁ r₂).symm

theorem inl_mul_inr [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (r : R) (m : M) :
  (inl r*inr m : tsze R M) = inr (r • m) :=
  ext (mul_zero r)$
    show ((r • m)+(0 : R) • 0) = r • m by 
      rw [smul_zero, add_zeroₓ]

theorem inr_mul_inl [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (r : R) (m : M) :
  (inr m*inl r : tsze R M) = inr (r • m) :=
  ext (zero_mul r)$
    show (((0 : R) • 0)+r • m) = r • m by 
      rw [smul_zero, zero_addₓ]

@[simp]
theorem inr_mul_inr [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (m₁ m₂ : M) : (inr m₁*inr m₂ : tsze R M) = 0 :=
  ext (mul_zero _)$
    show (((0 : R) • m₂)+(0 : R) • m₁) = 0 by 
      rw [zero_smul, zero_addₓ, zero_smul]

instance [CommMonoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : Monoidₓ (tsze R M) :=
  { TrivSqZeroExt.hasOne R M, TrivSqZeroExt.hasMul R M with
    mul_assoc :=
      fun x y z =>
        ext (mul_assocₓ x.1 y.1 z.1)$
          show (((x.1*y.1) • z.2)+z.1 • (x.1 • y.2)+y.1 • x.2) = (x.1 • (y.1 • z.2)+z.1 • y.2)+(y.1*z.1) • x.2by 
            simpRw [smul_add, ←mul_smul, add_assocₓ, mul_commₓ],
    one_mul :=
      fun x =>
        ext (one_mulₓ x.1)$
          show (((1 : R) • x.2)+x.1 • 0) = x.2by 
            rw [one_smul, smul_zero, add_zeroₓ],
    mul_one :=
      fun x =>
        ext (mul_oneₓ x.1)$
          show ((x.1 • 0 : M)+(1 : R) • x.2) = x.2by 
            rw [smul_zero, zero_addₓ, one_smul] }

instance [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] : CommSemiringₓ (tsze R M) :=
  { TrivSqZeroExt.monoid R M, TrivSqZeroExt.addCommMonoid R M with
    mul_comm :=
      fun x₁ x₂ =>
        ext (mul_commₓ x₁.1 x₂.1)$ show ((x₁.1 • x₂.2)+x₂.1 • x₁.2) = (x₂.1 • x₁.2)+x₁.1 • x₂.2 from add_commₓ _ _,
    zero_mul :=
      fun x =>
        ext (zero_mul x.1)$
          show (((0 : R) • x.2)+x.1 • 0) = 0 by 
            rw [zero_smul, zero_addₓ, smul_zero],
    mul_zero :=
      fun x =>
        ext (mul_zero x.1)$
          show ((x.1 • 0 : M)+(0 : R) • x.2) = 0 by 
            rw [smul_zero, zero_addₓ, zero_smul],
    left_distrib :=
      fun x₁ x₂ x₃ =>
        ext (mul_addₓ x₁.1 x₂.1 x₃.1)$
          show ((x₁.1 • x₂.2+x₃.2)+(x₂.1+x₃.1) • x₁.2) = ((x₁.1 • x₂.2)+x₂.1 • x₁.2)+(x₁.1 • x₃.2)+x₃.1 • x₁.2by 
            simpRw [smul_add, add_smul, add_add_add_commₓ],
    right_distrib :=
      fun x₁ x₂ x₃ =>
        ext (add_mulₓ x₁.1 x₂.1 x₃.1)$
          show (((x₁.1+x₂.1) • x₃.2)+x₃.1 • x₁.2+x₂.2) = ((x₁.1 • x₃.2)+x₃.1 • x₁.2)+(x₂.1 • x₃.2)+x₃.1 • x₂.2by 
            simpRw [add_smul, smul_add, add_add_add_commₓ] }

/-- The canonical inclusion of rings `R → triv_sq_zero_ext R M`. -/
@[simps apply]
def inl_hom [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] : R →+* tsze R M :=
  { toFun := inl, map_one' := inl_one R M, map_mul' := inl_mul R M, map_zero' := inl_zero R M, map_add' := inl_add R M }

end Mul

section Algebra

variable (R : Type u) (M : Type v)

instance [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] : Algebra R (tsze R M) :=
  { TrivSqZeroExt.module R M, TrivSqZeroExt.inlHom R M with commutes' := fun r x => mul_commₓ _ _,
    smul_def' :=
      fun r x =>
        ext rfl$
          show r • x.2 = (r • x.2)+x.1 • 0 by 
            rw [smul_zero, add_zeroₓ] }

/-- The canonical `R`-algebra projection `triv_sq_zero_ext R M → R`. -/
def fst_hom [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] : tsze R M →ₐ[R] R :=
  { toFun := fst, map_one' := fst_one R M, map_mul' := fst_mul R M, map_zero' := fst_zero R M, map_add' := fst_add R M,
    commutes' := fst_inl }

/-- The canonical `R`-module projection `triv_sq_zero_ext R M → M`. -/
@[simps apply]
def snd_hom [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : tsze R M →ₗ[R] M :=
  { toFun := snd, map_add' := snd_add R M, map_smul' := snd_smul R M }

end Algebra

end TrivSqZeroExt

