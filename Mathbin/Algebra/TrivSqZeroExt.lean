/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.triv_sq_zero_ext
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.LinearAlgebra.Prod

/-!
# Trivial Square-Zero Extension

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.

## Main definitions

* `triv_sq_zero_ext.inl`, `triv_sq_zero_ext.inr`: the canonical inclusions into
  `triv_sq_zero_ext R M`.
* `triv_sq_zero_ext.fst`, `triv_sq_zero_ext.snd`: the canonical projections from
  `triv_sq_zero_ext R M`.
* `triv_sq_zero_ext.algebra`: the associated `R`-algebra structure.
* `triv_sq_zero_ext.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `triv_sq_zero_ext R M →ₐ[R] A` are uniquely defined by linear maps `M →ₗ[R] A` for
  which the product of any two elements in the range is zero.

-/


universe u v w

/-- "Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
def TrivSqZeroExt (R : Type u) (M : Type v) :=
  R × M
#align triv_sq_zero_ext TrivSqZeroExt

-- mathport name: exprtsze
local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Basic

variable {R : Type u} {M : Type v}

/-- The canonical inclusion `R → triv_sq_zero_ext R M`. -/
def inl [Zero M] (r : R) : tsze R M :=
  (r, 0)
#align triv_sq_zero_ext.inl TrivSqZeroExt.inl

/-- The canonical inclusion `M → triv_sq_zero_ext R M`. -/
def inr [Zero R] (m : M) : tsze R M :=
  (0, m)
#align triv_sq_zero_ext.inr TrivSqZeroExt.inr

/-- The canonical projection `triv_sq_zero_ext R M → R`. -/
def fst (x : tsze R M) : R :=
  x.1
#align triv_sq_zero_ext.fst TrivSqZeroExt.fst

/-- The canonical projection `triv_sq_zero_ext R M → M`. -/
def snd (x : tsze R M) : M :=
  x.2
#align triv_sq_zero_ext.snd TrivSqZeroExt.snd

@[simp]
theorem fst_mk (r : R) (m : M) : fst (r, m) = r :=
  rfl
#align triv_sq_zero_ext.fst_mk TrivSqZeroExt.fst_mk

@[simp]
theorem snd_mk (r : R) (m : M) : snd (r, m) = m :=
  rfl
#align triv_sq_zero_ext.snd_mk TrivSqZeroExt.snd_mk

@[ext]
theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2
#align triv_sq_zero_ext.ext TrivSqZeroExt.ext

section

variable (M)

@[simp]
theorem fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst = r :=
  rfl
#align triv_sq_zero_ext.fst_inl TrivSqZeroExt.fst_inl

@[simp]
theorem snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_inl TrivSqZeroExt.snd_inl

end

section

variable (R)

@[simp]
theorem fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst = 0 :=
  rfl
#align triv_sq_zero_ext.fst_inr TrivSqZeroExt.fst_inr

@[simp]
theorem snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd = m :=
  rfl
#align triv_sq_zero_ext.snd_inr TrivSqZeroExt.snd_inr

end

theorem inl_injective [Zero M] : Function.Injective (inl : R → tsze R M) :=
  Function.LeftInverse.injective <| fst_inl _
#align triv_sq_zero_ext.inl_injective TrivSqZeroExt.inl_injective

theorem inr_injective [Zero R] : Function.Injective (inr : M → tsze R M) :=
  Function.LeftInverse.injective <| snd_inr _
#align triv_sq_zero_ext.inr_injective TrivSqZeroExt.inr_injective

end Basic

/-! ### Structures inherited from `prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type _} {S : Type _} {R : Type u} {M : Type v}

instance [Inhabited R] [Inhabited M] : Inhabited (tsze R M) :=
  Prod.inhabited

instance [Zero R] [Zero M] : Zero (tsze R M) :=
  Prod.hasZero

instance [Add R] [Add M] : Add (tsze R M) :=
  Prod.hasAdd

instance [Neg R] [Neg M] : Neg (tsze R M) :=
  Prod.hasNeg

instance [AddSemigroup R] [AddSemigroup M] : AddSemigroup (tsze R M) :=
  Prod.addSemigroup

instance [AddZeroClass R] [AddZeroClass M] : AddZeroClass (tsze R M) :=
  Prod.addZeroClass

instance [AddMonoid R] [AddMonoid M] : AddMonoid (tsze R M) :=
  Prod.addMonoid

instance [AddGroup R] [AddGroup M] : AddGroup (tsze R M) :=
  Prod.addGroup

instance [AddCommSemigroup R] [AddCommSemigroup M] : AddCommSemigroup (tsze R M) :=
  Prod.addCommSemigroup

instance [AddCommMonoid R] [AddCommMonoid M] : AddCommMonoid (tsze R M) :=
  Prod.addCommMonoid

instance [AddCommGroup R] [AddCommGroup M] : AddCommGroup (tsze R M) :=
  Prod.addCommGroup

instance [HasSmul S R] [HasSmul S M] : HasSmul S (tsze R M) :=
  Prod.hasSmul

instance [HasSmul T R] [HasSmul T M] [HasSmul S R] [HasSmul S M] [HasSmul T S] [IsScalarTower T S R]
    [IsScalarTower T S M] : IsScalarTower T S (tsze R M) :=
  Prod.is_scalar_tower

instance [HasSmul T R] [HasSmul T M] [HasSmul S R] [HasSmul S M] [SMulCommClass T S R]
    [SMulCommClass T S M] : SMulCommClass T S (tsze R M) :=
  Prod.smul_comm_class

instance [HasSmul S R] [HasSmul S M] [HasSmul Sᵐᵒᵖ R] [HasSmul Sᵐᵒᵖ M] [IsCentralScalar S R]
    [IsCentralScalar S M] : IsCentralScalar S (tsze R M) :=
  Prod.is_central_scalar

instance [Monoid S] [MulAction S R] [MulAction S M] : MulAction S (tsze R M) :=
  Prod.mulAction

instance [Monoid S] [AddMonoid R] [AddMonoid M] [DistribMulAction S R] [DistribMulAction S M] :
    DistribMulAction S (tsze R M) :=
  Prod.distribMulAction

instance [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Module S M] :
    Module S (tsze R M) :=
  Prod.module

@[simp]
theorem fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst = 0 :=
  rfl
#align triv_sq_zero_ext.fst_zero TrivSqZeroExt.fst_zero

@[simp]
theorem snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_zero TrivSqZeroExt.snd_zero

@[simp]
theorem fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl
#align triv_sq_zero_ext.fst_add TrivSqZeroExt.fst_add

@[simp]
theorem snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl
#align triv_sq_zero_ext.snd_add TrivSqZeroExt.snd_add

@[simp]
theorem fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst :=
  rfl
#align triv_sq_zero_ext.fst_neg TrivSqZeroExt.fst_neg

@[simp]
theorem snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd :=
  rfl
#align triv_sq_zero_ext.snd_neg TrivSqZeroExt.snd_neg

@[simp]
theorem fst_smul [HasSmul S R] [HasSmul S M] (s : S) (x : tsze R M) : (s • x).fst = s • x.fst :=
  rfl
#align triv_sq_zero_ext.fst_smul TrivSqZeroExt.fst_smul

@[simp]
theorem snd_smul [HasSmul S R] [HasSmul S M] (s : S) (x : tsze R M) : (s • x).snd = s • x.snd :=
  rfl
#align triv_sq_zero_ext.snd_smul TrivSqZeroExt.snd_smul

section

variable (M)

@[simp]
theorem inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) = 0 :=
  rfl
#align triv_sq_zero_ext.inl_zero TrivSqZeroExt.inl_zero

@[simp]
theorem inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂ :=
  ext rfl (add_zero 0).symm
#align triv_sq_zero_ext.inl_add TrivSqZeroExt.inl_add

@[simp]
theorem inl_neg [Neg R] [AddGroup M] (r : R) : (inl (-r) : tsze R M) = -inl r :=
  ext rfl neg_zero.symm
#align triv_sq_zero_ext.inl_neg TrivSqZeroExt.inl_neg

@[simp]
theorem inl_smul [Monoid S] [AddMonoid M] [HasSmul S R] [DistribMulAction S M] (s : S) (r : R) :
    (inl (s • r) : tsze R M) = s • inl r :=
  ext rfl (smul_zero s).symm
#align triv_sq_zero_ext.inl_smul TrivSqZeroExt.inl_smul

end

section

variable (R)

@[simp]
theorem inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) = 0 :=
  rfl
#align triv_sq_zero_ext.inr_zero TrivSqZeroExt.inr_zero

@[simp]
theorem inr_add [AddZeroClass R] [AddZeroClass M] (m₁ m₂ : M) :
    (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
  ext (add_zero 0).symm rfl
#align triv_sq_zero_ext.inr_add TrivSqZeroExt.inr_add

@[simp]
theorem inr_neg [AddGroup R] [Neg M] (m : M) : (inr (-m) : tsze R M) = -inr m :=
  ext neg_zero.symm rfl
#align triv_sq_zero_ext.inr_neg TrivSqZeroExt.inr_neg

@[simp]
theorem inr_smul [Zero R] [Zero S] [SMulWithZero S R] [HasSmul S M] (r : S) (m : M) :
    (inr (r • m) : tsze R M) = r • inr m :=
  ext (smul_zero _).symm rfl
#align triv_sq_zero_ext.inr_smul TrivSqZeroExt.inr_smul

end

theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass M] (x : tsze R M) :
    inl x.fst + inr x.snd = x :=
  ext (add_zero x.1) (zero_add x.2)
#align triv_sq_zero_ext.inl_fst_add_inr_snd_eq TrivSqZeroExt.inl_fst_add_inr_snd_eq

/-- To show a property hold on all `triv_sq_zero_ext R M` it suffices to show it holds
on terms of the form `inl r + inr m`.

This can be used as `induction x using triv_sq_zero_ext.ind`. -/
theorem ind {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M → Prop}
    (h : ∀ r m, P (inl r + inr m)) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ h x.1 x.2
#align triv_sq_zero_ext.ind TrivSqZeroExt.ind

/-- This cannot be marked `@[ext]` as it ends up being used instead of `linear_map.prod_ext` when
working with `R × M`. -/
theorem linear_map_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
    [Module S R] [Module S M] [Module S N] ⦃f g : tsze R M →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ m, f (inr m) = g (inr m)) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)
#align triv_sq_zero_ext.linear_map_ext TrivSqZeroExt.linear_map_ext

variable (R M)

/-- The canonical `R`-linear inclusion `M → triv_sq_zero_ext R M`. -/
@[simps apply]
def inrHom [Semiring R] [AddCommMonoid M] [Module R M] : M →ₗ[R] tsze R M :=
  { LinearMap.inr R R M with toFun := inr }
#align triv_sq_zero_ext.inr_hom TrivSqZeroExt.inrHom

/-- The canonical `R`-linear projection `triv_sq_zero_ext R M → M`. -/
@[simps apply]
def sndHom [Semiring R] [AddCommMonoid M] [Module R M] : tsze R M →ₗ[R] M :=
  { LinearMap.snd _ _ _ with toFun := snd }
#align triv_sq_zero_ext.snd_hom TrivSqZeroExt.sndHom

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R : Type u} {M : Type v}

instance [One R] [Zero M] : One (tsze R M) :=
  ⟨(1, 0)⟩

instance [Mul R] [Add M] [HasSmul R M] : Mul (tsze R M) :=
  ⟨fun x y => (x.1 * y.1, x.1 • y.2 + y.1 • x.2)⟩

@[simp]
theorem fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1 :=
  rfl
#align triv_sq_zero_ext.fst_one TrivSqZeroExt.fst_one

@[simp]
theorem snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0 :=
  rfl
#align triv_sq_zero_ext.snd_one TrivSqZeroExt.snd_one

@[simp]
theorem fst_mul [Mul R] [Add M] [HasSmul R M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl
#align triv_sq_zero_ext.fst_mul TrivSqZeroExt.fst_mul

@[simp]
theorem snd_mul [Mul R] [Add M] [HasSmul R M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd :=
  rfl
#align triv_sq_zero_ext.snd_mul TrivSqZeroExt.snd_mul

section

variable (M)

@[simp]
theorem inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1 :=
  rfl
#align triv_sq_zero_ext.inl_one TrivSqZeroExt.inl_one

@[simp]
theorem inl_mul [Monoid R] [AddMonoid M] [DistribMulAction R M] (r₁ r₂ : R) :
    (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂ :=
  ext rfl <| show (0 : M) = r₁ • 0 + r₂ • 0 by rw [smul_zero, zero_add, smul_zero]
#align triv_sq_zero_ext.inl_mul TrivSqZeroExt.inl_mul

theorem inl_mul_inl [Monoid R] [AddMonoid M] [DistribMulAction R M] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂) :=
  (inl_mul M r₁ r₂).symm
#align triv_sq_zero_ext.inl_mul_inl TrivSqZeroExt.inl_mul_inl

end

section

variable (R)

@[simp]
theorem inr_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] (m₁ m₂ : M) :
    (inr m₁ * inr m₂ : tsze R M) = 0 :=
  ext (mul_zero _) <| show (0 : R) • m₂ + (0 : R) • m₁ = 0 by rw [zero_smul, zero_add, zero_smul]
#align triv_sq_zero_ext.inr_mul_inr TrivSqZeroExt.inr_mul_inr

end

theorem inl_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] (r : R) (m : M) :
    (inl r * inr m : tsze R M) = inr (r • m) :=
  ext (mul_zero r) <| show r • m + (0 : R) • 0 = r • m by rw [smul_zero, add_zero]
#align triv_sq_zero_ext.inl_mul_inr TrivSqZeroExt.inl_mul_inr

theorem inr_mul_inl [Semiring R] [AddCommMonoid M] [Module R M] (r : R) (m : M) :
    (inr m * inl r : tsze R M) = inr (r • m) :=
  ext (zero_mul r) <| show (0 : R) • 0 + r • m = r • m by rw [smul_zero, zero_add]
#align triv_sq_zero_ext.inr_mul_inl TrivSqZeroExt.inr_mul_inl

instance [Monoid R] [AddMonoid M] [DistribMulAction R M] : MulOneClass (tsze R M) :=
  { TrivSqZeroExt.hasOne,
    TrivSqZeroExt.hasMul with
    one_mul := fun x =>
      ext (one_mul x.1) <| show (1 : R) • x.2 + x.1 • 0 = x.2 by rw [one_smul, smul_zero, add_zero]
    mul_one := fun x =>
      ext (mul_one x.1) <|
        show (x.1 • 0 : M) + (1 : R) • x.2 = x.2 by rw [smul_zero, zero_add, one_smul] }

instance [AddMonoidWithOne R] [AddMonoid M] : AddMonoidWithOne (tsze R M) :=
  { TrivSqZeroExt.addMonoid,
    TrivSqZeroExt.hasOne with
    natCast := fun n => (n, 0)
    nat_cast_zero := by simp [Nat.cast]
    nat_cast_succ := fun _ => by ext <;> simp [Nat.cast] }

instance [Semiring R] [AddCommMonoid M] [Module R M] : NonAssocSemiring (tsze R M) :=
  { TrivSqZeroExt.addMonoidWithOne, TrivSqZeroExt.mulOneClass,
    TrivSqZeroExt.addCommMonoid with
    zero_mul := fun x =>
      ext (zero_mul x.1) <| show (0 : R) • x.2 + x.1 • 0 = 0 by rw [zero_smul, zero_add, smul_zero]
    mul_zero := fun x =>
      ext (mul_zero x.1) <|
        show (x.1 • 0 : M) + (0 : R) • x.2 = 0 by rw [smul_zero, zero_add, zero_smul]
    left_distrib := fun x₁ x₂ x₃ =>
      ext (mul_add x₁.1 x₂.1 x₃.1) <|
        show
          x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 =
            x₁.1 • x₂.2 + x₂.1 • x₁.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2)
          by simp_rw [smul_add, add_smul, add_add_add_comm]
    right_distrib := fun x₁ x₂ x₃ =>
      ext (add_mul x₁.1 x₂.1 x₃.1) <|
        show
          (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) =
            x₁.1 • x₃.2 + x₃.1 • x₁.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2)
          by simp_rw [add_smul, smul_add, add_add_add_comm] }

instance [CommMonoid R] [AddMonoid M] [DistribMulAction R M] : Monoid (tsze R M) :=
  { TrivSqZeroExt.mulOneClass with
    mul_assoc := fun x y z =>
      ext (mul_assoc x.1 y.1 z.1) <|
        show
          (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2) =
            x.1 • (y.1 • z.2 + z.1 • y.2) + (y.1 * z.1) • x.2
          by simp_rw [smul_add, ← mul_smul, add_assoc, mul_comm] }

instance [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M] : CommMonoid (tsze R M) :=
  { TrivSqZeroExt.monoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 • x₂.2 + x₂.1 • x₁.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2 from add_comm _ _ }

instance [CommSemiring R] [AddCommMonoid M] [Module R M] : CommSemiring (tsze R M) :=
  { TrivSqZeroExt.commMonoid, TrivSqZeroExt.nonAssocSemiring with }

variable (R M)

/-- The canonical inclusion of rings `R → triv_sq_zero_ext R M`. -/
@[simps apply]
def inlHom [Semiring R] [AddCommMonoid M] [Module R M] : R →+* tsze R M
    where
  toFun := inl
  map_one' := inl_one M
  map_mul' := inl_mul M
  map_zero' := inl_zero M
  map_add' := inl_add M
#align triv_sq_zero_ext.inl_hom TrivSqZeroExt.inlHom

end Mul

section Algebra

variable (S : Type _) (R : Type u) (M : Type v)

variable [CommSemiring S] [CommSemiring R] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [IsScalarTower S R M]

instance algebra' : Algebra S (tsze R M) :=
  {
    (TrivSqZeroExt.inlHom R M).comp
      (algebraMap S R) with
    commutes' := fun r x => mul_comm _ _
    smul_def' := fun r x =>
      ext (Algebra.smul_def _ _) <|
        show r • x.2 = algebraMap S R r • x.2 + x.1 • 0 by
          rw [smul_zero, add_zero, algebra_map_smul] }
#align triv_sq_zero_ext.algebra' TrivSqZeroExt.algebra'

-- shortcut instance for the common case
instance : Algebra R (tsze R M) :=
  TrivSqZeroExt.algebra' _ _ _

theorem algebra_map_eq_inl : ⇑(algebraMap R (tsze R M)) = inl :=
  rfl
#align triv_sq_zero_ext.algebra_map_eq_inl TrivSqZeroExt.algebra_map_eq_inl

theorem algebra_map_eq_inl_hom : algebraMap R (tsze R M) = inlHom R M :=
  rfl
#align triv_sq_zero_ext.algebra_map_eq_inl_hom TrivSqZeroExt.algebra_map_eq_inl_hom

theorem algebra_map_eq_inl' (s : S) : algebraMap S (tsze R M) s = inl (algebraMap S R s) :=
  rfl
#align triv_sq_zero_ext.algebra_map_eq_inl' TrivSqZeroExt.algebra_map_eq_inl'

/-- The canonical `R`-algebra projection `triv_sq_zero_ext R M → R`. -/
@[simps]
def fstHom : tsze R M →ₐ[R] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero
  map_add' := fst_add
  commutes' := fst_inl M
#align triv_sq_zero_ext.fst_hom TrivSqZeroExt.fstHom

variable {R S M}

theorem alg_hom_ext {A} [Semiring A] [Algebra R A] ⦃f g : tsze R M →ₐ[R] A⦄
    (h : ∀ m, f (inr m) = g (inr m)) : f = g :=
  AlgHom.to_linear_map_injective <|
    linear_map_ext (fun r => (f.commutes _).trans (g.commutes _).symm) h
#align triv_sq_zero_ext.alg_hom_ext TrivSqZeroExt.alg_hom_ext

@[ext]
theorem alg_hom_ext' {A} [Semiring A] [Algebra R A] ⦃f g : tsze R M →ₐ[R] A⦄
    (h : f.toLinearMap.comp (inrHom R M) = g.toLinearMap.comp (inrHom R M)) : f = g :=
  alg_hom_ext <| LinearMap.congr_fun h
#align triv_sq_zero_ext.alg_hom_ext' TrivSqZeroExt.alg_hom_ext'

variable {A : Type _} [Semiring A] [Algebra R A]

/-- There is an alg_hom from the trivial square zero extension to any `R`-algebra with a submodule
whose products are all zero.

See `triv_sq_zero_ext.lift` for this as an equiv. -/
def liftAux (f : M →ₗ[R] A) (hf : ∀ x y, f x * f y = 0) : tsze R M →ₐ[R] A :=
  AlgHom.ofLinearMap ((Algebra.linearMap _ _).comp (fstHom R M).toLinearMap + f.comp (sndHom R M))
    (show algebraMap R _ 1 + f (0 : M) = 1 by rw [map_zero, map_one, add_zero])
    (TrivSqZeroExt.ind fun r₁ m₁ =>
      TrivSqZeroExt.ind fun r₂ m₂ => by
        dsimp
        simp only [add_zero, zero_add, add_mul, mul_add, smul_mul_smul, hf, smul_zero]
        rw [← RingHom.map_mul, LinearMap.map_add, ← Algebra.commutes _ (f _), ← Algebra.smul_def, ←
          Algebra.smul_def, add_right_comm, add_assoc, LinearMap.map_smul, LinearMap.map_smul])
#align triv_sq_zero_ext.lift_aux TrivSqZeroExt.liftAux

@[simp]
theorem lift_aux_apply_inr (f : M →ₗ[R] A) (hf : ∀ x y, f x * f y = 0) (m : M) :
    liftAux f hf (inr m) = f m :=
  show algebraMap R A 0 + f m = f m by rw [RingHom.map_zero, zero_add]
#align triv_sq_zero_ext.lift_aux_apply_inr TrivSqZeroExt.lift_aux_apply_inr

@[simp]
theorem lift_aux_comp_inr_hom (f : M →ₗ[R] A) (hf : ∀ x y, f x * f y = 0) :
    (liftAux f hf).toLinearMap.comp (inrHom R M) = f :=
  LinearMap.ext <| lift_aux_apply_inr f hf
#align triv_sq_zero_ext.lift_aux_comp_inr_hom TrivSqZeroExt.lift_aux_comp_inr_hom

-- When applied to `inr` itself, `lift_aux` is the identity.
@[simp]
theorem lift_aux_inr_hom : liftAux (inrHom R M) (inr_mul_inr R) = AlgHom.id R (tsze R M) :=
  alg_hom_ext' <| lift_aux_comp_inr_hom _ _
#align triv_sq_zero_ext.lift_aux_inr_hom TrivSqZeroExt.lift_aux_inr_hom

/-- A universal property of the trivial square-zero extension, providing a unique
`triv_sq_zero_ext R M →ₐ[R] A` for every linear map `M →ₗ[R] A` whose range has no non-zero
products.

This isomorphism is named to match the very similar `complex.lift`. -/
@[simps]
def lift : { f : M →ₗ[R] A // ∀ x y, f x * f y = 0 } ≃ (tsze R M →ₐ[R] A)
    where
  toFun f := liftAux f f.Prop
  invFun F :=
    ⟨F.toLinearMap.comp (inrHom R M), fun x y =>
      (F.map_mul _ _).symm.trans <| (F.congr_arg <| inr_mul_inr _ _ _).trans F.map_zero⟩
  left_inv f := Subtype.ext <| lift_aux_comp_inr_hom _ _
  right_inv F := alg_hom_ext' <| lift_aux_comp_inr_hom _ _
#align triv_sq_zero_ext.lift TrivSqZeroExt.lift

end Algebra

end TrivSqZeroExt

