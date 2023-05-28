/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.algebra.equiv
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Hom

/-!
# Isomorphisms of `R`-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled isomorphisms of `R`-algebras.

## Main definitions

* `alg_equiv R A B`: the type of `R`-algebra isomorphisms between `A` and `B`.

## Notations

* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/


open BigOperators

universe u v w u₁ v₁

#print AlgEquiv /-
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  commutes' : ∀ r : R, to_fun (algebraMap R A r) = algebraMap R B r
#align alg_equiv AlgEquiv
-/

attribute [nolint doc_blame] AlgEquiv.toRingEquiv

attribute [nolint doc_blame] AlgEquiv.toEquiv

attribute [nolint doc_blame] AlgEquiv.toAddEquiv

attribute [nolint doc_blame] AlgEquiv.toMulEquiv

-- mathport name: «expr ≃ₐ[ ] »
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

#print AlgEquivClass /-
/-- `alg_equiv_class F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `alg_equiv`. -/
class AlgEquivClass (F : Type _) (R A B : outParam (Type _)) [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] extends RingEquivClass F A B where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
#align alg_equiv_class AlgEquivClass
-/

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] AlgEquivClass.toRingEquivClass

namespace AlgEquivClass

#print AlgEquivClass.toAlgHomClass /-
-- See note [lower instance priority]
instance (priority := 100) toAlgHomClass (F R A B : Type _) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [h : AlgEquivClass F R A B] : AlgHomClass F R A B :=
  { h with
    coe := coeFn
    coe_injective' := FunLike.coe_injective
    map_zero := map_zero
    map_one := map_one }
#align alg_equiv_class.to_alg_hom_class AlgEquivClass.toAlgHomClass
-/

#print AlgEquivClass.toLinearEquivClass /-
instance (priority := 100) toLinearEquivClass (F R A B : Type _) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [h : AlgEquivClass F R A B] :
    LinearEquivClass F R A B :=
  { h with map_smulₛₗ := fun f => map_smulₛₗ f }
#align alg_equiv_class.to_linear_equiv_class AlgEquivClass.toLinearEquivClass
-/

instance (F R A B : Type _) [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [h : AlgEquivClass F R A B] : CoeTC F (A ≃ₐ[R] B)
    where coe f :=
    { (f : A ≃+* B) with
      toFun := f
      invFun := EquivLike.inv f
      commutes' := AlgHomClass.commutes f }

end AlgEquivClass

namespace AlgEquiv

variable {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁}

section Semiring

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable (e : A₁ ≃ₐ[R] A₂)

instance : AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂
    where
  coe := toFun
  inv := invFun
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr
  map_add := map_add'
  map_mul := map_mul'
  commutes := commutes'
  left_inv := left_inv
  right_inv := right_inv

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : CoeFun (A₁ ≃ₐ[R] A₂) fun _ => A₁ → A₂ :=
  ⟨AlgEquiv.toFun⟩

/- warning: alg_equiv.coe_coe -> AlgEquiv.coe_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_coe AlgEquiv.coe_coeₓ'. -/
@[simp, protected]
theorem coe_coe {F : Type _} [AlgEquivClass F R A₁ A₂] (f : F) : ⇑(f : A₁ ≃ₐ[R] A₂) = f :=
  rfl
#align alg_equiv.coe_coe AlgEquiv.coe_coe

/- warning: alg_equiv.ext -> AlgEquiv.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.ext AlgEquiv.extₓ'. -/
@[ext]
theorem ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align alg_equiv.ext AlgEquiv.ext

/- warning: alg_equiv.congr_arg -> AlgEquiv.congr_arg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.congr_arg AlgEquiv.congr_argₓ'. -/
protected theorem congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' → f x = f x' :=
  FunLike.congr_arg f
#align alg_equiv.congr_arg AlgEquiv.congr_arg

/- warning: alg_equiv.congr_fun -> AlgEquiv.congr_fun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.congr_fun AlgEquiv.congr_funₓ'. -/
protected theorem congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
  FunLike.congr_fun h x
#align alg_equiv.congr_fun AlgEquiv.congr_fun

/- warning: alg_equiv.ext_iff -> AlgEquiv.ext_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.ext_iff AlgEquiv.ext_iffₓ'. -/
protected theorem ext_iff {f g : A₁ ≃ₐ[R] A₂} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align alg_equiv.ext_iff AlgEquiv.ext_iff

/- warning: alg_equiv.coe_fun_injective -> AlgEquiv.coe_fun_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_fun_injective AlgEquiv.coe_fun_injectiveₓ'. -/
theorem coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) fun e => (e : A₁ → A₂) :=
  FunLike.coe_injective
#align alg_equiv.coe_fun_injective AlgEquiv.coe_fun_injective

/- warning: alg_equiv.has_coe_to_ring_equiv -> AlgEquiv.hasCoeToRingEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} {A₂ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_3 : Semiring.{u3} A₂] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2] [_inst_6 : Algebra.{u1, u3} R A₂ _inst_1 _inst_3], Coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AlgEquiv.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) (RingEquiv.{u2, u3} A₁ A₂ (Distrib.toHasMul.{u2} A₁ (NonUnitalNonAssocSemiring.toDistrib.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (Distrib.toHasAdd.{u2} A₁ (NonUnitalNonAssocSemiring.toDistrib.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (Distrib.toHasMul.{u3} A₂ (NonUnitalNonAssocSemiring.toDistrib.{u3} A₂ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A₂ (Semiring.toNonAssocSemiring.{u3} A₂ _inst_3)))) (Distrib.toHasAdd.{u3} A₂ (NonUnitalNonAssocSemiring.toDistrib.{u3} A₂ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A₂ (Semiring.toNonAssocSemiring.{u3} A₂ _inst_3)))))
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} {A₂ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_3 : Semiring.{u3} A₂] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2] [_inst_6 : Algebra.{u1, u3} R A₂ _inst_1 _inst_3], CoeOut.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (AlgEquiv.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) (RingEquiv.{u2, u3} A₁ A₂ (NonUnitalNonAssocSemiring.toMul.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))) (NonUnitalNonAssocSemiring.toMul.{u3} A₂ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A₂ (Semiring.toNonAssocSemiring.{u3} A₂ _inst_3))) (Distrib.toAdd.{u2} A₁ (NonUnitalNonAssocSemiring.toDistrib.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (Distrib.toAdd.{u3} A₂ (NonUnitalNonAssocSemiring.toDistrib.{u3} A₂ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A₂ (Semiring.toNonAssocSemiring.{u3} A₂ _inst_3)))))
Case conversion may be inaccurate. Consider using '#align alg_equiv.has_coe_to_ring_equiv AlgEquiv.hasCoeToRingEquivₓ'. -/
instance hasCoeToRingEquiv : Coe (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) :=
  ⟨AlgEquiv.toRingEquiv⟩
#align alg_equiv.has_coe_to_ring_equiv AlgEquiv.hasCoeToRingEquiv

/- warning: alg_equiv.coe_mk -> AlgEquiv.coe_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_mk AlgEquiv.coe_mkₓ'. -/
@[simp]
theorem coe_mk {to_fun inv_fun left_inv right_inv map_mul map_add commutes} :
    ⇑(⟨to_fun, inv_fun, left_inv, right_inv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = to_fun :=
  rfl
#align alg_equiv.coe_mk AlgEquiv.coe_mk

/- warning: alg_equiv.mk_coe -> AlgEquiv.mk_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.mk_coe AlgEquiv.mk_coeₓ'. -/
@[simp]
theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨e, e', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e :=
  ext fun _ => rfl
#align alg_equiv.mk_coe AlgEquiv.mk_coe

/- warning: alg_equiv.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
warning: alg_equiv.to_fun_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} {A₁ : Type.{v}} {A₂ : Type.{w}} [_inst_1 : CommSemiring.{u} R] [_inst_2 : Semiring.{v} A₁] [_inst_3 : Semiring.{w} A₂] [_inst_5 : Algebra.{u, v} R A₁ _inst_1 _inst_2] [_inst_6 : Algebra.{u, w} R A₂ _inst_1 _inst_3] (e : AlgEquiv.{u, v, w} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6), Eq.{max (succ v) (succ w)} (A₁ -> A₂) (AlgEquiv.toFun.{u, v, w} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 e) (coeFn.{max (succ v) (succ w), max (succ v) (succ w)} (AlgEquiv.{u, v, w} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) (fun (_x : AlgEquiv.{u, v, w} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) => A₁ -> A₂) (AlgEquiv.hasCoeToFun.{u, v, w} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) e)
but is expected to have type
  forall {R : Type.{u}} {A₁ : Type.{v}}, (Nat -> R -> A₁) -> Nat -> (List.{u} R) -> (List.{v} A₁)
Case conversion may be inaccurate. Consider using '#align alg_equiv.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (e : A₁ ≃ₐ[R] A₂) : e.toFun = e :=
  rfl
#align alg_equiv.to_fun_eq_coe [anonymous]

#print AlgEquiv.toEquiv_eq_coe /-
@[simp]
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl
#align alg_equiv.to_equiv_eq_coe AlgEquiv.toEquiv_eq_coe
-/

/- warning: alg_equiv.to_ring_equiv_eq_coe -> AlgEquiv.toRingEquiv_eq_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.to_ring_equiv_eq_coe AlgEquiv.toRingEquiv_eq_coeₓ'. -/
@[simp]
theorem toRingEquiv_eq_coe : e.toRingEquiv = e :=
  rfl
#align alg_equiv.to_ring_equiv_eq_coe AlgEquiv.toRingEquiv_eq_coe

#print AlgEquiv.coe_ringEquiv /-
@[simp, norm_cast]
theorem coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e :=
  rfl
#align alg_equiv.coe_ring_equiv AlgEquiv.coe_ringEquiv
-/

#print AlgEquiv.coe_ringEquiv' /-
theorem coe_ringEquiv' : (e.toRingEquiv : A₁ → A₂) = e :=
  rfl
#align alg_equiv.coe_ring_equiv' AlgEquiv.coe_ringEquiv'
-/

#print AlgEquiv.coe_ringEquiv_injective /-
theorem coe_ringEquiv_injective : Function.Injective (coe : (A₁ ≃ₐ[R] A₂) → A₁ ≃+* A₂) :=
  fun e₁ e₂ h => ext <| RingEquiv.congr_fun h
#align alg_equiv.coe_ring_equiv_injective AlgEquiv.coe_ringEquiv_injective
-/

/- warning: alg_equiv.map_add -> AlgEquiv.map_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_add AlgEquiv.map_addₓ'. -/
protected theorem map_add : ∀ x y, e (x + y) = e x + e y :=
  map_add e
#align alg_equiv.map_add AlgEquiv.map_add

/- warning: alg_equiv.map_zero -> AlgEquiv.map_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_zero AlgEquiv.map_zeroₓ'. -/
protected theorem map_zero : e 0 = 0 :=
  map_zero e
#align alg_equiv.map_zero AlgEquiv.map_zero

/- warning: alg_equiv.map_mul -> AlgEquiv.map_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_mul AlgEquiv.map_mulₓ'. -/
protected theorem map_mul : ∀ x y, e (x * y) = e x * e y :=
  map_mul e
#align alg_equiv.map_mul AlgEquiv.map_mul

/- warning: alg_equiv.map_one -> AlgEquiv.map_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_one AlgEquiv.map_oneₓ'. -/
protected theorem map_one : e 1 = 1 :=
  map_one e
#align alg_equiv.map_one AlgEquiv.map_one

/- warning: alg_equiv.commutes -> AlgEquiv.commutes is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.commutes AlgEquiv.commutesₓ'. -/
@[simp]
theorem commutes : ∀ r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r :=
  e.commutes'
#align alg_equiv.commutes AlgEquiv.commutes

/- warning: alg_equiv.map_smul -> AlgEquiv.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_smul AlgEquiv.map_smulₓ'. -/
@[simp]
theorem map_smul (r : R) (x : A₁) : e (r • x) = r • e x := by
  simp only [Algebra.smul_def, map_mul, commutes]
#align alg_equiv.map_smul AlgEquiv.map_smul

/- warning: alg_equiv.map_sum -> AlgEquiv.map_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_sum AlgEquiv.map_sumₓ'. -/
theorem map_sum {ι : Type _} (f : ι → A₁) (s : Finset ι) : e (∑ x in s, f x) = ∑ x in s, e (f x) :=
  e.toAddEquiv.map_sum f s
#align alg_equiv.map_sum AlgEquiv.map_sum

/- warning: alg_equiv.map_finsupp_sum -> AlgEquiv.map_finsupp_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_finsupp_sum AlgEquiv.map_finsupp_sumₓ'. -/
theorem map_finsupp_sum {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A₁) :
    e (f.Sum g) = f.Sum fun i b => e (g i b) :=
  e.map_sum _ _
#align alg_equiv.map_finsupp_sum AlgEquiv.map_finsupp_sum

#print AlgEquiv.toAlgHom /-
/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to_*_hom` projections.
The `simp` normal form is to use the coercion of the `alg_hom_class.has_coe_t` instance. -/
def toAlgHom : A₁ →ₐ[R] A₂ :=
  { e with
    map_one' := e.map_one
    map_zero' := e.map_zero }
#align alg_equiv.to_alg_hom AlgEquiv.toAlgHom
-/

/- warning: alg_equiv.to_alg_hom_eq_coe -> AlgEquiv.toAlgHom_eq_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.to_alg_hom_eq_coe AlgEquiv.toAlgHom_eq_coeₓ'. -/
@[simp]
theorem toAlgHom_eq_coe : e.toAlgHom = e :=
  rfl
#align alg_equiv.to_alg_hom_eq_coe AlgEquiv.toAlgHom_eq_coe

#print AlgEquiv.coe_algHom /-
@[simp, norm_cast]
theorem coe_algHom : ((e : A₁ →ₐ[R] A₂) : A₁ → A₂) = e :=
  rfl
#align alg_equiv.coe_alg_hom AlgEquiv.coe_algHom
-/

/- warning: alg_equiv.coe_alg_hom_injective -> AlgEquiv.coe_algHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_alg_hom_injective AlgEquiv.coe_algHom_injectiveₓ'. -/
theorem coe_algHom_injective : Function.Injective (coe : (A₁ ≃ₐ[R] A₂) → A₁ →ₐ[R] A₂) :=
  fun e₁ e₂ h => ext <| AlgHom.congr_fun h
#align alg_equiv.coe_alg_hom_injective AlgEquiv.coe_algHom_injective

/- warning: alg_equiv.coe_ring_hom_commutes -> AlgEquiv.coe_ringHom_commutes is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_ring_hom_commutes AlgEquiv.coe_ringHom_commutesₓ'. -/
/-- The two paths coercion can take to a `ring_hom` are equivalent -/
theorem coe_ringHom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
  rfl
#align alg_equiv.coe_ring_hom_commutes AlgEquiv.coe_ringHom_commutes

/- warning: alg_equiv.map_pow -> AlgEquiv.map_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_pow AlgEquiv.map_powₓ'. -/
protected theorem map_pow : ∀ (x : A₁) (n : ℕ), e (x ^ n) = e x ^ n :=
  map_pow _
#align alg_equiv.map_pow AlgEquiv.map_pow

/- warning: alg_equiv.injective -> AlgEquiv.injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.injective AlgEquiv.injectiveₓ'. -/
protected theorem injective : Function.Injective e :=
  EquivLike.injective e
#align alg_equiv.injective AlgEquiv.injective

/- warning: alg_equiv.surjective -> AlgEquiv.surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.surjective AlgEquiv.surjectiveₓ'. -/
protected theorem surjective : Function.Surjective e :=
  EquivLike.surjective e
#align alg_equiv.surjective AlgEquiv.surjective

/- warning: alg_equiv.bijective -> AlgEquiv.bijective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.bijective AlgEquiv.bijectiveₓ'. -/
protected theorem bijective : Function.Bijective e :=
  EquivLike.bijective e
#align alg_equiv.bijective AlgEquiv.bijective

#print AlgEquiv.refl /-
/-- Algebra equivalences are reflexive. -/
@[refl]
def refl : A₁ ≃ₐ[R] A₁ :=
  { (1 : A₁ ≃+* A₁) with commutes' := fun r => rfl }
#align alg_equiv.refl AlgEquiv.refl
-/

instance : Inhabited (A₁ ≃ₐ[R] A₁) :=
  ⟨refl⟩

/- warning: alg_equiv.refl_to_alg_hom -> AlgEquiv.refl_toAlgHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], Eq.{succ u2} (AlgHom.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgHom.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (HasLiftT.mk.{succ u2, succ u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgHom.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (CoeTCₓ.coe.{succ u2, succ u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgHom.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgHomClass.coeTC.{u1, u2, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquivClass.toAlgHomClass.{u2, u1, u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgEquiv.algEquivClass.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5))))) (AlgEquiv.refl.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)) (AlgHom.id.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], Eq.{succ u2} (AlgHom.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgHomClass.toAlgHom.{u1, u2, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquivClass.toAlgHomClass.{u2, u1, u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgEquiv.instAlgEquivClassAlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5)) (AlgEquiv.refl.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)) (AlgHom.id.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)
Case conversion may be inaccurate. Consider using '#align alg_equiv.refl_to_alg_hom AlgEquiv.refl_toAlgHomₓ'. -/
@[simp]
theorem refl_toAlgHom : ↑(refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁ :=
  rfl
#align alg_equiv.refl_to_alg_hom AlgEquiv.refl_toAlgHom

/- warning: alg_equiv.coe_refl -> AlgEquiv.coe_refl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_refl AlgEquiv.coe_reflₓ'. -/
@[simp]
theorem coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id :=
  rfl
#align alg_equiv.coe_refl AlgEquiv.coe_refl

#print AlgEquiv.symm /-
/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := fun r =>
      by
      rw [← e.to_ring_equiv.symm_apply_apply (algebraMap R A₁ r)]; congr
      change _ = e _; rw [e.commutes] }
#align alg_equiv.symm AlgEquiv.symm
-/

#print AlgEquiv.Simps.symm_apply /-
/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ :=
  e.symm
#align alg_equiv.simps.symm_apply AlgEquiv.Simps.symm_apply
-/

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symm_apply)

/- warning: alg_equiv.coe_apply_coe_coe_symm_apply -> AlgEquiv.coe_apply_coe_coe_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_apply_coe_coe_symm_apply AlgEquiv.coe_apply_coe_coe_symm_applyₓ'. -/
@[simp]
theorem coe_apply_coe_coe_symm_apply {F : Type _} [AlgEquivClass F R A₁ A₂] (f : F) (x : A₂) :
    f ((f : A₁ ≃ₐ[R] A₂).symm x) = x :=
  EquivLike.right_inv f x
#align alg_equiv.coe_apply_coe_coe_symm_apply AlgEquiv.coe_apply_coe_coe_symm_apply

/- warning: alg_equiv.coe_coe_symm_apply_coe_apply -> AlgEquiv.coe_coe_symm_apply_coe_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_coe_symm_apply_coe_apply AlgEquiv.coe_coe_symm_apply_coe_applyₓ'. -/
@[simp]
theorem coe_coe_symm_apply_coe_apply {F : Type _} [AlgEquivClass F R A₁ A₂] (f : F) (x : A₁) :
    (f : A₁ ≃ₐ[R] A₂).symm (f x) = x :=
  EquivLike.left_inv f x
#align alg_equiv.coe_coe_symm_apply_coe_apply AlgEquiv.coe_coe_symm_apply_coe_apply

/- warning: alg_equiv.inv_fun_eq_symm -> AlgEquiv.invFun_eq_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.inv_fun_eq_symm AlgEquiv.invFun_eq_symmₓ'. -/
@[simp]
theorem invFun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.invFun = e.symm :=
  rfl
#align alg_equiv.inv_fun_eq_symm AlgEquiv.invFun_eq_symm

#print AlgEquiv.symm_symm /-
@[simp]
theorem symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e := by ext; rfl
#align alg_equiv.symm_symm AlgEquiv.symm_symm
-/

#print AlgEquiv.symm_bijective /-
theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) :=
  Equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩
#align alg_equiv.symm_bijective AlgEquiv.symm_bijective
-/

/- warning: alg_equiv.mk_coe' -> AlgEquiv.mk_coe' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.mk_coe' AlgEquiv.mk_coe'ₓ'. -/
@[simp]
theorem mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨f, e, h₁, h₂, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
  symm_bijective.Injective <| ext fun x => rfl
#align alg_equiv.mk_coe' AlgEquiv.mk_coe'

/- warning: alg_equiv.symm_mk -> AlgEquiv.symm_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.symm_mk AlgEquiv.symm_mkₓ'. -/
@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
      {
        (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ :
            A₁ ≃ₐ[R] A₂).symm with
        toFun := f'
        invFun := f } :=
  rfl
#align alg_equiv.symm_mk AlgEquiv.symm_mk

#print AlgEquiv.refl_symm /-
@[simp]
theorem refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl :=
  rfl
#align alg_equiv.refl_symm AlgEquiv.refl_symm
-/

/- warning: alg_equiv.to_ring_equiv_symm -> AlgEquiv.toRingEquiv_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.to_ring_equiv_symm AlgEquiv.toRingEquiv_symmₓ'. -/
--this should be a simp lemma but causes a lint timeout
theorem toRingEquiv_symm (f : A₁ ≃ₐ[R] A₁) : (f : A₁ ≃+* A₁).symm = f.symm :=
  rfl
#align alg_equiv.to_ring_equiv_symm AlgEquiv.toRingEquiv_symm

/- warning: alg_equiv.symm_to_ring_equiv -> AlgEquiv.symm_toRingEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.symm_to_ring_equiv AlgEquiv.symm_toRingEquivₓ'. -/
@[simp]
theorem symm_toRingEquiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm :=
  rfl
#align alg_equiv.symm_to_ring_equiv AlgEquiv.symm_toRingEquiv

#print AlgEquiv.trans /-
/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }
#align alg_equiv.trans AlgEquiv.trans
-/

/- warning: alg_equiv.apply_symm_apply -> AlgEquiv.apply_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.apply_symm_apply AlgEquiv.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply
#align alg_equiv.apply_symm_apply AlgEquiv.apply_symm_apply

/- warning: alg_equiv.symm_apply_apply -> AlgEquiv.symm_apply_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.symm_apply_apply AlgEquiv.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply
#align alg_equiv.symm_apply_apply AlgEquiv.symm_apply_apply

/- warning: alg_equiv.symm_trans_apply -> AlgEquiv.symm_trans_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.symm_trans_apply AlgEquiv.symm_trans_applyₓ'. -/
@[simp]
theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl
#align alg_equiv.symm_trans_apply AlgEquiv.symm_trans_apply

/- warning: alg_equiv.coe_trans -> AlgEquiv.coe_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_trans AlgEquiv.coe_transₓ'. -/
@[simp]
theorem coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align alg_equiv.coe_trans AlgEquiv.coe_trans

/- warning: alg_equiv.trans_apply -> AlgEquiv.trans_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.trans_apply AlgEquiv.trans_applyₓ'. -/
@[simp]
theorem trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
#align alg_equiv.trans_apply AlgEquiv.trans_apply

/- warning: alg_equiv.comp_symm -> AlgEquiv.comp_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.comp_symm AlgEquiv.comp_symmₓ'. -/
@[simp]
theorem comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂ := by
  ext; simp
#align alg_equiv.comp_symm AlgEquiv.comp_symm

/- warning: alg_equiv.symm_comp -> AlgEquiv.symm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.symm_comp AlgEquiv.symm_compₓ'. -/
@[simp]
theorem symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = AlgHom.id R A₁ := by
  ext; simp
#align alg_equiv.symm_comp AlgEquiv.symm_comp

/- warning: alg_equiv.left_inverse_symm -> AlgEquiv.leftInverse_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.left_inverse_symm AlgEquiv.leftInverse_symmₓ'. -/
theorem leftInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv
#align alg_equiv.left_inverse_symm AlgEquiv.leftInverse_symm

/- warning: alg_equiv.right_inverse_symm -> AlgEquiv.rightInverse_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.right_inverse_symm AlgEquiv.rightInverse_symmₓ'. -/
theorem rightInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e :=
  e.right_inv
#align alg_equiv.right_inverse_symm AlgEquiv.rightInverse_symm

#print AlgEquiv.arrowCongr /-
/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
def arrowCongr {A₁' A₂' : Type _} [Semiring A₁'] [Semiring A₂'] [Algebra R A₁'] [Algebra R A₂']
    (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂')
    where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, to_alg_hom_eq_coe, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, to_alg_hom_eq_coe, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]
#align alg_equiv.arrow_congr AlgEquiv.arrowCongr
-/

/- warning: alg_equiv.arrow_congr_comp -> AlgEquiv.arrowCongr_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.arrow_congr_comp AlgEquiv.arrowCongr_compₓ'. -/
theorem arrowCongr_comp {A₁' A₂' A₃' : Type _} [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
    [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
    (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) :=
  by
  ext; simp only [arrow_congr, Equiv.coe_fn_mk, AlgHom.comp_apply]
  congr ; exact (e₂.symm_apply_apply _).symm
#align alg_equiv.arrow_congr_comp AlgEquiv.arrowCongr_comp

#print AlgEquiv.arrowCongr_refl /-
@[simp]
theorem arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ →ₐ[R] A₂) := by
  ext; rfl
#align alg_equiv.arrow_congr_refl AlgEquiv.arrowCongr_refl
-/

/- warning: alg_equiv.arrow_congr_trans -> AlgEquiv.arrowCongr_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.arrow_congr_trans AlgEquiv.arrowCongr_transₓ'. -/
@[simp]
theorem arrowCongr_trans {A₁' A₂' A₃' : Type _} [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
    [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
    (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := by
  ext; rfl
#align alg_equiv.arrow_congr_trans AlgEquiv.arrowCongr_trans

/- warning: alg_equiv.arrow_congr_symm -> AlgEquiv.arrowCongr_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.arrow_congr_symm AlgEquiv.arrowCongr_symmₓ'. -/
@[simp]
theorem arrowCongr_symm {A₁' A₂' : Type _} [Semiring A₁'] [Semiring A₂'] [Algebra R A₁']
    [Algebra R A₂'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm := by ext; rfl
#align alg_equiv.arrow_congr_symm AlgEquiv.arrowCongr_symm

#print AlgEquiv.ofAlgHom /-
/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂)
    (h₂ : g.comp f = AlgHom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }
#align alg_equiv.of_alg_hom AlgEquiv.ofAlgHom
-/

/- warning: alg_equiv.coe_alg_hom_of_alg_hom -> AlgEquiv.coe_algHom_ofAlgHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.coe_alg_hom_of_alg_hom AlgEquiv.coe_algHom_ofAlgHomₓ'. -/
theorem coe_algHom_ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  AlgHom.ext fun _ => rfl
#align alg_equiv.coe_alg_hom_of_alg_hom AlgEquiv.coe_algHom_ofAlgHom

/- warning: alg_equiv.of_alg_hom_coe_alg_hom -> AlgEquiv.ofAlgHom_coe_algHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.of_alg_hom_coe_alg_hom AlgEquiv.ofAlgHom_coe_algHomₓ'. -/
@[simp]
theorem ofAlgHom_coe_algHom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl
#align alg_equiv.of_alg_hom_coe_alg_hom AlgEquiv.ofAlgHom_coe_algHom

#print AlgEquiv.ofAlgHom_symm /-
theorem ofAlgHom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl
#align alg_equiv.of_alg_hom_symm AlgEquiv.ofAlgHom_symm
-/

#print AlgEquiv.ofBijective /-
/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with }
#align alg_equiv.of_bijective AlgEquiv.ofBijective
-/

#print AlgEquiv.coe_ofBijective /-
@[simp]
theorem coe_ofBijective {f : A₁ →ₐ[R] A₂} {hf : Function.Bijective f} :
    (AlgEquiv.ofBijective f hf : A₁ → A₂) = f :=
  rfl
#align alg_equiv.coe_of_bijective AlgEquiv.coe_ofBijective
-/

#print AlgEquiv.ofBijective_apply /-
theorem ofBijective_apply {f : A₁ →ₐ[R] A₂} {hf : Function.Bijective f} (a : A₁) :
    (AlgEquiv.ofBijective f hf) a = f a :=
  rfl
#align alg_equiv.of_bijective_apply AlgEquiv.ofBijective_apply
-/

#print AlgEquiv.toLinearEquiv /-
/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply]
def toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
  { e with
    toFun := e
    map_smul' := e.map_smul
    invFun := e.symm }
#align alg_equiv.to_linear_equiv AlgEquiv.toLinearEquiv
-/

#print AlgEquiv.toLinearEquiv_refl /-
@[simp]
theorem toLinearEquiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁ :=
  rfl
#align alg_equiv.to_linear_equiv_refl AlgEquiv.toLinearEquiv_refl
-/

#print AlgEquiv.toLinearEquiv_symm /-
@[simp]
theorem toLinearEquiv_symm (e : A₁ ≃ₐ[R] A₂) : e.toLinearEquiv.symm = e.symm.toLinearEquiv :=
  rfl
#align alg_equiv.to_linear_equiv_symm AlgEquiv.toLinearEquiv_symm
-/

#print AlgEquiv.toLinearEquiv_trans /-
@[simp]
theorem toLinearEquiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl
#align alg_equiv.to_linear_equiv_trans AlgEquiv.toLinearEquiv_trans
-/

#print AlgEquiv.toLinearEquiv_injective /-
theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ → A₁ ≃ₗ[R] A₂) :=
  fun e₁ e₂ h => ext <| LinearEquiv.congr_fun h
#align alg_equiv.to_linear_equiv_injective AlgEquiv.toLinearEquiv_injective
-/

#print AlgEquiv.toLinearMap /-
/-- Interpret an algebra equivalence as a linear map. -/
def toLinearMap : A₁ →ₗ[R] A₂ :=
  e.toAlgHom.toLinearMap
#align alg_equiv.to_linear_map AlgEquiv.toLinearMap
-/

/- warning: alg_equiv.to_alg_hom_to_linear_map -> AlgEquiv.toAlgHom_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.to_alg_hom_to_linear_map AlgEquiv.toAlgHom_toLinearMapₓ'. -/
@[simp]
theorem toAlgHom_toLinearMap : (e : A₁ →ₐ[R] A₂).toLinearMap = e.toLinearMap :=
  rfl
#align alg_equiv.to_alg_hom_to_linear_map AlgEquiv.toAlgHom_toLinearMap

#print AlgEquiv.toLinearEquiv_toLinearMap /-
@[simp]
theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl
#align alg_equiv.to_linear_equiv_to_linear_map AlgEquiv.toLinearEquiv_toLinearMap
-/

/- warning: alg_equiv.to_linear_map_apply -> AlgEquiv.toLinearMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.to_linear_map_apply AlgEquiv.toLinearMap_applyₓ'. -/
@[simp]
theorem toLinearMap_apply (x : A₁) : e.toLinearMap x = e x :=
  rfl
#align alg_equiv.to_linear_map_apply AlgEquiv.toLinearMap_apply

#print AlgEquiv.toLinearMap_injective /-
theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A₁ →ₗ[R] A₂) := fun e₁ e₂ h =>
  ext <| LinearMap.congr_fun h
#align alg_equiv.to_linear_map_injective AlgEquiv.toLinearMap_injective
-/

#print AlgEquiv.trans_toLinearMap /-
@[simp]
theorem trans_toLinearMap (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl
#align alg_equiv.trans_to_linear_map AlgEquiv.trans_toLinearMap
-/

section OfLinearEquiv

variable (l : A₁ ≃ₗ[R] A₂) (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)
  (commutes : ∀ r : R, l (algebraMap R A₁ r) = algebraMap R A₂ r)

/- warning: alg_equiv.of_linear_equiv -> AlgEquiv.ofLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.of_linear_equiv AlgEquiv.ofLinearEquivₓ'. -/
/-- Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and action of scalars.
-/
@[simps apply]
def ofLinearEquiv : A₁ ≃ₐ[R] A₂ :=
  { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := commutes }
#align alg_equiv.of_linear_equiv AlgEquiv.ofLinearEquiv

/- warning: alg_equiv.of_linear_equiv_symm -> AlgEquiv.ofLinearEquiv_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.of_linear_equiv_symm AlgEquiv.ofLinearEquiv_symmₓ'. -/
@[simp]
theorem ofLinearEquiv_symm :
    (ofLinearEquiv l map_mul commutes).symm =
      ofLinearEquiv l.symm (ofLinearEquiv l map_mul commutes).symm.map_mul
        (ofLinearEquiv l map_mul commutes).symm.commutes :=
  rfl
#align alg_equiv.of_linear_equiv_symm AlgEquiv.ofLinearEquiv_symm

/- warning: alg_equiv.of_linear_equiv_to_linear_equiv -> AlgEquiv.ofLinearEquiv_toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.of_linear_equiv_to_linear_equiv AlgEquiv.ofLinearEquiv_toLinearEquivₓ'. -/
@[simp]
theorem ofLinearEquiv_toLinearEquiv (map_mul) (commutes) :
    ofLinearEquiv e.toLinearEquiv map_mul commutes = e := by ext; rfl
#align alg_equiv.of_linear_equiv_to_linear_equiv AlgEquiv.ofLinearEquiv_toLinearEquiv

/- warning: alg_equiv.to_linear_equiv_of_linear_equiv -> AlgEquiv.toLinearEquiv_ofLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.to_linear_equiv_of_linear_equiv AlgEquiv.toLinearEquiv_ofLinearEquivₓ'. -/
@[simp]
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_mul commutes) = l := by
  ext; rfl
#align alg_equiv.to_linear_equiv_of_linear_equiv AlgEquiv.toLinearEquiv_ofLinearEquiv

end OfLinearEquiv

section OfRingEquiv

/- warning: alg_equiv.of_ring_equiv -> AlgEquiv.ofRingEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.of_ring_equiv AlgEquiv.ofRingEquivₓ'. -/
/-- Promotes a linear ring_equiv to an alg_equiv. -/
@[simps]
def ofRingEquiv {f : A₁ ≃+* A₂} (hf : ∀ x, f (algebraMap R A₁ x) = algebraMap R A₂ x) :
    A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }
#align alg_equiv.of_ring_equiv AlgEquiv.ofRingEquiv

end OfRingEquiv

#print AlgEquiv.aut /-
@[simps (config := { attrs := [] }) mul one]
instance aut : Group (A₁ ≃ₐ[R] A₁) where
  mul ϕ ψ := ψ.trans ϕ
  mul_assoc ϕ ψ χ := rfl
  one := refl
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl
  inv := symm
  mul_left_inv ϕ := ext <| symm_apply_apply ϕ
#align alg_equiv.aut AlgEquiv.aut
-/

/- warning: alg_equiv.one_apply -> AlgEquiv.one_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.one_apply AlgEquiv.one_applyₓ'. -/
@[simp]
theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x :=
  rfl
#align alg_equiv.one_apply AlgEquiv.one_apply

/- warning: alg_equiv.mul_apply -> AlgEquiv.mul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.mul_apply AlgEquiv.mul_applyₓ'. -/
@[simp]
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl
#align alg_equiv.mul_apply AlgEquiv.mul_apply

/- warning: alg_equiv.aut_congr -> AlgEquiv.autCongr is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} {A₂ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_3 : Semiring.{u3} A₂] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2] [_inst_6 : Algebra.{u1, u3} R A₂ _inst_1 _inst_3], (AlgEquiv.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) -> (MulEquiv.{u2, u3} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (MulOneClass.toHasMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (MulOneClass.toHasMul.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Monoid.toMulOneClass.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (DivInvMonoid.toMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Group.toDivInvMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.aut.{u1, u3} R A₂ _inst_1 _inst_3 _inst_6))))))
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} {A₂ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_3 : Semiring.{u3} A₂] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2] [_inst_6 : Algebra.{u1, u3} R A₂ _inst_1 _inst_3], (AlgEquiv.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) -> (MulEquiv.{u2, u3} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (MulOneClass.toMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (MulOneClass.toMul.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Monoid.toMulOneClass.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (DivInvMonoid.toMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Group.toDivInvMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.aut.{u1, u3} R A₂ _inst_1 _inst_3 _inst_6))))))
Case conversion may be inaccurate. Consider using '#align alg_equiv.aut_congr AlgEquiv.autCongrₓ'. -/
/-- An algebra isomorphism induces a group isomorphism between automorphism groups -/
@[simps apply]
def autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂
    where
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  left_inv ψ := by ext; simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by ext; simp_rw [trans_apply, apply_symm_apply]
  map_mul' ψ χ := by ext; simp only [mul_apply, trans_apply, symm_apply_apply]
#align alg_equiv.aut_congr AlgEquiv.autCongr

/- warning: alg_equiv.aut_congr_refl -> AlgEquiv.autCongr_refl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], Eq.{succ u2} (MulEquiv.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (MulOneClass.toHasMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (MulOneClass.toHasMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))) (AlgEquiv.autCongr.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgEquiv.refl.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)) (MulEquiv.refl.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (MulOneClass.toHasMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))))
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], Eq.{succ u2} (MulEquiv.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (MulOneClass.toMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (MulOneClass.toMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))) (AlgEquiv.autCongr.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgEquiv.refl.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)) (MulEquiv.refl.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (MulOneClass.toMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))))
Case conversion may be inaccurate. Consider using '#align alg_equiv.aut_congr_refl AlgEquiv.autCongr_reflₓ'. -/
@[simp]
theorem autCongr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁) := by ext; rfl
#align alg_equiv.aut_congr_refl AlgEquiv.autCongr_refl

/- warning: alg_equiv.aut_congr_symm -> AlgEquiv.autCongr_symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} {A₂ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_3 : Semiring.{u3} A₂] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2] [_inst_6 : Algebra.{u1, u3} R A₂ _inst_1 _inst_3] (ϕ : AlgEquiv.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6), Eq.{max (succ u3) (succ u2)} (MulEquiv.{u3, u2} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (MulOneClass.toHasMul.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Monoid.toMulOneClass.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (DivInvMonoid.toMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Group.toDivInvMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.aut.{u1, u3} R A₂ _inst_1 _inst_3 _inst_6))))) (MulOneClass.toHasMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))) (MulEquiv.symm.{u2, u3} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (MulOneClass.toHasMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (MulOneClass.toHasMul.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Monoid.toMulOneClass.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (DivInvMonoid.toMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Group.toDivInvMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.aut.{u1, u3} R A₂ _inst_1 _inst_3 _inst_6))))) (AlgEquiv.autCongr.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 ϕ)) (AlgEquiv.autCongr.{u1, u3, u2} R A₂ A₁ _inst_1 _inst_3 _inst_2 _inst_6 _inst_5 (AlgEquiv.symm.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 ϕ))
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} {A₂ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_3 : Semiring.{u3} A₂] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2] [_inst_6 : Algebra.{u1, u3} R A₂ _inst_1 _inst_3] (ϕ : AlgEquiv.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6), Eq.{max (succ u2) (succ u3)} (MulEquiv.{u3, u2} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (MulOneClass.toMul.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Monoid.toMulOneClass.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (DivInvMonoid.toMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Group.toDivInvMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.aut.{u1, u3} R A₂ _inst_1 _inst_3 _inst_6))))) (MulOneClass.toMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))) (MulEquiv.symm.{u2, u3} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (MulOneClass.toMul.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Monoid.toMulOneClass.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (MulOneClass.toMul.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Monoid.toMulOneClass.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (DivInvMonoid.toMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (Group.toDivInvMonoid.{u3} (AlgEquiv.{u1, u3, u3} R A₂ A₂ _inst_1 _inst_3 _inst_3 _inst_6 _inst_6) (AlgEquiv.aut.{u1, u3} R A₂ _inst_1 _inst_3 _inst_6))))) (AlgEquiv.autCongr.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 ϕ)) (AlgEquiv.autCongr.{u1, u3, u2} R A₂ A₁ _inst_1 _inst_3 _inst_2 _inst_6 _inst_5 (AlgEquiv.symm.{u1, u2, u3} R A₁ A₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 ϕ))
Case conversion may be inaccurate. Consider using '#align alg_equiv.aut_congr_symm AlgEquiv.autCongr_symmₓ'. -/
@[simp]
theorem autCongr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl
#align alg_equiv.aut_congr_symm AlgEquiv.autCongr_symm

/- warning: alg_equiv.aut_congr_trans -> AlgEquiv.autCongr_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.aut_congr_trans AlgEquiv.autCongr_transₓ'. -/
@[simp]
theorem autCongr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
    (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ) :=
  rfl
#align alg_equiv.aut_congr_trans AlgEquiv.autCongr_trans

#print AlgEquiv.applyMulSemiringAction /-
/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `function.End.apply_mul_action`. -/
instance applyMulSemiringAction : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁
    where
  smul := (· <| ·)
  smul_zero := AlgEquiv.map_zero
  smul_add := AlgEquiv.map_add
  smul_one := AlgEquiv.map_one
  smul_mul := AlgEquiv.map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align alg_equiv.apply_mul_semiring_action AlgEquiv.applyMulSemiringAction
-/

/- warning: alg_equiv.smul_def -> AlgEquiv.smul_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.smul_def AlgEquiv.smul_defₓ'. -/
@[simp]
protected theorem smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl
#align alg_equiv.smul_def AlgEquiv.smul_def

/- warning: alg_equiv.apply_has_faithful_smul -> AlgEquiv.apply_faithfulSMul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], FaithfulSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (SMulZeroClass.toHasSmul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (DistribSMul.toSmulZeroClass.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (MulSemiringAction.toDistribMulAction.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) _inst_2 (AlgEquiv.applyMulSemiringAction.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], FaithfulSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (SMulZeroClass.toSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (MonoidWithZero.toZero.{u2} A₁ (Semiring.toMonoidWithZero.{u2} A₁ _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (MulSemiringAction.toDistribMulAction.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) _inst_2 (AlgEquiv.applyMulSemiringAction.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))
Case conversion may be inaccurate. Consider using '#align alg_equiv.apply_has_faithful_smul AlgEquiv.apply_faithfulSMulₓ'. -/
instance apply_faithfulSMul : FaithfulSMul (A₁ ≃ₐ[R] A₁) A₁ :=
  ⟨fun _ _ => AlgEquiv.ext⟩
#align alg_equiv.apply_has_faithful_smul AlgEquiv.apply_faithfulSMul

/- warning: alg_equiv.apply_smul_comm_class -> AlgEquiv.apply_smulCommClass is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], SMulCommClass.{u1, u2, u2} R (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (SMulZeroClass.toHasSmul.{u1, u2} R A₁ (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddCommMonoid.toAddMonoid.{u2} A₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A₁ (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddCommMonoid.toAddMonoid.{u2} A₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A₁ (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddCommMonoid.toAddMonoid.{u2} A₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A₁ (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))) (Algebra.toModule.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (SMulZeroClass.toHasSmul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (DistribSMul.toSmulZeroClass.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (MulSemiringAction.toDistribMulAction.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) _inst_2 (AlgEquiv.applyMulSemiringAction.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], SMulCommClass.{u1, u2, u2} R (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (Algebra.toSMul.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5) (SMulZeroClass.toSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (MonoidWithZero.toZero.{u2} A₁ (Semiring.toMonoidWithZero.{u2} A₁ _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (MulSemiringAction.toDistribMulAction.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) _inst_2 (AlgEquiv.applyMulSemiringAction.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))
Case conversion may be inaccurate. Consider using '#align alg_equiv.apply_smul_comm_class AlgEquiv.apply_smulCommClassₓ'. -/
instance apply_smulCommClass : SMulCommClass R (A₁ ≃ₐ[R] A₁) A₁
    where smul_comm r e a := (e.map_smul r a).symm
#align alg_equiv.apply_smul_comm_class AlgEquiv.apply_smulCommClass

/- warning: alg_equiv.apply_smul_comm_class' -> AlgEquiv.apply_smulCommClass' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], SMulCommClass.{u2, u1, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) R A₁ (SMulZeroClass.toHasSmul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (DistribSMul.toSmulZeroClass.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (MulSemiringAction.toDistribMulAction.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) _inst_2 (AlgEquiv.applyMulSemiringAction.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (SMulZeroClass.toHasSmul.{u1, u2} R A₁ (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddCommMonoid.toAddMonoid.{u2} A₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A₁ (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddCommMonoid.toAddMonoid.{u2} A₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A₁ (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddCommMonoid.toAddMonoid.{u2} A₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A₁ (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A₁ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))) (Algebra.toModule.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)))))
but is expected to have type
  forall {R : Type.{u1}} {A₁ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A₁] [_inst_5 : Algebra.{u1, u2} R A₁ _inst_1 _inst_2], SMulCommClass.{u2, u1, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) R A₁ (SMulZeroClass.toSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (MonoidWithZero.toZero.{u2} A₁ (Semiring.toMonoidWithZero.{u2} A₁ _inst_2)) (DistribSMul.toSMulZeroClass.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (AddMonoid.toAddZeroClass.{u2} A₁ (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) (AddMonoidWithOne.toAddMonoid.{u2} A₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A₁ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A₁ (Semiring.toNonAssocSemiring.{u2} A₁ _inst_2)))) (MulSemiringAction.toDistribMulAction.{u2, u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) A₁ (DivInvMonoid.toMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (Group.toDivInvMonoid.{u2} (AlgEquiv.{u1, u2, u2} R A₁ A₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (AlgEquiv.aut.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))) _inst_2 (AlgEquiv.applyMulSemiringAction.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5))))) (Algebra.toSMul.{u1, u2} R A₁ _inst_1 _inst_2 _inst_5)
Case conversion may be inaccurate. Consider using '#align alg_equiv.apply_smul_comm_class' AlgEquiv.apply_smulCommClass'ₓ'. -/
instance apply_smulCommClass' : SMulCommClass (A₁ ≃ₐ[R] A₁) R A₁
    where smul_comm e r a := e.map_smul r a
#align alg_equiv.apply_smul_comm_class' AlgEquiv.apply_smulCommClass'

/- warning: alg_equiv.algebra_map_eq_apply -> AlgEquiv.algebraMap_eq_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.algebra_map_eq_apply AlgEquiv.algebraMap_eq_applyₓ'. -/
@[simp]
theorem algebraMap_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
    algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
  ⟨fun h => by simpa using e.symm.to_alg_hom.algebra_map_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩
#align alg_equiv.algebra_map_eq_apply AlgEquiv.algebraMap_eq_apply

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A₁] [CommSemiring A₂]

variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

/- warning: alg_equiv.map_prod -> AlgEquiv.map_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_prod AlgEquiv.map_prodₓ'. -/
theorem map_prod {ι : Type _} (f : ι → A₁) (s : Finset ι) : e (∏ x in s, f x) = ∏ x in s, e (f x) :=
  map_prod _ f s
#align alg_equiv.map_prod AlgEquiv.map_prod

/- warning: alg_equiv.map_finsupp_prod -> AlgEquiv.map_finsupp_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_finsupp_prod AlgEquiv.map_finsupp_prodₓ'. -/
theorem map_finsupp_prod {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A₁) :
    e (f.Prod g) = f.Prod fun i a => e (g i a) :=
  map_finsupp_prod _ f g
#align alg_equiv.map_finsupp_prod AlgEquiv.map_finsupp_prod

end CommSemiring

section Ring

variable [CommSemiring R] [Ring A₁] [Ring A₂]

variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

/- warning: alg_equiv.map_neg -> AlgEquiv.map_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_neg AlgEquiv.map_negₓ'. -/
protected theorem map_neg (x) : e (-x) = -e x :=
  map_neg e x
#align alg_equiv.map_neg AlgEquiv.map_neg

/- warning: alg_equiv.map_sub -> AlgEquiv.map_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_sub AlgEquiv.map_subₓ'. -/
protected theorem map_sub (x y) : e (x - y) = e x - e y :=
  map_sub e x y
#align alg_equiv.map_sub AlgEquiv.map_sub

end Ring

end AlgEquiv

namespace MulSemiringAction

variable {M G : Type _} (R A : Type _) [CommSemiring R] [Semiring A] [Algebra R A]

section

variable [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/- warning: mul_semiring_action.to_alg_equiv -> MulSemiringAction.toAlgEquiv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} (R : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u2, u3} R A _inst_1 _inst_2] [_inst_4 : Group.{u1} G] [_inst_5 : MulSemiringAction.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_2] [_inst_6 : SMulCommClass.{u1, u2, u3} G R A (SMulZeroClass.toHasSmul.{u1, u3} G A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u3} G A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_2 _inst_5)))) (SMulZeroClass.toHasSmul.{u2, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u2, u3} R A (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u3} R A (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (Module.toMulActionWithZero.{u2, u3} R A (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))) (Algebra.toModule.{u2, u3} R A _inst_1 _inst_2 _inst_3)))))], G -> (AlgEquiv.{u2, u3, u3} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3)
but is expected to have type
  forall {G : Type.{u1}} (R : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u2, u3} R A _inst_1 _inst_2] [_inst_4 : Group.{u1} G] [_inst_5 : MulSemiringAction.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_2] [_inst_6 : SMulCommClass.{u1, u2, u3} G R A (SMulZeroClass.toSMul.{u1, u3} G A (MonoidWithZero.toZero.{u3} A (Semiring.toMonoidWithZero.{u3} A _inst_2)) (DistribSMul.toSMulZeroClass.{u1, u3} G A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_2 _inst_5)))) (Algebra.toSMul.{u2, u3} R A _inst_1 _inst_2 _inst_3)], G -> (AlgEquiv.{u2, u3, u3} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3)
Case conversion may be inaccurate. Consider using '#align mul_semiring_action.to_alg_equiv MulSemiringAction.toAlgEquivₓ'. -/
/-- Each element of the group defines a algebra equivalence.

This is a stronger version of `mul_semiring_action.to_ring_equiv` and
`distrib_mul_action.to_linear_equiv`. -/
@[simps]
def toAlgEquiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }
#align mul_semiring_action.to_alg_equiv MulSemiringAction.toAlgEquiv

/- warning: mul_semiring_action.to_alg_equiv_injective -> MulSemiringAction.toAlgEquiv_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} (R : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u2, u3} R A _inst_1 _inst_2] [_inst_4 : Group.{u1} G] [_inst_5 : MulSemiringAction.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_2] [_inst_6 : SMulCommClass.{u1, u2, u3} G R A (SMulZeroClass.toHasSmul.{u1, u3} G A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u3} G A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_2 _inst_5)))) (SMulZeroClass.toHasSmul.{u2, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u2, u3} R A (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u3} R A (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (Module.toMulActionWithZero.{u2, u3} R A (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))) (Algebra.toModule.{u2, u3} R A _inst_1 _inst_2 _inst_3)))))] [_inst_7 : FaithfulSMul.{u1, u3} G A (SMulZeroClass.toHasSmul.{u1, u3} G A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u3} G A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)) _inst_2 _inst_5))))], Function.Injective.{succ u1, succ u3} G (AlgEquiv.{u2, u3, u3} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3) (MulSemiringAction.toAlgEquiv.{u1, u2, u3} G R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)
but is expected to have type
  forall {G : Type.{u3}} (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Group.{u3} G] [_inst_5 : MulSemiringAction.{u3, u2} G A (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_4)) _inst_2] [_inst_6 : SMulCommClass.{u3, u1, u2} G R A (SMulZeroClass.toSMul.{u3, u2} G A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (DistribSMul.toSMulZeroClass.{u3, u2} G A (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (DistribMulAction.toDistribSMul.{u3, u2} G A (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_4)) (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u3, u2} G A (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_4)) _inst_2 _inst_5)))) (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_3)] [_inst_7 : FaithfulSMul.{u3, u2} G A (SMulZeroClass.toSMul.{u3, u2} G A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (DistribSMul.toSMulZeroClass.{u3, u2} G A (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (DistribMulAction.toDistribSMul.{u3, u2} G A (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_4)) (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u3, u2} G A (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_4)) _inst_2 _inst_5))))], Function.Injective.{succ u3, succ u2} G (AlgEquiv.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3) (MulSemiringAction.toAlgEquiv.{u3, u1, u2} G R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align mul_semiring_action.to_alg_equiv_injective MulSemiringAction.toAlgEquiv_injectiveₓ'. -/
theorem toAlgEquiv_injective [FaithfulSMul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r
#align mul_semiring_action.to_alg_equiv_injective MulSemiringAction.toAlgEquiv_injective

end

end MulSemiringAction

