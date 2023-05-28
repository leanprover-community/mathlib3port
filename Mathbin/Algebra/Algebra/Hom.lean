/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.algebra.hom
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic

/-!
# Homomorphisms of `R`-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `alg_hom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `algebra.of_id R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `alg_hom`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/


open BigOperators

universe u v w u₁ v₁

#print AlgHom /-
/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_nonempty_instance]
structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, to_fun (algebraMap R A r) = algebraMap R B r
#align alg_hom AlgHom
-/

run_cmd
  tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

-- mathport name: «expr →ₐ »
infixr:25 " →ₐ " => AlgHom _

-- mathport name: «expr →ₐ[ ] »
notation:25 A " →ₐ[" R "] " B => AlgHom R A B

#print AlgHomClass /-
/-- `alg_hom_class F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class AlgHomClass (F : Type _) (R : outParam (Type _)) (A : outParam (Type _))
  (B : outParam (Type _)) [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B] extends RingHomClass F A B where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r
#align alg_hom_class AlgHomClass
-/

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] AlgHomClass.toRingHomClass

attribute [simp] AlgHomClass.commutes

namespace AlgHomClass

variable {R : Type _} {A : Type _} {B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

-- see Note [lower instance priority]
instance (priority := 100) {F : Type _} [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [Algebra.smul_def, map_mul, commutes, RingHom.id_apply] }

instance {F : Type _} [AlgHomClass F R A B] : CoeTC F (A →ₐ[R] B)
    where coe f :=
    { (f : A →+* B) with
      toFun := f
      commutes' := AlgHomClass.commutes f }

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

instance : CoeFun (A →ₐ[R] B) fun _ => A → B :=
  ⟨AlgHom.toFun⟩

initialize_simps_projections AlgHom (toFun → apply)

/- warning: alg_hom.coe_coe -> AlgHom.coe_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_coe AlgHom.coe_coeₓ'. -/
@[simp, protected]
theorem coe_coe {F : Type _} [AlgHomClass F R A B] (f : F) : ⇑(f : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_coe AlgHom.coe_coe

/- warning: alg_hom.to_fun_eq_coe -> AlgHom.toFun_eq_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.to_fun_eq_coe AlgHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe (f : A →ₐ[R] B) : f.toFun = f :=
  rfl
#align alg_hom.to_fun_eq_coe AlgHom.toFun_eq_coe

instance : AlgHomClass (A →ₐ[R] B) R A B
    where
  coe := toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
  map_add := map_add'
  map_zero := map_zero'
  map_mul := map_mul'
  map_one := map_one'
  commutes f := f.commutes'

/- warning: alg_hom.coe_ring_hom -> AlgHom.coeOutRingHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], Coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], CoeOut.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3))
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_ring_hom AlgHom.coeOutRingHomₓ'. -/
instance coeOutRingHom : Coe (A →ₐ[R] B) (A →+* B) :=
  ⟨AlgHom.toRingHom⟩
#align alg_hom.coe_ring_hom AlgHom.coeOutRingHom

/- warning: alg_hom.coe_monoid_hom -> AlgHom.coeOutMonoidHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], Coe.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (MonoidHom.{u2, u3} A B (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (MulZeroOneClass.toMulOneClass.{u3} B (NonAssocSemiring.toMulZeroOneClass.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], CoeOut.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (MonoidHom.{u2, u3} A B (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (MulZeroOneClass.toMulOneClass.{u3} B (NonAssocSemiring.toMulZeroOneClass.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))))
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_monoid_hom AlgHom.coeOutMonoidHomₓ'. -/
instance coeOutMonoidHom : Coe (A →ₐ[R] B) (A →* B) :=
  ⟨fun f => ↑(f : A →+* B)⟩
#align alg_hom.coe_monoid_hom AlgHom.coeOutMonoidHom

/- warning: alg_hom.coe_add_monoid_hom -> AlgHom.coeOutAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], Coe.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], CoeOut.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))))))
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_add_monoid_hom AlgHom.coeOutAddMonoidHomₓ'. -/
instance coeOutAddMonoidHom : Coe (A →ₐ[R] B) (A →+ B) :=
  ⟨fun f => ↑(f : A →+* B)⟩
#align alg_hom.coe_add_monoid_hom AlgHom.coeOutAddMonoidHom

/- warning: alg_hom.coe_mk -> AlgHom.coe_mks is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_mk AlgHom.coe_mksₓ'. -/
@[simp, norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
  rfl
#align alg_hom.coe_mk AlgHom.coe_mks

/- warning: alg_hom.to_ring_hom_eq_coe -> AlgHom.toRingHom_eq_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.to_ring_hom_eq_coe AlgHom.toRingHom_eq_coeₓ'. -/
-- make the coercion the simp-normal form
@[simp]
theorem toRingHom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f :=
  rfl
#align alg_hom.to_ring_hom_eq_coe AlgHom.toRingHom_eq_coe

/- warning: alg_hom.coe_to_ring_hom -> AlgHom.coe_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_to_ring_hom AlgHom.coe_toRingHomₓ'. -/
@[simp, norm_cast]
theorem coe_toRingHom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f :=
  rfl
#align alg_hom.coe_to_ring_hom AlgHom.coe_toRingHom

/- warning: alg_hom.coe_to_monoid_hom -> AlgHom.coe_toMonoidHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_to_monoid_hom AlgHom.coe_toMonoidHomₓ'. -/
@[simp, norm_cast]
theorem coe_toMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f :=
  rfl
#align alg_hom.coe_to_monoid_hom AlgHom.coe_toMonoidHom

/- warning: alg_hom.coe_to_add_monoid_hom -> AlgHom.coe_toAddMonoidHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_to_add_monoid_hom AlgHom.coe_toAddMonoidHomₓ'. -/
@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f :=
  rfl
#align alg_hom.coe_to_add_monoid_hom AlgHom.coe_toAddMonoidHom

variable (φ : A →ₐ[R] B)

#print AlgHom.coe_fn_injective /-
theorem coe_fn_injective : @Function.Injective (A →ₐ[R] B) (A → B) coeFn :=
  FunLike.coe_injective
#align alg_hom.coe_fn_injective AlgHom.coe_fn_injective
-/

#print AlgHom.coe_fn_inj /-
theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  FunLike.coe_fn_eq
#align alg_hom.coe_fn_inj AlgHom.coe_fn_inj
-/

/- warning: alg_hom.coe_ring_hom_injective -> AlgHom.coe_ringHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_ring_hom_injective AlgHom.coe_ringHom_injectiveₓ'. -/
theorem coe_ringHom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →+* B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_arg _ H
#align alg_hom.coe_ring_hom_injective AlgHom.coe_ringHom_injective

/- warning: alg_hom.coe_monoid_hom_injective -> AlgHom.coe_monoidHom_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_monoid_hom_injective AlgHom.coe_monoidHom_injectiveₓ'. -/
theorem coe_monoidHom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →* B) :=
  RingHom.coe_monoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_monoid_hom_injective AlgHom.coe_monoidHom_injective

/- warning: alg_hom.coe_add_monoid_hom_injective -> AlgHom.coe_addMonoidHom_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], Function.Injective.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u3) (succ u2)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u3) (succ u2)} a b] => self.0) (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) (AddMonoidHom.hasCoeT.{u2, u3, max u2 u3} A B (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))))) (SemilinearMapClass.addMonoidHomClass.{u1, u1, u2, u3, max u2 u3} R R A B (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_6) (Algebra.toModule.{u1, u3} R B _inst_1 _inst_3 _inst_7) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (AlgHomClass.linearMapClass.{u1, u2, u3, max u2 u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7 (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AlgHom.algHomClass.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7)))))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3], Function.Injective.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) (AddMonoidHomClass.toAddMonoidHom.{u2, u3, max u2 u3} A B (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (AddMonoid.toAddZeroClass.{u3} B (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))))) (DistribMulActionHomClass.toAddMonoidHomClass.{max u2 u3, u1, u2, u3} (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) R A B (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (AddMonoidWithOne.toAddMonoid.{u3} B (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} B (NonAssocSemiring.toAddCommMonoidWithOne.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))) (Module.toDistribMulAction.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_6)) (Module.toDistribMulAction.{u1, u3} R B (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))) (Algebra.toModule.{u1, u3} R B _inst_1 _inst_3 _inst_7)) (SemilinearMapClass.distribMulActionHomClass.{u1, u2, u3, max u2 u3} R A B (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_6) (Algebra.toModule.{u1, u3} R B _inst_1 _inst_3 _inst_7) (AlgHomClass.linearMapClass.{u1, u2, u3, max u2 u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7 (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (AlgHom.algHomClass.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7)))))
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_add_monoid_hom_injective AlgHom.coe_addMonoidHom_injectiveₓ'. -/
theorem coe_addMonoidHom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →+ B) :=
  RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective
#align alg_hom.coe_add_monoid_hom_injective AlgHom.coe_addMonoidHom_injective

#print AlgHom.congr_fun /-
protected theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  FunLike.congr_fun H x
#align alg_hom.congr_fun AlgHom.congr_fun
-/

#print AlgHom.congr_arg /-
protected theorem congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  FunLike.congr_arg φ h
#align alg_hom.congr_arg AlgHom.congr_arg
-/

#print AlgHom.ext /-
@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  FunLike.ext _ _ H
#align alg_hom.ext AlgHom.ext
-/

#print AlgHom.ext_iff /-
theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  FunLike.ext_iff
#align alg_hom.ext_iff AlgHom.ext_iff
-/

#print AlgHom.mk_coe /-
@[simp]
theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
  ext fun _ => rfl
#align alg_hom.mk_coe AlgHom.mk_coe
-/

#print AlgHom.commutes /-
@[simp]
theorem commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r :=
  φ.commutes' r
#align alg_hom.commutes AlgHom.commutes
-/

/- warning: alg_hom.comp_algebra_map -> AlgHom.comp_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.comp_algebra_map AlgHom.comp_algebraMapₓ'. -/
theorem comp_algebraMap : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext <| φ.commutes
#align alg_hom.comp_algebra_map AlgHom.comp_algebraMap

#print AlgHom.map_add /-
protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _
#align alg_hom.map_add AlgHom.map_add
-/

#print AlgHom.map_zero /-
protected theorem map_zero : φ 0 = 0 :=
  map_zero _
#align alg_hom.map_zero AlgHom.map_zero
-/

#print AlgHom.map_mul /-
protected theorem map_mul (x y) : φ (x * y) = φ x * φ y :=
  map_mul _ _ _
#align alg_hom.map_mul AlgHom.map_mul
-/

#print AlgHom.map_one /-
protected theorem map_one : φ 1 = 1 :=
  map_one _
#align alg_hom.map_one AlgHom.map_one
-/

#print AlgHom.map_pow /-
protected theorem map_pow (x : A) (n : ℕ) : φ (x ^ n) = φ x ^ n :=
  map_pow _ _ _
#align alg_hom.map_pow AlgHom.map_pow
-/

#print AlgHom.map_smul /-
@[simp]
protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _
#align alg_hom.map_smul AlgHom.map_smul
-/

/- warning: alg_hom.map_sum -> AlgHom.map_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.map_sum AlgHom.map_sumₓ'. -/
protected theorem map_sum {ι : Type _} (f : ι → A) (s : Finset ι) :
    φ (∑ x in s, f x) = ∑ x in s, φ (f x) :=
  map_sum _ _ _
#align alg_hom.map_sum AlgHom.map_sum

/- warning: alg_hom.map_finsupp_sum -> AlgHom.map_finsupp_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.map_finsupp_sum AlgHom.map_finsupp_sumₓ'. -/
protected theorem map_finsupp_sum {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.Sum g) = f.Sum fun i a => φ (g i a) :=
  map_finsupp_sum _ _ _
#align alg_hom.map_finsupp_sum AlgHom.map_finsupp_sum

#print AlgHom.map_bit0 /-
protected theorem map_bit0 (x) : φ (bit0 x) = bit0 (φ x) :=
  map_bit0 _ _
#align alg_hom.map_bit0 AlgHom.map_bit0
-/

#print AlgHom.map_bit1 /-
protected theorem map_bit1 (x) : φ (bit1 x) = bit1 (φ x) :=
  map_bit1 _ _
#align alg_hom.map_bit1 AlgHom.map_bit1
-/

/- warning: alg_hom.mk' -> AlgHom.mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3] (f : RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)), (forall (c : R) (x : A), Eq.{succ u3} B (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) (fun (_x : RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) => A -> B) (RingHom.hasCoeToFun.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) f (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_6))))) c x)) (SMul.smul.{u1, u3} R B (SMulZeroClass.toHasSmul.{u1, u3} R B (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) (SMulWithZero.toSmulZeroClass.{u1, u3} R B (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) (MulActionWithZero.toSMulWithZero.{u1, u3} R B (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)))))) (Module.toMulActionWithZero.{u1, u3} R B (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))) (Algebra.toModule.{u1, u3} R B _inst_1 _inst_3 _inst_7))))) c (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) (fun (_x : RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) => A -> B) (RingHom.hasCoeToFun.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) f x))) -> (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_7 : Algebra.{u1, u3} R B _inst_1 _inst_3] (f : RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)), (forall (c : R) (x : A), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) (HSMul.hSMul.{u1, u2, u2} R A A (instHSMul.{u1, u2} R A (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_6)) c x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A B (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toMul.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3) (RingHom.instRingHomClassRingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3))))) f (HSMul.hSMul.{u1, u2, u2} R A A (instHSMul.{u1, u2} R A (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_6)) c x)) (HSMul.hSMul.{u1, u3, u3} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) x) (instHSMul.{u1, u3} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) x) (Algebra.toSMul.{u1, u3} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) x) _inst_1 _inst_3 _inst_7)) c (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A B (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toMul.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B _inst_3)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3)) A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3) (RingHom.instRingHomClassRingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u3} B _inst_3))))) f x))) -> (AlgHom.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_6 _inst_7)
Case conversion may be inaccurate. Consider using '#align alg_hom.mk' AlgHom.mk'ₓ'. -/
/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : A →ₐ[R] B :=
  { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }
#align alg_hom.mk' AlgHom.mk'

/- warning: alg_hom.coe_mk' -> AlgHom.coe_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.coe_mk' AlgHom.coe_mk'ₓ'. -/
@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl
#align alg_hom.coe_mk' AlgHom.coe_mk'

section

variable (R A)

#print AlgHom.id /-
/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }
#align alg_hom.id AlgHom.id
-/

#print AlgHom.coe_id /-
@[simp]
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl
#align alg_hom.coe_id AlgHom.coe_id
-/

/- warning: alg_hom.id_to_ring_hom -> AlgHom.id_toRingHom is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (RingHom.{u2, u2} A A (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6) (RingHom.{u2, u2} A A (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (HasLiftT.mk.{succ u2, succ u2} (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6) (RingHom.{u2, u2} A A (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (CoeTCₓ.coe.{succ u2, succ u2} (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6) (RingHom.{u2, u2} A A (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (RingHom.hasCoeT.{u2, u2, u2} (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6) A A (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} A _inst_2) (AlgHomClass.toRingHomClass.{u2, u1, u2, u2} (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6) R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6 (AlgHom.algHomClass.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6))))) (AlgHom.id.{u1, u2} R A _inst_1 _inst_2 _inst_6)) (RingHom.id.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_6 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (RingHom.{u2, u2} A A (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (RingHomClass.toRingHom.{u2, u2, u2} (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6) A A (Semiring.toNonAssocSemiring.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} A _inst_2) (AlgHomClass.toRingHomClass.{u2, u1, u2, u2} (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6) R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6 (AlgHom.algHomClass.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_6 _inst_6)) (AlgHom.id.{u1, u2} R A _inst_1 _inst_2 _inst_6)) (RingHom.id.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))
Case conversion may be inaccurate. Consider using '#align alg_hom.id_to_ring_hom AlgHom.id_toRingHomₓ'. -/
@[simp]
theorem id_toRingHom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl
#align alg_hom.id_to_ring_hom AlgHom.id_toRingHom

end

#print AlgHom.id_apply /-
theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl
#align alg_hom.id_apply AlgHom.id_apply
-/

#print AlgHom.comp /-
/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes] <;> rfl }
#align alg_hom.comp AlgHom.comp
-/

#print AlgHom.coe_comp /-
@[simp]
theorem coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl
#align alg_hom.coe_comp AlgHom.coe_comp
-/

#print AlgHom.comp_apply /-
theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl
#align alg_hom.comp_apply AlgHom.comp_apply
-/

/- warning: alg_hom.comp_to_ring_hom -> AlgHom.comp_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.comp_to_ring_hom AlgHom.comp_toRingHomₓ'. -/
theorem comp_toRingHom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
    (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ :=
  rfl
#align alg_hom.comp_to_ring_hom AlgHom.comp_toRingHom

#print AlgHom.comp_id /-
@[simp]
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  ext fun x => rfl
#align alg_hom.comp_id AlgHom.comp_id
-/

#print AlgHom.id_comp /-
@[simp]
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  ext fun x => rfl
#align alg_hom.id_comp AlgHom.id_comp
-/

#print AlgHom.comp_assoc /-
theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun x => rfl
#align alg_hom.comp_assoc AlgHom.comp_assoc
-/

#print AlgHom.toLinearMap /-
/-- R-Alg ⥤ R-Mod -/
def toLinearMap : A →ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _
#align alg_hom.to_linear_map AlgHom.toLinearMap
-/

/- warning: alg_hom.to_linear_map_apply -> AlgHom.toLinearMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.to_linear_map_apply AlgHom.toLinearMap_applyₓ'. -/
@[simp]
theorem toLinearMap_apply (p : A) : φ.toLinearMap p = φ p :=
  rfl
#align alg_hom.to_linear_map_apply AlgHom.toLinearMap_apply

#print AlgHom.toLinearMap_injective /-
theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun φ₁ φ₂ h =>
  ext <| LinearMap.congr_fun h
#align alg_hom.to_linear_map_injective AlgHom.toLinearMap_injective
-/

#print AlgHom.comp_toLinearMap /-
@[simp]
theorem comp_toLinearMap (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl
#align alg_hom.comp_to_linear_map AlgHom.comp_toLinearMap
-/

#print AlgHom.toLinearMap_id /-
@[simp]
theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl
#align alg_hom.to_linear_map_id AlgHom.toLinearMap_id
-/

/- warning: alg_hom.of_linear_map -> AlgHom.ofLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.of_linear_map AlgHom.ofLinearMapₓ'. -/
/-- Promote a `linear_map` to an `alg_hom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₐ[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }
#align alg_hom.of_linear_map AlgHom.ofLinearMap

/- warning: alg_hom.of_linear_map_to_linear_map -> AlgHom.ofLinearMap_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.of_linear_map_to_linear_map AlgHom.ofLinearMap_toLinearMapₓ'. -/
@[simp]
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap φ.toLinearMap map_one map_mul = φ :=
  by
  ext
  rfl
#align alg_hom.of_linear_map_to_linear_map AlgHom.ofLinearMap_toLinearMap

/- warning: alg_hom.to_linear_map_of_linear_map -> AlgHom.toLinearMap_ofLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.to_linear_map_of_linear_map AlgHom.toLinearMap_ofLinearMapₓ'. -/
@[simp]
theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f :=
  by
  ext
  rfl
#align alg_hom.to_linear_map_of_linear_map AlgHom.toLinearMap_ofLinearMap

/- warning: alg_hom.of_linear_map_id -> AlgHom.ofLinearMap_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.of_linear_map_id AlgHom.ofLinearMap_idₓ'. -/
@[simp]
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A :=
  ext fun _ => rfl
#align alg_hom.of_linear_map_id AlgHom.ofLinearMap_id

/- warning: alg_hom.map_smul_of_tower -> AlgHom.map_smul_of_tower is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.map_smul_of_tower AlgHom.map_smul_of_towerₓ'. -/
theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x
#align alg_hom.map_smul_of_tower AlgHom.map_smul_of_tower

#print AlgHom.map_list_prod /-
theorem map_list_prod (s : List A) : φ s.Prod = (s.map φ).Prod :=
  φ.toRingHom.map_list_prod s
#align alg_hom.map_list_prod AlgHom.map_list_prod
-/

#print AlgHom.End /-
@[simps (config := { attrs := [] }) mul one]
instance End : Monoid (A →ₐ[R] A) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := AlgHom.id R A
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl
#align alg_hom.End AlgHom.End
-/

#print AlgHom.one_apply /-
@[simp]
theorem one_apply (x : A) : (1 : A →ₐ[R] A) x = x :=
  rfl
#align alg_hom.one_apply AlgHom.one_apply
-/

#print AlgHom.mul_apply /-
@[simp]
theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl
#align alg_hom.mul_apply AlgHom.mul_apply
-/

/- warning: alg_hom.algebra_map_eq_apply -> AlgHom.algebraMap_eq_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.algebra_map_eq_apply AlgHom.algebraMap_eq_applyₓ'. -/
theorem algebraMap_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm
#align alg_hom.algebra_map_eq_apply AlgHom.algebraMap_eq_apply

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

#print AlgHom.map_multiset_prod /-
protected theorem map_multiset_prod (s : Multiset A) : φ s.Prod = (s.map φ).Prod :=
  map_multiset_prod _ _
#align alg_hom.map_multiset_prod AlgHom.map_multiset_prod
-/

/- warning: alg_hom.map_prod -> AlgHom.map_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.map_prod AlgHom.map_prodₓ'. -/
protected theorem map_prod {ι : Type _} (f : ι → A) (s : Finset ι) :
    φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
  map_prod _ _ _
#align alg_hom.map_prod AlgHom.map_prod

/- warning: alg_hom.map_finsupp_prod -> AlgHom.map_finsupp_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.map_finsupp_prod AlgHom.map_finsupp_prodₓ'. -/
protected theorem map_finsupp_prod {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.Prod g) = f.Prod fun i a => φ (g i a) :=
  map_finsupp_prod _ _ _
#align alg_hom.map_finsupp_prod AlgHom.map_finsupp_prod

end CommSemiring

section Ring

variable [CommSemiring R] [Ring A] [Ring B]

variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

#print AlgHom.map_neg /-
protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _
#align alg_hom.map_neg AlgHom.map_neg
-/

#print AlgHom.map_sub /-
protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _
#align alg_hom.map_sub AlgHom.map_sub
-/

end Ring

end AlgHom

namespace RingHom

variable {R S : Type _}

#print RingHom.toNatAlgHom /-
/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }
#align ring_hom.to_nat_alg_hom RingHom.toNatAlgHom
-/

/- warning: ring_hom.to_int_alg_hom -> RingHom.toIntAlgHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] [_inst_3 : Algebra.{0, u1} Int R Int.commSemiring (Ring.toSemiring.{u1} R _inst_1)] [_inst_4 : Algebra.{0, u2} Int S Int.commSemiring (Ring.toSemiring.{u2} S _inst_2)], (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) -> (AlgHom.{0, u1, u2} Int R S Int.commSemiring (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2) _inst_3 _inst_4)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] [_inst_3 : Algebra.{0, u1} Int R Int.instCommSemiringInt (Ring.toSemiring.{u1} R _inst_1)] [_inst_4 : Algebra.{0, u2} Int S Int.instCommSemiringInt (Ring.toSemiring.{u2} S _inst_2)], (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) -> (AlgHom.{0, u1, u2} Int R S Int.instCommSemiringInt (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S _inst_2) _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align ring_hom.to_int_alg_hom RingHom.toIntAlgHomₓ'. -/
/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by simp }
#align ring_hom.to_int_alg_hom RingHom.toIntAlgHom

#print RingHom.toRatAlgHom /-
/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `ring_hom.equiv_rat_alg_hom`. -/
def toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }
#align ring_hom.to_rat_alg_hom RingHom.toRatAlgHom
-/

/- warning: ring_hom.to_rat_alg_hom_to_ring_hom -> RingHom.toRatAlgHom_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.to_rat_alg_hom_to_ring_hom RingHom.toRatAlgHom_toRingHomₓ'. -/
@[simp]
theorem toRatAlgHom_toRingHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun x => rfl
#align ring_hom.to_rat_alg_hom_to_ring_hom RingHom.toRatAlgHom_toRingHom

end RingHom

section

variable {R S : Type _}

/- warning: alg_hom.to_ring_hom_to_rat_alg_hom -> AlgHom.toRingHom_toRatAlgHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.to_ring_hom_to_rat_alg_hom AlgHom.toRingHom_toRatAlgHomₓ'. -/
@[simp]
theorem AlgHom.toRingHom_toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) :
    (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun x => rfl
#align alg_hom.to_ring_hom_to_rat_alg_hom AlgHom.toRingHom_toRatAlgHom

#print RingHom.equivRatAlgHom /-
/-- The equivalence between `ring_hom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def RingHom.equivRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] : (R →+* S) ≃ (R →ₐ[ℚ] S)
    where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv := RingHom.toRatAlgHom_toRingHom
  right_inv := AlgHom.toRingHom_toRatAlgHom
#align ring_hom.equiv_rat_alg_hom RingHom.equivRatAlgHom
-/

end

namespace Algebra

variable (R : Type u) (A : Type v)

variable [CommSemiring R] [Semiring A] [Algebra R A]

#print Algebra.ofId /-
/-- `algebra_map` as an `alg_hom`. -/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }
#align algebra.of_id Algebra.ofId
-/

variable {R}

#print Algebra.ofId_apply /-
theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl
#align algebra.of_id_apply Algebra.ofId_apply
-/

end Algebra

namespace MulSemiringAction

variable {M G : Type _} (R A : Type _) [CommSemiring R] [Semiring A] [Algebra R A]

variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/- warning: mul_semiring_action.to_alg_hom -> MulSemiringAction.toAlgHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (R : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u2, u3} R A _inst_1 _inst_2] [_inst_4 : Monoid.{u1} M] [_inst_5 : MulSemiringAction.{u1, u3} M A _inst_4 _inst_2] [_inst_6 : SMulCommClass.{u1, u2, u3} M R A (SMulZeroClass.toHasSmul.{u1, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u3} M A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} M A _inst_4 (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} M A _inst_4 _inst_2 _inst_5)))) (SMulZeroClass.toHasSmul.{u2, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u2, u3} R A (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u3} R A (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (Module.toMulActionWithZero.{u2, u3} R A (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))) (Algebra.toModule.{u2, u3} R A _inst_1 _inst_2 _inst_3)))))], M -> (AlgHom.{u2, u3, u3} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3)
but is expected to have type
  forall {M : Type.{u1}} (R : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u2, u3} R A _inst_1 _inst_2] [_inst_4 : Monoid.{u1} M] [_inst_5 : MulSemiringAction.{u1, u3} M A _inst_4 _inst_2] [_inst_6 : SMulCommClass.{u1, u2, u3} M R A (SMulZeroClass.toSMul.{u1, u3} M A (MonoidWithZero.toZero.{u3} A (Semiring.toMonoidWithZero.{u3} A _inst_2)) (DistribSMul.toSMulZeroClass.{u1, u3} M A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} M A _inst_4 (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} M A _inst_4 _inst_2 _inst_5)))) (Algebra.toSMul.{u2, u3} R A _inst_1 _inst_2 _inst_3)], M -> (AlgHom.{u2, u3, u3} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3)
Case conversion may be inaccurate. Consider using '#align mul_semiring_action.to_alg_hom MulSemiringAction.toAlgHomₓ'. -/
/-- Each element of the monoid defines a algebra homomorphism.

This is a stronger version of `mul_semiring_action.to_ring_hom` and
`distrib_mul_action.to_linear_map`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  {
    MulSemiringAction.toRingHom _ _
      m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }
#align mul_semiring_action.to_alg_hom MulSemiringAction.toAlgHom

/- warning: mul_semiring_action.to_alg_hom_injective -> MulSemiringAction.toAlgHom_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (R : Type.{u2}) (A : Type.{u3}) [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_3 : Algebra.{u2, u3} R A _inst_1 _inst_2] [_inst_4 : Monoid.{u1} M] [_inst_5 : MulSemiringAction.{u1, u3} M A _inst_4 _inst_2] [_inst_6 : SMulCommClass.{u1, u2, u3} M R A (SMulZeroClass.toHasSmul.{u1, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u3} M A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} M A _inst_4 (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} M A _inst_4 _inst_2 _inst_5)))) (SMulZeroClass.toHasSmul.{u2, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u2, u3} R A (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u3} R A (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (Module.toMulActionWithZero.{u2, u3} R A (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))) (Algebra.toModule.{u2, u3} R A _inst_1 _inst_2 _inst_3)))))] [_inst_7 : FaithfulSMul.{u1, u3} M A (SMulZeroClass.toHasSmul.{u1, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u3} M A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u3} M A _inst_4 (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u3} M A _inst_4 _inst_2 _inst_5))))], Function.Injective.{succ u1, succ u3} M (AlgHom.{u2, u3, u3} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3) (MulSemiringAction.toAlgHom.{u1, u2, u3} M R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)
but is expected to have type
  forall {M : Type.{u3}} (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : Monoid.{u3} M] [_inst_5 : MulSemiringAction.{u3, u2} M A _inst_4 _inst_2] [_inst_6 : SMulCommClass.{u3, u1, u2} M R A (SMulZeroClass.toSMul.{u3, u2} M A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (DistribSMul.toSMulZeroClass.{u3, u2} M A (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (DistribMulAction.toDistribSMul.{u3, u2} M A _inst_4 (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u3, u2} M A _inst_4 _inst_2 _inst_5)))) (Algebra.toSMul.{u1, u2} R A _inst_1 _inst_2 _inst_3)] [_inst_7 : FaithfulSMul.{u3, u2} M A (SMulZeroClass.toSMul.{u3, u2} M A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (DistribSMul.toSMulZeroClass.{u3, u2} M A (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (DistribMulAction.toDistribSMul.{u3, u2} M A _inst_4 (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (MulSemiringAction.toDistribMulAction.{u3, u2} M A _inst_4 _inst_2 _inst_5))))], Function.Injective.{succ u3, succ u2} M (AlgHom.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_3 _inst_3) (MulSemiringAction.toAlgHom.{u3, u1, u2} M R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align mul_semiring_action.to_alg_hom_injective MulSemiringAction.toAlgHom_injectiveₓ'. -/
theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r
#align mul_semiring_action.to_alg_hom_injective MulSemiringAction.toAlgHom_injective

end MulSemiringAction

