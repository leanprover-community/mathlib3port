import Mathbin.Algebra.Ring.Ulift
import Mathbin.Data.Equiv.Module

/-!
# `ulift` instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.module_equiv : ulift M ≃ₗ[R] M`.

-/


namespace Ulift

universe u v w

variable {R : Type u}

variable {M : Type v}

variable {N : Type w}

instance has_scalar_left [HasScalar R M] : HasScalar (Ulift R) M :=
  ⟨fun s x => s.down • x⟩

@[simp]
theorem smul_down [HasScalar R M] (s : Ulift R) (x : M) : s • x = s.down • x :=
  rfl

@[simp]
theorem smul_down' [HasScalar R M] (s : R) (x : Ulift M) : (s • x).down = s • x.down :=
  rfl

instance IsScalarTower [HasScalar R M] [HasScalar M N] [HasScalar R N] [IsScalarTower R M N] :
    IsScalarTower (Ulift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩

instance is_scalar_tower' [HasScalar R M] [HasScalar M N] [HasScalar R N] [IsScalarTower R M N] :
    IsScalarTower R (Ulift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩

instance is_scalar_tower'' [HasScalar R M] [HasScalar M N] [HasScalar R N] [IsScalarTower R M N] :
    IsScalarTower R M (Ulift N) :=
  ⟨fun x y z =>
    show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by
      rw [smul_assoc]⟩

instance [HasScalar R M] [HasScalar (Rᵐᵒᵖ) M] [IsCentralScalar R M] : IsCentralScalar R (Ulift M) :=
  ⟨fun r m => congr_argₓ up <| op_smul_eq_smul r m.down⟩

instance MulAction [Monoidₓ R] [MulAction R M] : MulAction (Ulift R) M where
  smul := · • ·
  mul_smul := fun r s f => by
    cases r
    cases s
    simp [mul_smul]
  one_smul := fun f => by
    simp [one_smul]

instance mul_action' [Monoidₓ R] [MulAction R M] : MulAction R (Ulift M) where
  smul := · • ·
  mul_smul := fun r s f => by
    cases f
    ext
    simp [mul_smul]
  one_smul := fun f => by
    ext
    simp [one_smul]

instance DistribMulAction [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction (Ulift R) M :=
  { Ulift.mulAction with
    smul_zero := fun c => by
      cases c
      simp [smul_zero],
    smul_add := fun c f g => by
      cases c
      simp [smul_add] }

instance distrib_mul_action' [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R (Ulift M) :=
  { Ulift.mulAction' with
    smul_zero := fun c => by
      ext
      simp [smul_zero],
    smul_add := fun c f g => by
      ext
      simp [smul_add] }

instance MulDistribMulAction [Monoidₓ R] [Monoidₓ M] [MulDistribMulAction R M] : MulDistribMulAction (Ulift R) M :=
  { Ulift.mulAction with
    smul_one := fun c => by
      cases c
      simp [smul_one],
    smul_mul := fun c f g => by
      cases c
      simp [smul_mul'] }

instance mul_distrib_mul_action' [Monoidₓ R] [Monoidₓ M] [MulDistribMulAction R M] : MulDistribMulAction R (Ulift M) :=
  { Ulift.mulAction' with
    smul_one := fun c => by
      ext
      simp [smul_one],
    smul_mul := fun c f g => by
      ext
      simp [smul_mul'] }

instance Module [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module (Ulift R) M :=
  { Ulift.distribMulAction with
    add_smul := fun c f g => by
      cases c
      simp [add_smul],
    zero_smul := fun f => by
      simp [zero_smul] }

instance module' [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module R (Ulift M) where
  add_smul := by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    apply zero_smul

/-- The `R`-linear equivalence between `ulift M` and `M`.
-/
def module_equiv [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Ulift M ≃ₗ[R] M where
  toFun := Ulift.down
  invFun := Ulift.up
  map_smul' := fun r x => rfl
  map_add' := fun x y => rfl
  left_inv := by
    tidy
  right_inv := by
    tidy

end Ulift

