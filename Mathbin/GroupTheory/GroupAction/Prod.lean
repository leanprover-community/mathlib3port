import Mathbin.Algebra.Group.Prod 
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Prod instances for additive and multiplicative actions

This file defines instances for binary product of additive and multiplicative actions
-/


variable {M N P α β : Type _}

namespace Prod

section 

variable [HasScalar M α] [HasScalar M β] [HasScalar N α] [HasScalar N β] (a : M) (x : α × β)

@[toAdditive Prod.hasVadd]
instance : HasScalar M (α × β) :=
  ⟨fun a p => (a • p.1, a • p.2)⟩

@[simp, toAdditive]
theorem smul_fst : (a • x).1 = a • x.1 :=
  rfl

@[simp, toAdditive]
theorem smul_snd : (a • x).2 = a • x.2 :=
  rfl

@[simp, toAdditive]
theorem smul_mk (a : M) (b : α) (c : β) : a • (b, c) = (a • b, a • c) :=
  rfl

@[toAdditive]
theorem smul_def (a : M) (x : α × β) : a • x = (a • x.1, a • x.2) :=
  rfl

instance [HasScalar M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (α × β) :=
  ⟨fun x y z => mk.inj_iff.mpr ⟨smul_assoc _ _ _, smul_assoc _ _ _⟩⟩

@[toAdditive]
instance [SmulCommClass M N α] [SmulCommClass M N β] : SmulCommClass M N (α × β) :=
  { smul_comm := fun r s x => mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩ }

instance [HasScalar (Mᵐᵒᵖ) α] [HasScalar (Mᵐᵒᵖ) β] [IsCentralScalar M α] [IsCentralScalar M β] :
  IsCentralScalar M (α × β) :=
  ⟨fun r m => Prod.extₓ (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)⟩

@[toAdditive has_faithful_vadd_left]
instance has_faithful_scalar_left [HasFaithfulScalar M α] [Nonempty β] : HasFaithfulScalar M (α × β) :=
  ⟨fun x y h =>
      let ⟨b⟩ := ‹Nonempty β›
      eq_of_smul_eq_smul$
        fun a : α =>
          by 
            injection h (a, b)⟩

@[toAdditive has_faithful_vadd_right]
instance has_faithful_scalar_right [Nonempty α] [HasFaithfulScalar M β] : HasFaithfulScalar M (α × β) :=
  ⟨fun x y h =>
      let ⟨a⟩ := ‹Nonempty α›
      eq_of_smul_eq_smul$
        fun b : β =>
          by 
            injection h (a, b)⟩

end 

@[toAdditive]
instance smul_comm_class_both [Monoidₓ N] [Monoidₓ P] [HasScalar M N] [HasScalar M P] [SmulCommClass M N N]
  [SmulCommClass M P P] : SmulCommClass M (N × P) (N × P) :=
  ⟨fun c x y =>
      by 
        simp [smul_def, mul_def, mul_smul_comm]⟩

instance is_scalar_tower_both [Monoidₓ N] [Monoidₓ P] [HasScalar M N] [HasScalar M P] [IsScalarTower M N N]
  [IsScalarTower M P P] : IsScalarTower M (N × P) (N × P) :=
  ⟨fun c x y =>
      by 
        simp [smul_def, mul_def, smul_mul_assoc]⟩

@[toAdditive]
instance {m : Monoidₓ M} [MulAction M α] [MulAction M β] : MulAction M (α × β) :=
  { mul_smul := fun a₁ a₂ p => mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩,
    one_smul := fun ⟨b, c⟩ => mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩ }

instance {R M N : Type _} {r : Monoidₓ R} [AddMonoidₓ M] [AddMonoidₓ N] [DistribMulAction R M] [DistribMulAction R N] :
  DistribMulAction R (M × N) :=
  { smul_add := fun a p₁ p₂ => mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩,
    smul_zero := fun a => mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩ }

instance {R M N : Type _} {r : Monoidₓ R} [Monoidₓ M] [Monoidₓ N] [MulDistribMulAction R M] [MulDistribMulAction R N] :
  MulDistribMulAction R (M × N) :=
  { smul_mul := fun a p₁ p₂ => mk.inj_iff.mpr ⟨smul_mul' _ _ _, smul_mul' _ _ _⟩,
    smul_one := fun a => mk.inj_iff.mpr ⟨smul_one _, smul_one _⟩ }

end Prod

