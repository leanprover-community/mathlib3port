import Mathbin.Algebra.Module.Basic

/-!
# Instances on punit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/


universe u

namespace PUnit

variable (x y : PUnit.{u + 1}) (s : Set PUnit.{u + 1})

@[toAdditive]
instance : CommGroupₓ PUnit :=
  by 
    refineStruct
        { mul := fun _ _ => star, one := star, inv := fun _ => star, div := fun _ _ => star, npow := fun _ _ => star,
          zpow := fun _ _ => star, .. } <;>
      intros  <;> exact Subsingleton.elimₓ _ _

instance : CommRingₓ PUnit :=
  by 
    refine' { PUnit.commGroup, PUnit.addCommGroup with .. } <;> intros  <;> exact Subsingleton.elimₓ _ _

instance : CompleteBooleanAlgebra PUnit :=
  by 
    refine'
        { le := fun _ _ => True, le_antisymm := fun _ _ _ _ => Subsingleton.elimₓ _ _, lt := fun _ _ => False,
          lt_iff_le_not_le := fun _ _ => iff_of_false not_false fun H => H.2 trivialₓ, top := star, bot := star,
          sup := fun _ _ => star, inf := fun _ _ => star, sup := fun _ => star, inf := fun _ => star,
          Compl := fun _ => star, sdiff := fun _ _ => star, .. } <;>
      intros  <;>
        first |
          trivial|
          simp only [eq_iff_true_of_subsingleton]

instance : CanonicallyOrderedAddMonoid PUnit :=
  by 
    refine'
        { PUnit.commRing, PUnit.completeBooleanAlgebra with
          le_iff_exists_add := fun _ _ => iff_of_true _ ⟨star, Subsingleton.elimₓ _ _⟩, .. } <;>
      intros  <;> trivial

instance : LinearOrderedCancelAddCommMonoid PUnit :=
  { PUnit.canonicallyOrderedAddMonoid with add_left_cancel := fun _ _ _ _ => Subsingleton.elimₓ _ _,
    le_of_add_le_add_left := fun _ _ _ _ => trivialₓ, le_total := fun _ _ => Or.inl trivialₓ,
    decidableLe := fun _ _ => Decidable.true, DecidableEq := PUnit.decidableEq,
    decidableLt := fun _ _ => Decidable.false }

instance (R : Type u) [Semiringₓ R] : Module R PUnit :=
  Module.ofCore$
    by 
      refine' { PUnit.commRing with smul := fun _ _ => star, .. } <;> intros  <;> exact Subsingleton.elimₓ _ _

@[simp]
theorem zero_eq : (0 : PUnit) = star :=
  rfl

@[simp, toAdditive]
theorem one_eq : (1 : PUnit) = star :=
  rfl

@[simp]
theorem add_eq : (x+y) = star :=
  rfl

@[simp, toAdditive]
theorem mul_eq : (x*y) = star :=
  rfl

@[simp, toAdditive]
theorem div_eq : x / y = star :=
  rfl

@[simp]
theorem neg_eq : -x = star :=
  rfl

@[simp, toAdditive]
theorem inv_eq : x⁻¹ = star :=
  rfl

theorem smul_eq : x • y = star :=
  rfl

@[simp]
theorem top_eq : (⊤ : PUnit) = star :=
  rfl

@[simp]
theorem bot_eq : (⊥ : PUnit) = star :=
  rfl

@[simp]
theorem sup_eq : x⊔y = star :=
  rfl

@[simp]
theorem inf_eq : x⊓y = star :=
  rfl

@[simp]
theorem Sup_eq : Sup s = star :=
  rfl

@[simp]
theorem Inf_eq : Inf s = star :=
  rfl

@[simp]
protected theorem le : x ≤ y :=
  trivialₓ

@[simp]
theorem not_ltₓ : ¬x < y :=
  not_false

end PUnit

