/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathbin.Algebra.Jordan.Basic
import Mathbin.Algebra.Module.Basic

/-!
# Symmetrized algebra

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrization" i.e
$$
a \circ b = \frac{1}{2}(ab + ba)
$$

We provide the symmetrized version of a type `α` as `sym_alg α`, with notation `αˢʸᵐ`.

## Implementation notes

The approach taken here is inspired by algebra.opposites. We use Oxford Spellings
(IETF en-GB-oxendict).

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/


open Function

/-- The symmetrized algebra has the same underlying space as the original algebra.
-/
def SymAlg (α : Type _) : Type _ :=
  α

-- mathport name: «expr ˢʸᵐ»
postfix:max "ˢʸᵐ" => SymAlg

namespace SymAlg

variable {α : Type _}

/-- The element of `sym_alg α` that represents `a : α`. -/
@[match_pattern, pp_nodot]
def sym : α ≃ αˢʸᵐ :=
  Equiv.refl _

/-- The element of `α` represented by `x : αˢʸᵐ`. -/
@[pp_nodot]
def unsym : αˢʸᵐ ≃ α :=
  Equiv.refl _

@[simp]
theorem unsym_sym (a : α) : unsym (sym a) = a :=
  rfl

@[simp]
theorem sym_unsym (a : α) : sym (unsym a) = a :=
  rfl

@[simp]
theorem sym_comp_unsym : (sym : α → αˢʸᵐ) ∘ unsym = id :=
  rfl

@[simp]
theorem unsym_comp_sym : (unsym : αˢʸᵐ → α) ∘ Sym = id :=
  rfl

@[simp]
theorem sym_symm : (@sym α).symm = unsym :=
  rfl

@[simp]
theorem unsym_symm : (@unsym α).symm = Sym :=
  rfl

theorem sym_bijective : Bijective (sym : α → αˢʸᵐ) :=
  sym.Bijective

theorem unsym_bijective : Bijective (unsym : αˢʸᵐ → α) :=
  unsym.symm.Bijective

theorem sym_injective : Injective (sym : α → αˢʸᵐ) :=
  sym.Injective

theorem sym_surjective : Surjective (sym : α → αˢʸᵐ) :=
  sym.Surjective

theorem unsym_injective : Injective (unsym : αˢʸᵐ → α) :=
  unsym.Injective

theorem unsym_surjective : Surjective (unsym : αˢʸᵐ → α) :=
  unsym.Surjective

@[simp]
theorem sym_inj {a b : α} : sym a = sym b ↔ a = b :=
  sym_injective.eq_iff

@[simp]
theorem unsym_inj {a b : αˢʸᵐ} : unsym a = unsym b ↔ a = b :=
  unsym_injective.eq_iff

instance [Nontrivial α] : Nontrivial αˢʸᵐ :=
  sym_injective.Nontrivial

instance [Inhabited α] : Inhabited αˢʸᵐ :=
  ⟨sym default⟩

instance [Subsingleton α] : Subsingleton αˢʸᵐ :=
  unsym_injective.Subsingleton

instance [Unique α] : Unique αˢʸᵐ :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty αˢʸᵐ :=
  Function.is_empty unsym

@[to_additive]
instance [One α] : One αˢʸᵐ where one := sym 1

instance [Add α] : Add αˢʸᵐ where add a b := sym (unsym a + unsym b)

instance [Sub α] : Sub αˢʸᵐ where sub a b := sym (unsym a - unsym b)

instance [Neg α] : Neg αˢʸᵐ where neg a := sym (-unsym a)

-- Introduce the symmetrized multiplication
instance [Add α] [Mul α] [One α] [Invertible (2 : α)] :
    Mul αˢʸᵐ where mul a b := sym (⅟ 2 * (unsym a * unsym b + unsym b * unsym a))

@[to_additive]
instance [Inv α] : Inv αˢʸᵐ where inv a := Sym <| (unsym a)⁻¹

instance (R : Type _) [HasSmul R α] : HasSmul R αˢʸᵐ where smul r a := sym (r • unsym a)

@[simp, to_additive]
theorem sym_one [One α] : sym (1 : α) = 1 :=
  rfl

@[simp, to_additive]
theorem unsym_one [One α] : unsym (1 : αˢʸᵐ) = 1 :=
  rfl

@[simp]
theorem sym_add [Add α] (a b : α) : sym (a + b) = sym a + sym b :=
  rfl

@[simp]
theorem unsym_add [Add α] (a b : αˢʸᵐ) : unsym (a + b) = unsym a + unsym b :=
  rfl

@[simp]
theorem sym_sub [Sub α] (a b : α) : sym (a - b) = sym a - sym b :=
  rfl

@[simp]
theorem unsym_sub [Sub α] (a b : αˢʸᵐ) : unsym (a - b) = unsym a - unsym b :=
  rfl

@[simp]
theorem sym_neg [Neg α] (a : α) : sym (-a) = -sym a :=
  rfl

@[simp]
theorem unsym_neg [Neg α] (a : αˢʸᵐ) : unsym (-a) = -unsym a :=
  rfl

theorem mul_def [Add α] [Mul α] [One α] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    a * b = sym (⅟ 2 * (unsym a * unsym b + unsym b * unsym a)) := by rfl

theorem unsym_mul [Mul α] [Add α] [One α] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    unsym (a * b) = ⅟ 2 * (unsym a * unsym b + unsym b * unsym a) := by rfl

theorem sym_mul_sym [Mul α] [Add α] [One α] [Invertible (2 : α)] (a b : α) :
    sym a * sym b = sym (⅟ 2 * (a * b + b * a)) :=
  rfl

@[simp, to_additive]
theorem sym_inv [Inv α] (a : α) : sym a⁻¹ = (sym a)⁻¹ :=
  rfl

@[simp, to_additive]
theorem unsym_inv [Inv α] (a : αˢʸᵐ) : unsym a⁻¹ = (unsym a)⁻¹ :=
  rfl

@[simp]
theorem sym_smul {R : Type _} [HasSmul R α] (c : R) (a : α) : sym (c • a) = c • sym a :=
  rfl

@[simp]
theorem unsym_smul {R : Type _} [HasSmul R α] (c : R) (a : αˢʸᵐ) : unsym (c • a) = c • unsym a :=
  rfl

@[simp, to_additive]
theorem unsym_eq_one_iff [One α] (a : αˢʸᵐ) : a.unsym = 1 ↔ a = 1 :=
  unsym_injective.eq_iff' rfl

@[simp, to_additive]
theorem sym_eq_one_iff [One α] (a : α) : sym a = 1 ↔ a = 1 :=
  sym_injective.eq_iff' rfl

@[to_additive]
theorem unsym_ne_one_iff [One α] (a : αˢʸᵐ) : a.unsym ≠ (1 : α) ↔ a ≠ (1 : αˢʸᵐ) :=
  not_congr <| unsym_eq_one_iff a

@[to_additive]
theorem sym_ne_one_iff [One α] (a : α) : sym a ≠ (1 : αˢʸᵐ) ↔ a ≠ (1 : α) :=
  not_congr <| sym_eq_one_iff a

instance [AddCommSemigroup α] : AddCommSemigroup αˢʸᵐ :=
  unsym_injective.AddCommSemigroup _ unsym_add

instance [AddMonoid α] : AddMonoid αˢʸᵐ :=
  unsym_injective.AddMonoid _ unsym_zero unsym_add fun _ _ => rfl

instance [AddGroup α] : AddGroup αˢʸᵐ :=
  unsym_injective.AddGroup _ unsym_zero unsym_add unsym_neg unsym_sub (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommMonoid α] : AddCommMonoid αˢʸᵐ :=
  { SymAlg.addCommSemigroup, SymAlg.addMonoid with }

instance [AddCommGroup α] : AddCommGroup αˢʸᵐ :=
  { SymAlg.addCommMonoid, SymAlg.addGroup with }

instance {R : Type _} [Semiring R] [AddCommMonoid α] [Module R α] : Module R αˢʸᵐ :=
  Function.Injective.module R ⟨unsym, unsym_zero, unsym_add⟩ unsym_injective unsym_smul

instance [Mul α] [Add α] [One α] [Invertible (2 : α)] (a : α) [Invertible a] : Invertible (sym a) where
  invOf := sym (⅟ a)
  inv_of_mul_self := by rw [sym_mul_sym, mul_inv_of_self, inv_of_mul_self, ← bit0, inv_of_mul_self, sym_one]
  mul_inv_of_self := by rw [sym_mul_sym, mul_inv_of_self, inv_of_mul_self, ← bit0, inv_of_mul_self, sym_one]

@[simp]
theorem inv_of_sym [Mul α] [Add α] [One α] [Invertible (2 : α)] (a : α) [Invertible a] : ⅟ (sym a) = sym (⅟ a) :=
  rfl

instance [Semiring α] [Invertible (2 : α)] : NonAssocSemiring αˢʸᵐ :=
  { SymAlg.addCommMonoid with one := 1, mul := (· * ·), zero := 0,
    zero_mul := fun _ => by rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero, mul_zero, sym_zero],
    mul_zero := fun _ => by rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero, mul_zero, sym_zero],
    mul_one := fun _ => by rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, inv_of_mul_self_assoc, sym_unsym],
    one_mul := fun _ => by rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, inv_of_mul_self_assoc, sym_unsym],
    left_distrib := fun a b c =>
      match a, b, c with
      | Sym a, Sym b, Sym c => by
        rw [sym_mul_sym, sym_mul_sym, ← sym_add, sym_mul_sym, ← sym_add, mul_add a, add_mul _ _ a, add_add_add_comm,
          mul_add],
    right_distrib := fun a b c =>
      match a, b, c with
      | Sym a, Sym b, Sym c => by
        rw [sym_mul_sym, sym_mul_sym, ← sym_add, sym_mul_sym, ← sym_add, mul_add c, add_mul _ _ c, add_add_add_comm,
          mul_add] }

/-- The symmetrization of a real (unital, associative) algebra is a non-associative ring. -/
instance [Ring α] [Invertible (2 : α)] : NonAssocRing αˢʸᵐ :=
  { SymAlg.nonAssocSemiring, SymAlg.addCommGroup with }

/-! The squaring operation coincides for both multiplications -/


theorem unsym_mul_self [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ) : unsym (a * a) = unsym a * unsym a := by
  rw [mul_def, unsym_sym, ← two_mul, inv_of_mul_self_assoc]

theorem sym_mul_self [Semiring α] [Invertible (2 : α)] (a : α) : sym (a * a) = sym a * sym a := by
  rw [sym_mul_sym, ← two_mul, inv_of_mul_self_assoc]

theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [Invertible (2 : α)] (a b : αˢʸᵐ) : a * b = b * a := by
  rw [mul_def, mul_def, add_comm]

instance [Ring α] [Invertible (2 : α)] : IsCommJordan αˢʸᵐ where
  mul_comm := SymAlg.mul_comm
  lmul_comm_rmul_rmul a b := by
    -- Rearrange LHS
    have commute_half_left := fun a : α => (Commute.one_left a).bit0_left.inv_of_left.Eq
    rw [mul_def, mul_def a b, unsym_sym, ← mul_assoc, ← commute_half_left (unsym (a * a)), mul_assoc, mul_assoc, ←
      mul_add, ← mul_assoc, add_mul, mul_add (unsym (a * a)), ← add_assoc, ← mul_assoc, ← mul_assoc]
    -- Rearrange RHS
    nth_rw_rhs 0 [mul_def]
    nth_rw_rhs 0 [mul_def]
    nth_rw_rhs 2 [mul_def]
    rw [unsym_sym, sym_inj, ← mul_assoc, ← commute_half_left (unsym a), mul_assoc (⅟ 2) (unsym a),
      mul_assoc (⅟ 2) _ (unsym a), ← mul_add, ← mul_assoc]
    nth_rw_rhs 0 [mul_add (unsym a)]
    rw [add_mul, ← add_assoc, ← mul_assoc, ← mul_assoc]
    rw [unsym_mul_self]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_eq_zero, ← mul_sub]
    convert mul_zero (⅟ (2 : α) * ⅟ (2 : α))
    rw [add_sub_add_right_eq_sub, add_assoc, add_assoc, add_sub_add_left_eq_sub, add_comm, add_sub_add_right_eq_sub,
      sub_eq_zero]

end SymAlg

