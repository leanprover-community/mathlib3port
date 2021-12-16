import Mathbin.Algebra.Group.Defs 
import Mathbin.Data.Equiv.Basic 
import Mathbin.Logic.Nontrivial

/-!
# Multiplicative opposite and algebraic operations on it

In this file we define `mul_opposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It
inherits all additive algebraic structures on `α` (in other files), and reverses the order of
multipliers in multiplicative structures, i.e., `op (x * y) = op x * op y`, where `mul_opposite.op`
is the canonical map from `α` to `αᵐᵒᵖ`.

## Notation

`αᵐᵒᵖ = mul_opposite α`
-/


universe u v

open Function

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication.-/
def MulOpposite (α : Type u) : Type u :=
  α

-- ././Mathport/Syntax/Translate/Basic.lean:308:9: unsupported: advanced prec syntax
postfix:999 "ᵐᵒᵖ" => MulOpposite

namespace MulOpposite

variable {α : Type u}

/-- The element of `mul_opposite α` that represents `x : α`. -/
@[pp_nodot]
def op : α → αᵐᵒᵖ :=
  id

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot]
def unop : αᵐᵒᵖ → α :=
  id

@[simp]
theorem unop_op (x : α) : unop (op x) = x :=
  rfl

@[simp]
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl

@[simp]
theorem op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id :=
  rfl

@[simp]
theorem unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id :=
  rfl

/-- A recursor for `opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp]
protected def rec {F : ∀ X : αᵐᵒᵖ, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X :=
  fun X => h (unop X)

/-- The canonical bijection between `αᵐᵒᵖ` and `α`. -/
@[simps (config := { fullyApplied := ff }) apply symmApply]
def op_equiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩

theorem op_bijective : bijective (op : α → αᵐᵒᵖ) :=
  op_equiv.Bijective

theorem unop_bijective : bijective (unop : αᵐᵒᵖ → α) :=
  op_equiv.symm.Bijective

theorem op_injective : injective (op : α → αᵐᵒᵖ) :=
  op_bijective.Injective

theorem op_surjective : surjective (op : α → αᵐᵒᵖ) :=
  op_bijective.Surjective

theorem unop_injective : injective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.Injective

theorem unop_surjective : surjective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.Surjective

@[simp]
theorem op_inj {x y : α} : op x = op y ↔ x = y :=
  op_injective.eq_iff

@[simp]
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

variable (α)

instance [Nontrivial α] : Nontrivial (αᵐᵒᵖ) :=
  op_injective.Nontrivial

instance [Inhabited α] : Inhabited (αᵐᵒᵖ) :=
  ⟨op (default α)⟩

instance [Subsingleton α] : Subsingleton (αᵐᵒᵖ) :=
  unop_injective.Subsingleton

instance [Unique α] : Unique (αᵐᵒᵖ) :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty (αᵐᵒᵖ) :=
  Function.is_empty unop

instance [HasZero α] : HasZero (αᵐᵒᵖ) :=
  { zero := op 0 }

instance [HasOne α] : HasOne (αᵐᵒᵖ) :=
  { one := op 1 }

instance [Add α] : Add (αᵐᵒᵖ) :=
  { add := fun x y => op (unop x+unop y) }

instance [Sub α] : Sub (αᵐᵒᵖ) :=
  { sub := fun x y => op (unop x - unop y) }

instance [Neg α] : Neg (αᵐᵒᵖ) :=
  { neg := fun x => op$ -unop x }

instance [Mul α] : Mul (αᵐᵒᵖ) :=
  { mul := fun x y => op (unop y*unop x) }

instance [HasInv α] : HasInv (αᵐᵒᵖ) :=
  { inv := fun x => op$ unop x⁻¹ }

instance (R : Type _) [HasScalar R α] : HasScalar R (αᵐᵒᵖ) :=
  { smul := fun c x => op (c • unop x) }

section 

variable (α)

@[simp]
theorem op_zero [HasZero α] : op (0 : α) = 0 :=
  rfl

@[simp]
theorem unop_zero [HasZero α] : unop (0 : αᵐᵒᵖ) = 0 :=
  rfl

@[simp]
theorem op_one [HasOne α] : op (1 : α) = 1 :=
  rfl

@[simp]
theorem unop_one [HasOne α] : unop (1 : αᵐᵒᵖ) = 1 :=
  rfl

variable {α}

@[simp]
theorem op_add [Add α] (x y : α) : op (x+y) = op x+op y :=
  rfl

@[simp]
theorem unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x+y) = unop x+unop y :=
  rfl

@[simp]
theorem op_neg [Neg α] (x : α) : op (-x) = -op x :=
  rfl

@[simp]
theorem unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x :=
  rfl

@[simp]
theorem op_mul [Mul α] (x y : α) : op (x*y) = op y*op x :=
  rfl

@[simp]
theorem unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x*y) = unop y*unop x :=
  rfl

@[simp]
theorem op_inv [HasInv α] (x : α) : op (x⁻¹) = op x⁻¹ :=
  rfl

@[simp]
theorem unop_inv [HasInv α] (x : αᵐᵒᵖ) : unop (x⁻¹) = unop x⁻¹ :=
  rfl

@[simp]
theorem op_sub [Sub α] (x y : α) : op (x - y) = op x - op y :=
  rfl

@[simp]
theorem unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y :=
  rfl

@[simp]
theorem op_smul {R : Type _} [HasScalar R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl

@[simp]
theorem unop_smul {R : Type _} [HasScalar R α] (c : R) (a : αᵐᵒᵖ) : unop (c • a) = c • unop a :=
  rfl

end 

@[simp]
theorem unop_eq_zero_iff {α} [HasZero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_zero_iff {α} [HasZero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl

theorem unop_ne_zero_iff {α} [HasZero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
  not_congr$ unop_eq_zero_iff a

theorem op_ne_zero_iff {α} [HasZero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
  not_congr$ op_eq_zero_iff a

@[simp]
theorem unop_eq_one_iff {α} [HasOne α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_one_iff {α} [HasOne α] (a : α) : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' rfl

end MulOpposite

