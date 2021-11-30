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

-- error in Algebra.Opposites: ././Mathport/Syntax/Translate/Basic.lean:265:9: unsupported: advanced prec syntax
postfix `ᵐᵒᵖ`:std.prec.max_plus := mul_opposite

namespace MulOpposite

variable {α : Type u}

/-- The element of `mul_opposite α` that represents `x : α`. -/
@[pp_nodot]
def op : α → «expr ᵐᵒᵖ» α :=
  id

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot]
def unop : «expr ᵐᵒᵖ» α → α :=
  id

@[simp]
theorem unop_op (x : α) : unop (op x) = x :=
  rfl

@[simp]
theorem op_unop (x : «expr ᵐᵒᵖ» α) : op (unop x) = x :=
  rfl

@[simp]
theorem op_comp_unop : (op : α → «expr ᵐᵒᵖ» α) ∘ unop = id :=
  rfl

@[simp]
theorem unop_comp_op : (unop : «expr ᵐᵒᵖ» α → α) ∘ op = id :=
  rfl

/-- A recursor for `opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp]
protected def rec {F : ∀ X : «expr ᵐᵒᵖ» α, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X :=
  fun X => h (unop X)

/-- The canonical bijection between `αᵐᵒᵖ` and `α`. -/
@[simps (config := { fullyApplied := ff }) apply symmApply]
def op_equiv : α ≃ «expr ᵐᵒᵖ» α :=
  ⟨op, unop, unop_op, op_unop⟩

theorem op_bijective : bijective (op : α → «expr ᵐᵒᵖ» α) :=
  op_equiv.Bijective

theorem unop_bijective : bijective (unop : «expr ᵐᵒᵖ» α → α) :=
  op_equiv.symm.Bijective

theorem op_injective : injective (op : α → «expr ᵐᵒᵖ» α) :=
  op_bijective.Injective

theorem op_surjective : surjective (op : α → «expr ᵐᵒᵖ» α) :=
  op_bijective.Surjective

theorem unop_injective : injective (unop : «expr ᵐᵒᵖ» α → α) :=
  unop_bijective.Injective

theorem unop_surjective : surjective (unop : «expr ᵐᵒᵖ» α → α) :=
  unop_bijective.Surjective

@[simp]
theorem op_inj {x y : α} : op x = op y ↔ x = y :=
  op_injective.eq_iff

@[simp]
theorem unop_inj {x y : «expr ᵐᵒᵖ» α} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

variable (α)

instance [Nontrivial α] : Nontrivial («expr ᵐᵒᵖ» α) :=
  op_injective.Nontrivial

instance [Inhabited α] : Inhabited («expr ᵐᵒᵖ» α) :=
  ⟨op (default α)⟩

instance [Subsingleton α] : Subsingleton («expr ᵐᵒᵖ» α) :=
  unop_injective.Subsingleton

instance [Unique α] : Unique («expr ᵐᵒᵖ» α) :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty («expr ᵐᵒᵖ» α) :=
  Function.is_empty unop

instance [HasZero α] : HasZero («expr ᵐᵒᵖ» α) :=
  { zero := op 0 }

instance [HasOne α] : HasOne («expr ᵐᵒᵖ» α) :=
  { one := op 1 }

instance [Add α] : Add («expr ᵐᵒᵖ» α) :=
  { add := fun x y => op (unop x+unop y) }

instance [Sub α] : Sub («expr ᵐᵒᵖ» α) :=
  { sub := fun x y => op (unop x - unop y) }

instance [Neg α] : Neg («expr ᵐᵒᵖ» α) :=
  { neg := fun x => op$ -unop x }

instance [Mul α] : Mul («expr ᵐᵒᵖ» α) :=
  { mul := fun x y => op (unop y*unop x) }

instance [HasInv α] : HasInv («expr ᵐᵒᵖ» α) :=
  { inv := fun x => op$ unop x⁻¹ }

instance (R : Type _) [HasScalar R α] : HasScalar R («expr ᵐᵒᵖ» α) :=
  { smul := fun c x => op (c • unop x) }

section 

variable (α)

@[simp]
theorem op_zero [HasZero α] : op (0 : α) = 0 :=
  rfl

@[simp]
theorem unop_zero [HasZero α] : unop (0 : «expr ᵐᵒᵖ» α) = 0 :=
  rfl

@[simp]
theorem op_one [HasOne α] : op (1 : α) = 1 :=
  rfl

@[simp]
theorem unop_one [HasOne α] : unop (1 : «expr ᵐᵒᵖ» α) = 1 :=
  rfl

variable {α}

@[simp]
theorem op_add [Add α] (x y : α) : op (x+y) = op x+op y :=
  rfl

@[simp]
theorem unop_add [Add α] (x y : «expr ᵐᵒᵖ» α) : unop (x+y) = unop x+unop y :=
  rfl

@[simp]
theorem op_neg [Neg α] (x : α) : op (-x) = -op x :=
  rfl

@[simp]
theorem unop_neg [Neg α] (x : «expr ᵐᵒᵖ» α) : unop (-x) = -unop x :=
  rfl

@[simp]
theorem op_mul [Mul α] (x y : α) : op (x*y) = op y*op x :=
  rfl

@[simp]
theorem unop_mul [Mul α] (x y : «expr ᵐᵒᵖ» α) : unop (x*y) = unop y*unop x :=
  rfl

@[simp]
theorem op_inv [HasInv α] (x : α) : op (x⁻¹) = op x⁻¹ :=
  rfl

@[simp]
theorem unop_inv [HasInv α] (x : «expr ᵐᵒᵖ» α) : unop (x⁻¹) = unop x⁻¹ :=
  rfl

@[simp]
theorem op_sub [Sub α] (x y : α) : op (x - y) = op x - op y :=
  rfl

@[simp]
theorem unop_sub [Sub α] (x y : «expr ᵐᵒᵖ» α) : unop (x - y) = unop x - unop y :=
  rfl

@[simp]
theorem op_smul {R : Type _} [HasScalar R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl

@[simp]
theorem unop_smul {R : Type _} [HasScalar R α] (c : R) (a : «expr ᵐᵒᵖ» α) : unop (c • a) = c • unop a :=
  rfl

end 

@[simp]
theorem unop_eq_zero_iff {α} [HasZero α] (a : «expr ᵐᵒᵖ» α) : a.unop = (0 : α) ↔ a = (0 : «expr ᵐᵒᵖ» α) :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_zero_iff {α} [HasZero α] (a : α) : op a = (0 : «expr ᵐᵒᵖ» α) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl

theorem unop_ne_zero_iff {α} [HasZero α] (a : «expr ᵐᵒᵖ» α) : a.unop ≠ (0 : α) ↔ a ≠ (0 : «expr ᵐᵒᵖ» α) :=
  not_congr$ unop_eq_zero_iff a

theorem op_ne_zero_iff {α} [HasZero α] (a : α) : op a ≠ (0 : «expr ᵐᵒᵖ» α) ↔ a ≠ (0 : α) :=
  not_congr$ op_eq_zero_iff a

@[simp]
theorem unop_eq_one_iff {α} [HasOne α] (a : «expr ᵐᵒᵖ» α) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_one_iff {α} [HasOne α] (a : α) : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' rfl

end MulOpposite

