import Mathbin.Tactic.SplitIfs 
import Mathbin.Tactic.Simpa 
import Mathbin.Tactic.Congr 
import Mathbin.Algebra.Group.ToAdditive

/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `pi.lean` files elsewhere.
-/


open Function

universe u v₁ v₂ v₃

variable{I : Type u}

variable{α β γ : Type _}

variable{f : I → Type v₁}{g : I → Type v₂}{h : I → Type v₃}

variable(x y : ∀ i, f i)(i : I)

namespace Pi

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/


@[toAdditive]
instance HasOne [∀ i, HasOne$ f i] : HasOne (∀ i : I, f i) :=
  ⟨fun _ => 1⟩

@[simp, toAdditive]
theorem one_apply [∀ i, HasOne$ f i] : (1 : ∀ i, f i) i = 1 :=
  rfl

@[toAdditive]
theorem one_def [∀ i, HasOne$ f i] : (1 : ∀ i, f i) = fun i => 1 :=
  rfl

@[simp, toAdditive]
theorem const_one [HasOne β] : const α (1 : β) = 1 :=
  rfl

@[simp, toAdditive]
theorem one_comp [HasOne γ] (x : α → β) : (1 : β → γ) ∘ x = 1 :=
  rfl

@[simp, toAdditive]
theorem comp_one [HasOne β] (x : β → γ) : x ∘ 1 = const α (x 1) :=
  rfl

@[toAdditive]
instance Mul [∀ i, Mul$ f i] : Mul (∀ i : I, f i) :=
  ⟨fun f g i => f i*g i⟩

@[simp, toAdditive]
theorem mul_apply [∀ i, Mul$ f i] : (x*y) i = x i*y i :=
  rfl

@[toAdditive]
theorem mul_def [∀ i, Mul$ f i] : (x*y) = fun i => x i*y i :=
  rfl

@[simp, toAdditive]
theorem const_mul [Mul β] (a b : β) : (const α a*const α b) = const α (a*b) :=
  rfl

@[toAdditive]
theorem mul_comp [Mul γ] (x y : β → γ) (z : α → β) : (x*y) ∘ z = (x ∘ z)*y ∘ z :=
  rfl

@[toAdditive]
instance HasInv [∀ i, HasInv$ f i] : HasInv (∀ i : I, f i) :=
  ⟨fun f i => f i⁻¹⟩

@[simp, toAdditive]
theorem inv_apply [∀ i, HasInv$ f i] : (x⁻¹) i = x i⁻¹ :=
  rfl

@[toAdditive]
theorem inv_def [∀ i, HasInv$ f i] : x⁻¹ = fun i => x i⁻¹ :=
  rfl

@[toAdditive]
theorem const_inv [HasInv β] (a : β) : const α a⁻¹ = const α (a⁻¹) :=
  rfl

@[toAdditive]
theorem inv_comp [HasInv γ] (x : β → γ) (y : α → β) : x⁻¹ ∘ y = (x ∘ y)⁻¹ :=
  rfl

@[toAdditive]
instance Div [∀ i, Div$ f i] : Div (∀ i : I, f i) :=
  ⟨fun f g i => f i / g i⟩

@[simp, toAdditive]
theorem div_apply [∀ i, Div$ f i] : (x / y) i = x i / y i :=
  rfl

@[toAdditive]
theorem div_def [∀ i, Div$ f i] : x / y = fun i => x i / y i :=
  rfl

@[toAdditive]
theorem div_comp [Div γ] (x y : β → γ) (z : α → β) : (x / y) ∘ z = x ∘ z / y ∘ z :=
  rfl

@[simp, toAdditive]
theorem const_div [Div β] (a b : β) : const α a / const α b = const α (a / b) :=
  rfl

section 

variable[DecidableEq I]

variable[∀ i, HasZero (f i)][∀ i, HasZero (g i)][∀ i, HasZero (h i)]

/-- The function supported at `i`, with value `x` there. -/
def single (i : I) (x : f i) : ∀ i, f i :=
  Function.update 0 i x

@[simp]
theorem single_eq_same (i : I) (x : f i) : single i x i = x :=
  Function.update_same i x _

@[simp]
theorem single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : single i x i' = 0 :=
  Function.update_noteq h x _

/-- Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[simp]
theorem single_eq_of_ne' {i i' : I} (h : i ≠ i') (x : f i) : single i x i' = 0 :=
  single_eq_of_ne h.symm x

@[simp]
theorem single_zero (i : I) : single i (0 : f i) = 0 :=
  Function.update_eq_self _ _

/-- On non-dependent functions, `pi.single` can be expressed as an `ite` -/
theorem single_apply {β : Sort _} [HasZero β] (i : I) (x : β) (i' : I) : single i x i' = if i' = i then x else 0 :=
  Function.update_apply 0 i x i'

/-- On non-dependent functions, `pi.single` is symmetric in the two indices. -/
theorem single_comm {β : Sort _} [HasZero β] (i : I) (x : β) (i' : I) : single i x i' = single i' x i :=
  by 
    simp only [single_apply, eq_comm] <;> congr

theorem apply_single (f' : ∀ i, f i → g i) (hf' : ∀ i, f' i 0 = 0) (i : I) (x : f i) (j : I) :
  f' j (single i x j) = single i (f' i x) j :=
  by 
    simpa only [Pi.zero_apply, hf', single] using Function.apply_update f' 0 i x j

theorem apply_single₂ (f' : ∀ i, f i → g i → h i) (hf' : ∀ i, f' i 0 0 = 0) (i : I) (x : f i) (y : g i) (j : I) :
  f' j (single i x j) (single i y j) = single i (f' i x y) j :=
  by 
    byCases' h : j = i
    ·
      subst h 
      simp only [single_eq_same]
    ·
      simp only [single_eq_of_ne h, hf']

theorem single_op {g : I → Type _} [∀ i, HasZero (g i)] (op : ∀ i, f i → g i) (h : ∀ i, op i 0 = 0) (i : I) (x : f i) :
  single i (op i x) = fun j => op j (single i x j) :=
  Eq.symm$ funext$ apply_single op h i x

theorem single_op₂ {g₁ g₂ : I → Type _} [∀ i, HasZero (g₁ i)] [∀ i, HasZero (g₂ i)] (op : ∀ i, g₁ i → g₂ i → f i)
  (h : ∀ i, op i 0 0 = 0) (i : I) (x₁ : g₁ i) (x₂ : g₂ i) :
  single i (op i x₁ x₂) = fun j => op j (single i x₁ j) (single i x₂ j) :=
  Eq.symm$ funext$ apply_single₂ op h i x₁ x₂

variable(f)

theorem single_injective (i : I) : Function.Injective (single i : f i → ∀ i, f i) :=
  Function.update_injective _ i

end 

end Pi

namespace Function

section Extend

@[toAdditive]
theorem extend_one [HasOne γ] (f : α → β) : Function.extendₓ f (1 : α → γ) (1 : β → γ) = 1 :=
  funext$
    fun _ =>
      by 
        apply if_t_t _ _

@[toAdditive]
theorem extend_mul [Mul γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
  Function.extendₓ f (g₁*g₂) (e₁*e₂) = Function.extendₓ f g₁ e₁*Function.extendₓ f g₂ e₂ :=
  funext$
    fun _ =>
      by 
        convert (apply_dite2 (·*·) _ _ _ _ _).symm

@[toAdditive]
theorem extend_inv [HasInv γ] (f : α → β) (g : α → γ) (e : β → γ) :
  Function.extendₓ f (g⁻¹) (e⁻¹) = Function.extendₓ f g e⁻¹ :=
  funext$
    fun _ =>
      by 
        convert (apply_dite HasInv.inv _ _ _).symm

@[toAdditive]
theorem extend_div [Div γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
  Function.extendₓ f (g₁ / g₂) (e₁ / e₂) = Function.extendₓ f g₁ e₁ / Function.extendₓ f g₂ e₂ :=
  funext$
    fun _ =>
      by 
        convert (apply_dite2 (· / ·) _ _ _ _ _).symm

end Extend

theorem surjective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, surjective (F i)) :
  surjective fun x : ∀ i, f i => fun i => F i (x i) :=
  fun y => ⟨fun i => (hF i (y i)).some, funext$ fun i => (hF i (y i)).some_spec⟩

theorem injective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, injective (F i)) :
  injective fun x : ∀ i, f i => fun i => F i (x i) :=
  fun x y h => funext$ fun i => hF i$ (congr_funₓ h i : _)

theorem bijective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, bijective (F i)) :
  bijective fun x : ∀ i, f i => fun i => F i (x i) :=
  ⟨injective_pi_map fun i => (hF i).Injective, surjective_pi_map fun i => (hF i).Surjective⟩

end Function

theorem Subsingleton.pi_single_eq {α : Type _} [DecidableEq I] [Subsingleton I] [HasZero α] (i : I) (x : α) :
  Pi.single i x = fun _ => x :=
  funext$
    fun j =>
      by 
        rw [Subsingleton.elimₓ j i, Pi.single_eq_same]

