import Mathbin.Algebra.Group.Defs 
import Mathbin.Logic.Function.Basic

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`algebra/group/defs.lean`.
-/


universe u

section Associative

variable {α : Type u} (f : α → α → α) [IsAssociative α f] (x y : α)

/--
Composing two associative operations of `f : α → α → α` on the left
is equal to an associative operation on the left.
-/
theorem comp_assoc_left : f x ∘ f y = f (f x y) :=
  by 
    ext z 
    rw [Function.comp_applyₓ, @IsAssociative.assoc _ f]

/--
Composing two associative operations of `f : α → α → α` on the right
is equal to an associative operation on the right.
-/
theorem comp_assoc_right : ((fun z => f z x) ∘ fun z => f z y) = fun z => f z (f y x) :=
  by 
    ext z 
    rw [Function.comp_applyₓ, @IsAssociative.assoc _ f]

end Associative

section Semigroupₓ

variable {α : Type _}

/--
Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp,
  toAdditive "Composing two additions on the left by `y` then `x`\nis equal to a addition on the left by `x + y`."]
theorem comp_mul_left [Semigroupₓ α] (x y : α) : (·*·) x ∘ (·*·) y = (·*·) (x*y) :=
  comp_assoc_left _ _ _

/--
Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp,
  toAdditive "Composing two additions on the right by `y` and `x`\nis equal to a addition on the right by `y + x`."]
theorem comp_mul_right [Semigroupₓ α] (x y : α) : ((·*x) ∘ ·*y) = ·*y*x :=
  comp_assoc_right _ _ _

end Semigroupₓ

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[toAdditive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} : ite P (a*b) 1 = ite P a 1*ite P b 1 :=
  by 
    byCases' h : P <;> simp [h]

@[toAdditive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} : ite P 1 (a*b) = ite P 1 a*ite P 1 b :=
  by 
    byCases' h : P <;> simp [h]

@[toAdditive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : (a*b) = 1) : a = 1 ↔ b = 1 :=
  by 
    split  <;>
      ·
        rintro rfl 
        simpa using h

@[toAdditive]
theorem one_mul_eq_id : (·*·) (1 : M) = id :=
  funext one_mulₓ

@[toAdditive]
theorem mul_one_eq_id : (·*(1 : M)) = id :=
  funext mul_oneₓ

end MulOneClass

section CommSemigroupₓ

variable {G : Type u} [CommSemigroupₓ G]

@[no_rsimp, toAdditive]
theorem mul_left_commₓ : ∀ a b c : G, (a*b*c) = b*a*c :=
  left_comm Mul.mul mul_commₓ mul_assocₓ

@[toAdditive]
theorem mul_right_commₓ : ∀ a b c : G, ((a*b)*c) = (a*c)*b :=
  right_comm Mul.mul mul_commₓ mul_assocₓ

@[toAdditive]
theorem mul_mul_mul_commₓ (a b c d : G) : ((a*b)*c*d) = (a*c)*b*d :=
  by 
    simp only [mul_left_commₓ, mul_assocₓ]

end CommSemigroupₓ

attribute [local simp] mul_assocₓ sub_eq_add_neg

section AddMonoidₓ

variable {M : Type u} [AddMonoidₓ M] {a b c : M}

@[simp]
theorem bit0_zero : bit0 (0 : M) = 0 :=
  add_zeroₓ _

@[simp]
theorem bit1_zero [HasOne M] : bit1 (0 : M) = 1 :=
  by 
    rw [bit1, bit0_zero, zero_addₓ]

end AddMonoidₓ

section CommMonoidₓ

variable {M : Type u} [CommMonoidₓ M] {x y z : M}

@[toAdditive]
theorem inv_unique (hy : (x*y) = 1) (hz : (x*z) = 1) : y = z :=
  left_inv_eq_right_invₓ (trans (mul_commₓ _ _) hy) hz

end CommMonoidₓ

section LeftCancelMonoid

variable {M : Type u} [LeftCancelMonoid M] {a b : M}

@[simp, toAdditive]
theorem mul_right_eq_self : (a*b) = a ↔ b = 1 :=
  calc (a*b) = a ↔ (a*b) = a*1 :=
    by 
      rw [mul_oneₓ]
    _ ↔ b = 1 := mul_left_cancel_iffₓ
    

@[simp, toAdditive]
theorem self_eq_mul_right : (a = a*b) ↔ b = 1 :=
  eq_comm.trans mul_right_eq_self

end LeftCancelMonoid

section RightCancelMonoid

variable {M : Type u} [RightCancelMonoid M] {a b : M}

@[simp, toAdditive]
theorem mul_left_eq_self : (a*b) = b ↔ a = 1 :=
  calc (a*b) = b ↔ (a*b) = 1*b :=
    by 
      rw [one_mulₓ]
    _ ↔ a = 1 := mul_right_cancel_iffₓ
    

@[simp, toAdditive]
theorem self_eq_mul_left : (b = a*b) ↔ a = 1 :=
  eq_comm.trans mul_left_eq_self

end RightCancelMonoid

section DivInvMonoidₓ

variable {G : Type u} [DivInvMonoidₓ G]

@[toAdditive]
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x :=
  by 
    rw [div_eq_mul_inv, one_mulₓ]

@[toAdditive]
theorem mul_one_div (x y : G) : (x*1 / y) = x / y :=
  by 
    rw [div_eq_mul_inv, one_mulₓ, div_eq_mul_inv]

theorem mul_div_assoc {a b c : G} : (a*b) / c = a*b / c :=
  by 
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assocₓ _ _ _]

theorem mul_div_assoc' (a b c : G) : (a*b / c) = (a*b) / c :=
  mul_div_assoc.symm

@[simp, toAdditive]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm

end DivInvMonoidₓ

section Groupₓ

variable {G : Type u} [Groupₓ G] {a b c : G}

@[simp, toAdditive]
theorem inv_mul_cancel_right (a b : G) : ((a*b⁻¹)*b) = a :=
  by 
    simp [mul_assocₓ]

@[simp, toAdditive neg_zero]
theorem one_inv : 1⁻¹ = (1 : G) :=
  inv_eq_of_mul_eq_oneₓ (one_mulₓ 1)

@[toAdditive]
theorem left_inverse_inv G [Groupₓ G] : Function.LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_invₓ

@[simp, toAdditive]
theorem inv_involutive : Function.Involutive (HasInv.inv : G → G) :=
  inv_invₓ

@[simp, toAdditive]
theorem inv_surjective : Function.Surjective (HasInv.inv : G → G) :=
  inv_involutive.Surjective

@[toAdditive]
theorem inv_injective : Function.Injective (HasInv.inv : G → G) :=
  inv_involutive.Injective

@[simp, toAdditive]
theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff

@[simp, toAdditive]
theorem mul_inv_cancel_left (a b : G) : (a*a⁻¹*b) = b :=
  by 
    rw [←mul_assocₓ, mul_right_invₓ, one_mulₓ]

@[toAdditive]
theorem mul_left_surjective (a : G) : Function.Surjective ((·*·) a) :=
  fun x => ⟨a⁻¹*x, mul_inv_cancel_left a x⟩

@[toAdditive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x => x*a :=
  fun x => ⟨x*a⁻¹, inv_mul_cancel_right x a⟩

@[simp, toAdditive neg_add_rev]
theorem mul_inv_rev (a b : G) : (a*b)⁻¹ = b⁻¹*a⁻¹ :=
  inv_eq_of_mul_eq_oneₓ$
    by 
      simp 

@[toAdditive]
theorem eq_inv_of_eq_inv (h : a = b⁻¹) : b = a⁻¹ :=
  by 
    simp [h]

@[toAdditive]
theorem eq_inv_of_mul_eq_one (h : (a*b) = 1) : a = b⁻¹ :=
  have  : a⁻¹ = b := inv_eq_of_mul_eq_oneₓ h 
  by 
    simp [this.symm]

@[toAdditive]
theorem eq_mul_inv_of_mul_eq (h : (a*c) = b) : a = b*c⁻¹ :=
  by 
    simp [h.symm]

@[toAdditive]
theorem eq_inv_mul_of_mul_eq (h : (b*a) = c) : a = b⁻¹*c :=
  by 
    simp [h.symm]

@[toAdditive]
theorem inv_mul_eq_of_eq_mul (h : b = a*c) : (a⁻¹*b) = c :=
  by 
    simp [h]

@[toAdditive]
theorem mul_inv_eq_of_eq_mul (h : a = c*b) : (a*b⁻¹) = c :=
  by 
    simp [h]

@[toAdditive]
theorem eq_mul_of_mul_inv_eq (h : (a*c⁻¹) = b) : a = b*c :=
  by 
    simp [h.symm]

@[toAdditive]
theorem eq_mul_of_inv_mul_eq (h : (b⁻¹*a) = c) : a = b*c :=
  by 
    simp [h.symm, mul_inv_cancel_left]

@[toAdditive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹*c) : (a*b) = c :=
  by 
    rw [h, mul_inv_cancel_left]

@[toAdditive]
theorem mul_eq_of_eq_mul_inv (h : a = c*b⁻¹) : (a*b) = c :=
  by 
    simp [h]

@[simp, toAdditive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  by 
    rw [←@inv_inj _ _ a 1, one_inv]

@[simp, toAdditive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  by 
    rw [eq_comm, inv_eq_one]

@[toAdditive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  not_congr inv_eq_one

@[toAdditive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

@[toAdditive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  eq_comm.trans$ eq_inv_iff_eq_inv.trans eq_comm

@[toAdditive]
theorem mul_eq_one_iff_eq_inv : (a*b) = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one,
    fun h =>
      by 
        rw [h, mul_left_invₓ]⟩

@[toAdditive]
theorem mul_eq_one_iff_inv_eq : (a*b) = 1 ↔ a⁻¹ = b :=
  by 
    rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

@[toAdditive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ (a*b) = 1 :=
  mul_eq_one_iff_eq_inv.symm

@[toAdditive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ (a*b) = 1 :=
  mul_eq_one_iff_inv_eq.symm

@[toAdditive]
theorem eq_mul_inv_iff_mul_eq : (a = b*c⁻¹) ↔ (a*c) = b :=
  ⟨fun h =>
      by 
        rw [h, inv_mul_cancel_right],
    fun h =>
      by 
        rw [←h, mul_inv_cancel_rightₓ]⟩

@[toAdditive]
theorem eq_inv_mul_iff_mul_eq : (a = b⁻¹*c) ↔ (b*a) = c :=
  ⟨fun h =>
      by 
        rw [h, mul_inv_cancel_left],
    fun h =>
      by 
        rw [←h, inv_mul_cancel_leftₓ]⟩

@[toAdditive]
theorem inv_mul_eq_iff_eq_mul : (a⁻¹*b) = c ↔ b = a*c :=
  ⟨fun h =>
      by 
        rw [←h, mul_inv_cancel_left],
    fun h =>
      by 
        rw [h, inv_mul_cancel_leftₓ]⟩

@[toAdditive]
theorem mul_inv_eq_iff_eq_mul : (a*b⁻¹) = c ↔ a = c*b :=
  ⟨fun h =>
      by 
        rw [←h, inv_mul_cancel_right],
    fun h =>
      by 
        rw [h, mul_inv_cancel_rightₓ]⟩

@[toAdditive]
theorem mul_inv_eq_one : (a*b⁻¹) = 1 ↔ a = b :=
  by 
    rw [mul_eq_one_iff_eq_inv, inv_invₓ]

@[toAdditive]
theorem inv_mul_eq_one : (a⁻¹*b) = 1 ↔ a = b :=
  by 
    rw [mul_eq_one_iff_eq_inv, inv_inj]

@[toAdditive]
theorem div_left_injective : Function.Injective fun a => a / b :=
  by 
    simpa only [div_eq_mul_inv] using fun a a' h => mul_left_injective (b⁻¹) h

@[toAdditive]
theorem div_right_injective : Function.Injective fun a => b / a :=
  by 
    simpa only [div_eq_mul_inv] using fun a a' h => inv_injective (mul_right_injective b h)

@[simp, toAdditive sub_zero]
theorem div_one' (a : G) : a / 1 = a :=
  calc a / 1 = a*1⁻¹ := div_eq_mul_inv a 1
    _ = a*1 := congr_argₓ _ one_inv 
    _ = a := mul_oneₓ a
    

@[simp, toAdditive neg_sub]
theorem inv_div' (a b : G) : (a / b)⁻¹ = b / a :=
  inv_eq_of_mul_eq_oneₓ
    (by 
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assocₓ, inv_mul_cancel_leftₓ, mul_right_invₓ])

@[simp, toAdditive sub_add_cancel]
theorem div_mul_cancel' (a b : G) : ((a / b)*b) = a :=
  by 
    rw [div_eq_mul_inv, inv_mul_cancel_right a b]

end Groupₓ

section AddGroupₓ

variable {G : Type u} [AddGroupₓ G] {a b c d : G}

@[simp]
theorem sub_self (a : G) : a - a = 0 :=
  by 
    rw [sub_eq_add_neg, add_right_negₓ a]

@[simp]
theorem add_sub_cancel (a b : G) : (a+b) - b = a :=
  by 
    rw [sub_eq_add_neg, add_neg_cancel_rightₓ a b]

theorem add_sub_assoc (a b c : G) : (a+b) - c = a+b - c :=
  by 
    rw [sub_eq_add_neg, add_assocₓ, ←sub_eq_add_neg]

theorem eq_of_sub_eq_zero (h : a - b = 0) : a = b :=
  calc a = (a - b)+b := (sub_add_cancel a b).symm 
    _ = b :=
    by 
      rw [h, zero_addₓ]
    

theorem sub_ne_zero_of_ne (h : a ≠ b) : a - b ≠ 0 :=
  mt eq_of_sub_eq_zero h

@[simp]
theorem sub_neg_eq_add (a b : G) : a - -b = a+b :=
  by 
    rw [sub_eq_add_neg, neg_negₓ]

attribute [local simp] add_assocₓ

theorem add_sub (a b c : G) : (a+b - c) = (a+b) - c :=
  by 
    simp 

theorem sub_add_eq_sub_sub_swap (a b c : G) : (a - b+c) = a - c - b :=
  by 
    simp 

@[simp]
theorem add_sub_add_right_eq_sub (a b c : G) : ((a+c) - b+c) = a - b :=
  by 
    rw [sub_add_eq_sub_sub_swap] <;> simp 

theorem eq_sub_of_add_eq (h : (a+c) = b) : a = b - c :=
  by 
    simp [←h]

theorem sub_eq_of_eq_add (h : a = c+b) : a - b = c :=
  by 
    simp [h]

theorem eq_add_of_sub_eq (h : a - c = b) : a = b+c :=
  by 
    simp [←h]

theorem add_eq_of_eq_sub (h : a = c - b) : (a+b) = c :=
  by 
    simp [h]

@[simp]
theorem sub_right_inj : a - b = a - c ↔ b = c :=
  sub_right_injective.eq_iff

@[simp]
theorem sub_left_inj : b - a = c - a ↔ b = c :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_left_injₓ _

@[simp]
theorem sub_add_sub_cancel (a b c : G) : ((a - b)+b - c) = a - c :=
  by 
    rw [←add_sub_assoc, sub_add_cancel]

@[simp]
theorem sub_sub_sub_cancel_right (a b c : G) : a - c - (b - c) = a - b :=
  by 
    rw [←neg_sub c b, sub_neg_eq_add, sub_add_sub_cancel]

theorem sub_sub_assoc_swap : a - (b - c) = (a+c) - b :=
  by 
    simp 

theorem sub_eq_zero : a - b = 0 ↔ a = b :=
  ⟨eq_of_sub_eq_zero,
    fun h =>
      by 
        rw [h, sub_self]⟩

alias sub_eq_zero ↔ _ sub_eq_zero_of_eq

theorem sub_ne_zero : a - b ≠ 0 ↔ a ≠ b :=
  not_congr sub_eq_zero

@[simp]
theorem sub_eq_self : a - b = a ↔ b = 0 :=
  by 
    rw [sub_eq_add_neg, add_right_eq_selfₓ, neg_eq_zero]

theorem eq_sub_iff_add_eq : a = b - c ↔ (a+c) = b :=
  by 
    rw [sub_eq_add_neg, eq_add_neg_iff_add_eq]

theorem sub_eq_iff_eq_add : a - b = c ↔ a = c+b :=
  by 
    rw [sub_eq_add_neg, add_neg_eq_iff_eq_add]

theorem eq_iff_eq_of_sub_eq_sub (H : a - b = c - d) : a = b ↔ c = d :=
  by 
    rw [←sub_eq_zero, H, sub_eq_zero]

theorem left_inverse_sub_add_left (c : G) : Function.LeftInverse (fun x => x - c) fun x => x+c :=
  fun x => add_sub_cancel x c

theorem left_inverse_add_left_sub (c : G) : Function.LeftInverse (fun x => x+c) fun x => x - c :=
  fun x => sub_add_cancel x c

theorem left_inverse_add_right_neg_add (c : G) : Function.LeftInverse (fun x => c+x) fun x => (-c)+x :=
  fun x => add_neg_cancel_left c x

theorem left_inverse_neg_add_add_right (c : G) : Function.LeftInverse (fun x => (-c)+x) fun x => c+x :=
  fun x => neg_add_cancel_leftₓ c x

end AddGroupₓ

section CommGroupₓ

variable {G : Type u} [CommGroupₓ G]

@[toAdditive neg_add]
theorem mul_inv (a b : G) : (a*b)⁻¹ = a⁻¹*b⁻¹ :=
  by 
    rw [mul_inv_rev, mul_commₓ]

@[toAdditive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b*c) : a / b = c :=
  by 
    rw [h, div_eq_mul_inv, mul_commₓ, inv_mul_cancel_leftₓ]

@[toAdditive]
theorem div_mul_comm (a b c d : G) : ((a / b)*c / d) = (a*c) / b*d :=
  by 
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, mul_assocₓ, mul_assocₓ, mul_left_cancel_iffₓ,
      mul_commₓ, mul_assocₓ]

end CommGroupₓ

section AddCommGroupₓ

variable {G : Type u} [AddCommGroupₓ G] {a b c d : G}

attribute [local simp] add_assocₓ add_commₓ add_left_commₓ sub_eq_add_neg

theorem sub_add_eq_sub_sub (a b c : G) : (a - b+c) = a - b - c :=
  by 
    simp 

theorem neg_add_eq_sub (a b : G) : ((-a)+b) = b - a :=
  by 
    simp 

theorem sub_add_eq_add_sub (a b c : G) : ((a - b)+c) = (a+c) - b :=
  by 
    simp 

theorem sub_sub (a b c : G) : a - b - c = a - b+c :=
  by 
    simp 

theorem sub_add (a b c : G) : ((a - b)+c) = a - (b - c) :=
  by 
    simp 

@[simp]
theorem add_sub_add_left_eq_sub (a b c : G) : ((c+a) - c+b) = a - b :=
  by 
    simp 

theorem eq_sub_of_add_eq' (h : (c+a) = b) : a = b - c :=
  by 
    simp [h.symm]

theorem eq_add_of_sub_eq' (h : a - b = c) : a = b+c :=
  by 
    simp [h.symm]

theorem add_eq_of_eq_sub' (h : b = c - a) : (a+b) = c :=
  by 
    simp [h]
    rw [add_commₓ c, add_neg_cancel_left]

theorem sub_sub_self (a b : G) : a - (a - b) = b :=
  by 
    simpa using add_neg_cancel_left a b

theorem add_sub_comm (a b c d : G) : ((a+b) - c+d) = (a - c)+b - d :=
  by 
    simp 

theorem sub_eq_sub_add_sub (a b c : G) : a - b = (c - b)+a - c :=
  by 
    simp 
    rw [add_left_commₓ c]
    simp 

theorem neg_neg_sub_neg (a b : G) : -(-a - -b) = a - b :=
  by 
    simp 

@[simp]
theorem sub_sub_cancel (a b : G) : a - (a - b) = b :=
  sub_sub_self a b

@[simp]
theorem sub_sub_cancel_left (a b : G) : a - b - a = -b :=
  by 
    simp 

theorem sub_eq_neg_add (a b : G) : a - b = (-b)+a :=
  by 
    rw [sub_eq_add_neg, add_commₓ _ _]

theorem neg_add' (a b : G) : (-a+b) = -a - b :=
  by 
    rw [sub_eq_add_neg, neg_add a b]

@[simp]
theorem neg_sub_neg (a b : G) : -a - -b = b - a :=
  by 
    simp [sub_eq_neg_add, add_commₓ]

theorem eq_sub_iff_add_eq' : a = b - c ↔ (c+a) = b :=
  by 
    rw [eq_sub_iff_add_eq, add_commₓ]

theorem sub_eq_iff_eq_add' : a - b = c ↔ a = b+c :=
  by 
    rw [sub_eq_iff_eq_add, add_commₓ]

@[simp]
theorem add_sub_cancel' (a b : G) : (a+b) - a = b :=
  by 
    rw [sub_eq_neg_add, neg_add_cancel_leftₓ]

@[simp]
theorem add_sub_cancel'_right (a b : G) : (a+b - a) = b :=
  by 
    rw [←add_sub_assoc, add_sub_cancel']

@[simp]
theorem sub_add_cancel' (a b : G) : (a - a+b) = -b :=
  by 
    rw [←neg_sub, add_sub_cancel']

theorem add_add_neg_cancel'_right (a b : G) : (a+b+-a) = b :=
  by 
    rw [←sub_eq_add_neg, add_sub_cancel'_right a b]

theorem sub_right_comm (a b c : G) : a - b - c = a - c - b :=
  by 
    repeat' 
      rw [sub_eq_add_neg]
    exact add_right_commₓ _ _ _

@[simp]
theorem add_add_sub_cancel (a b c : G) : ((a+c)+b - c) = a+b :=
  by 
    rw [add_assocₓ, add_sub_cancel'_right]

@[simp]
theorem sub_add_add_cancel (a b c : G) : ((a - c)+b+c) = a+b :=
  by 
    rw [add_left_commₓ, sub_add_cancel, add_commₓ]

@[simp]
theorem sub_add_sub_cancel' (a b c : G) : ((a - b)+c - a) = c - b :=
  by 
    rw [add_commₓ] <;> apply sub_add_sub_cancel

@[simp]
theorem add_sub_sub_cancel (a b c : G) : (a+b) - (a - c) = b+c :=
  by 
    rw [←sub_add, add_sub_cancel']

@[simp]
theorem sub_sub_sub_cancel_left (a b c : G) : c - a - (c - b) = b - a :=
  by 
    rw [←neg_sub b c, sub_neg_eq_add, add_commₓ, sub_add_sub_cancel]

theorem sub_eq_sub_iff_add_eq_add : a - b = c - d ↔ (a+d) = c+b :=
  by 
    rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, eq_comm, sub_eq_iff_eq_add']
    simp only [add_commₓ, eq_comm]

theorem sub_eq_sub_iff_sub_eq_sub : a - b = c - d ↔ a - c = b - d :=
  by 
    rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, sub_eq_iff_eq_add', add_sub_assoc]

end AddCommGroupₓ

