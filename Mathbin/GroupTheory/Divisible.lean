/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.GroupTheory.GroupAction.Pi
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.Algebra.Group.Pi

/-!
# Divisible Group and rootable group

In this file, we define a divisible add monoid and a rootable monoid with some basic properties.

## Main definition

* `divisible_by A α`: An additive monoid `A` is said to be divisible by `α` iff for all `n ≠ 0 ∈ α`
  and `y ∈ A`, there is an `x ∈ A` such that `n • x = y`. In this file, we adopt a constructive
  approach, i.e. we ask for an explicit `div : A → α → A` function such that `div a 0 = 0` and
  `n • div a n = a` for all `n ≠ 0 ∈ α`.
* `rootable_by A α`: A monoid `A` is said to be rootable by `α` iff for all `n ≠ 0 ∈ α` and `y ∈ A`,
  there is an `x ∈ A` such that `x^n = y`. In this file, we adopt a constructive approach, i.e. we
  ask for an explicit `root : A → α → A` function such that `root a 0 = 1` and `(root a n)ⁿ = a` for
  all `n ≠ 0 ∈ α`.

## Main results

For additive monoids and groups:

* `divisible_by_of_smul_right_surj` : the constructive definition of divisiblity is implied by
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `smul_right_surj_of_divisible_by` : the constructive definition of divisiblity implies
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `prod.divisible_by` : `A × B` is divisible for any two divisible additive monoids.
* `pi.divisible_by` : any product of divisble additive monoids is divisible.
* `add_group.divisible_by_int_of_divisible_by_nat` : for additive groups, int divisiblity is implied
  by nat divisiblity.
* `add_group.divisible_by_nat_of_divisible_by_int` : for additive groups, nat divisiblity is implied
  by int divisiblity.
* `add_comm_group.divisible_by_int_of_smul_top_eq_top`: the constructive definition of divisiblity
  is implied by the condition that `n • A = A` for all `n ≠ 0`.
* `add_comm_group.smul_top_eq_top_of_divisible_by_int`: the constructive definition of divisiblity
  implies the condition that `n • A = A` for all `n ≠ 0`.
* `divisible_by_int_of_char_zero` : any field of characteristic zero is divisible.
* `quotient_add_group.divisible_by` : quotient group of divisible group is divisible.
* `function.surjective.divisible_by` : if `A` is divisible and `A →+ B` is surjective, then `B`
  is divisible.

and their multiplicative counterparts:

* `rootable_by_of_pow_left_surj` : the constructive definition of rootablity is implied by the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `pow_left_surj_of_rootable_by` : the constructive definition of rootablity implies the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `prod.rootable_by` : any product of two rootable monoids is rootable.
* `pi.rootable_by` : any product of rootable monoids is rootable.
* `group.rootable_by_int_of_rootable_by_nat` : in groups, int rootablity is implied by nat
  rootablity.
* `group.rootable_by_nat_of_rootable_by_int` : in groups, nat rootablity is implied by int
  rootablity.
* `quotient_group.rootable_by` : quotient group of rootable group is rootable.
* `function.surjective.rootable_by` : if `A` is rootable and `A →* B` is surjective, then `B` is
  rootable.

TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/


open Pointwise

section AddMonoidₓ

variable (A α : Type _) [AddMonoidₓ A] [HasSmul α A] [Zero α]

/-- An `add_monoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `div : A → α → A` function such that
* `div a 0 = 0` for all `a ∈ A`
* `n • div a n = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
class DivisibleBy where
  div : A → α → A
  div_zero : ∀ a, div a 0 = 0
  div_cancel : ∀ {n : α} (a : A), n ≠ 0 → n • div a n = a

end AddMonoidₓ

section Monoidₓ

variable (A α : Type _) [Monoidₓ A] [Pow A α] [Zero α]

/-- A `monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `root : A → α → A` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive]
class RootableBy where
  root : A → α → A
  root_zero : ∀ a, root a 0 = 1
  root_cancel : ∀ {n : α} (a : A), n ≠ 0 → root a n ^ n = a

@[to_additive smul_right_surj_of_divisible_by]
theorem pow_left_surj_of_rootable_by [RootableBy A α] {n : α} (hn : n ≠ 0) :
    Function.Surjective (fun a => pow a n : A → A) := fun x => ⟨RootableBy.root x n, RootableBy.root_cancel _ hn⟩

/-- A `monoid A` is `α`-rootable iff the `pow _ n` function is surjective, i.e. the constructive version
implies the textbook approach.
-/
@[to_additive divisibleByOfSmulRightSurj
      "An `add_monoid A` is `α`-divisible iff `n • _` is a surjective function, i.e. the constructive\nversion implies the textbook approach."]
noncomputable def rootableByOfPowLeftSurj (H : ∀ {n : α}, n ≠ 0 → Function.Surjective (fun a => a ^ n : A → A)) :
    RootableBy A α where
  root := fun a n => @dite _ (n = 0) (Classical.dec _) (fun _ => (1 : A)) fun hn => (H hn a).some
  root_zero := fun _ => by
    classical <;> exact dif_pos rfl
  root_cancel := fun n a hn => by
    rw [dif_neg hn] <;> exact (H hn a).some_spec

section Pi

variable {ι β : Type _} (B : ι → Type _) [∀ i : ι, Pow (B i) β]

variable [Zero β] [∀ i : ι, Monoidₓ (B i)] [∀ i, RootableBy (B i) β]

@[to_additive]
instance Pi.rootableBy : RootableBy (∀ i, B i) β where
  root := fun x n i => RootableBy.root (x i) n
  root_zero := fun x => funext fun i => RootableBy.root_zero _
  root_cancel := fun n x hn => funext fun i => RootableBy.root_cancel _ hn

end Pi

section Prod

variable {β B B' : Type _} [Pow B β] [Pow B' β]

variable [Zero β] [Monoidₓ B] [Monoidₓ B'] [RootableBy B β] [RootableBy B' β]

@[to_additive]
instance Prod.rootableBy : RootableBy (B × B') β where
  root := fun p n => (RootableBy.root p.1 n, RootableBy.root p.2 n)
  root_zero := fun p => Prod.extₓ (RootableBy.root_zero _) (RootableBy.root_zero _)
  root_cancel := fun n p hn => Prod.extₓ (RootableBy.root_cancel _ hn) (RootableBy.root_cancel _ hn)

end Prod

end Monoidₓ

namespace AddCommGroupₓ

variable (A : Type _) [AddCommGroupₓ A]

theorem smul_top_eq_top_of_divisible_by_int [DivisibleBy A ℤ] {n : ℤ} (hn : n ≠ 0) : n • (⊤ : AddSubgroup A) = ⊤ :=
  (AddSubgroup.map_top_of_surjective _) fun a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel _ hn⟩

/-- If for all `n ≠ 0 ∈ ℤ`, `n • A = A`, then `A` is divisible.
-/
noncomputable def divisibleByIntOfSmulTopEqTop (H : ∀ {n : ℤ} (hn : n ≠ 0), n • (⊤ : AddSubgroup A) = ⊤) :
    DivisibleBy A ℤ where
  div := fun a n =>
    if hn : n = 0 then 0
    else
      show a ∈ n • (⊤ : AddSubgroup A) by
          rw [H hn] <;> trivial.some
  div_zero := fun a => dif_pos rfl
  div_cancel := fun n a hn => by
    rw [dif_neg hn]
    generalize_proofs h1
    exact h1.some_spec.2

end AddCommGroupₓ

instance (priority := 100) divisibleByIntOfCharZero {𝕜} [DivisionRing 𝕜] [CharZero 𝕜] : DivisibleBy 𝕜 ℤ where
  div := fun q n => q / n
  div_zero := fun q => by
    norm_num
  div_cancel := fun n q hn => by
    rw [zsmul_eq_mul, (Int.cast_commute n _).Eq, div_mul_cancel q (int.cast_ne_zero.mpr hn)]

namespace Groupₓ

variable (A : Type _) [Groupₓ A]

/-- A group is `ℤ`-rootable if it is `ℕ`-rootable.
-/
@[to_additive AddGroupₓ.divisibleByIntOfDivisibleByNat "An additive group is `ℤ`-divisible if it is `ℕ`-divisible."]
def rootableByIntOfRootableByNat [RootableBy A ℕ] : RootableBy A ℤ where
  root := fun a z =>
    match z with
    | (n : ℕ) => RootableBy.root a n
    | -[1+ n] => (RootableBy.root a (n + 1))⁻¹
  root_zero := fun a => RootableBy.root_zero a
  root_cancel := fun n a hn => by
    induction n
    · change RootableBy.root a _ ^ _ = a
      norm_num
      rw [RootableBy.root_cancel]
      rw [Int.of_nat_eq_coe] at hn
      exact_mod_cast hn
      
    · change (RootableBy.root a _)⁻¹ ^ _ = a
      norm_num
      rw [RootableBy.root_cancel]
      norm_num
      

/-- A group is `ℕ`-rootable if it is `ℤ`-rootable
-/
@[to_additive AddGroupₓ.divisibleByNatOfDivisibleByInt "An additive group is `ℕ`-divisible if it `ℤ`-divisible."]
def rootableByNatOfRootableByInt [RootableBy A ℤ] : RootableBy A ℕ where
  root := fun a n => RootableBy.root a (n : ℤ)
  root_zero := fun a => RootableBy.root_zero a
  root_cancel := fun n a hn => by
    have :=
      RootableBy.root_cancel a
        (show (n : ℤ) ≠ 0 by
          exact_mod_cast hn)
    norm_num at this
    exact this

end Groupₓ

section Hom

variable {α A B : Type _}

variable [Zero α] [Monoidₓ A] [Monoidₓ B] [Pow A α] [Pow B α] [RootableBy A α]

variable (f : A → B)

/-- If `f : A → B` is a surjective homomorphism and `A` is `α`-rootable, then `B` is also `α`-rootable.
-/
@[to_additive "If `f : A → B` is a surjective homomorphism and\n`A` is `α`-divisible, then `B` is also `α`-divisible."]
noncomputable def Function.Surjective.rootableBy (hf : Function.Surjective f)
    (hpow : ∀ (a : A) (n : α), f (a ^ n) = f a ^ n) : RootableBy B α :=
  (rootableByOfPowLeftSurj _ _) fun n hn x =>
    let ⟨y, hy⟩ := hf x
    ⟨f <| RootableBy.root y n,
      (by
        rw [← hpow (RootableBy.root y n) n, RootableBy.root_cancel _ hn, hy] : _ ^ _ = x)⟩

end Hom

section Quotientₓ

variable (α : Type _) {A : Type _} [CommGroupₓ A] (B : Subgroup A)

/-- Any quotient group of a rootable group is rootable. -/
@[to_additive QuotientAddGroup.divisibleBy "Any quotient group of a divisible group is divisible"]
noncomputable instance QuotientGroup.rootableBy [RootableBy A ℕ] : RootableBy (A ⧸ B) ℕ :=
  (QuotientGroup.mk_surjective.RootableBy _) fun _ _ => rfl

end Quotientₓ

