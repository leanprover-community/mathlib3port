import Mathbin.Algebra.GroupPower.Basic 
import Mathbin.Logic.Function.Iterate 
import Mathbin.GroupTheory.Perm.Basic

/-!
# Iterates of monoid and ring homomorphisms

Iterate of a monoid/ring homomorphism is a monoid/ring homomorphism but it has a wrong type, so Lean
can't apply lemmas like `monoid_hom.map_one` to `f^[n] 1`. Though it is possible to define
a monoid structure on the endomorphisms, quite often we do not want to convert from
`M →* M` to (not yet defined) `monoid.End M` and from `f^[n]` to `f^n` just to apply a simple lemma.

So, we restate standard `*_hom.map_*` lemmas under names `*_hom.iterate_map_*`.

We also prove formulas for iterates of add/mul left/right.

## Tags

homomorphism, iterate
-/


open Function

variable {M : Type _} {N : Type _} {G : Type _} {H : Type _}

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = (⇑f^[n])`. -/
theorem hom_coe_pow {F : Type _} [Monoidₓ F] (c : F → M → M) (h1 : c 1 = id) (hmul : ∀ f g, c (f*g) = c f ∘ c g)
  (f : F) : ∀ n, c (f ^ n) = c f^[n]
| 0 =>
  by 
    rw [pow_zeroₓ, h1]
    rfl
| n+1 =>
  by 
    rw [pow_succₓ, iterate_succ', hmul, hom_coe_pow]

namespace MonoidHom

section 

variable [MulOneClass M] [MulOneClass N]

@[simp, toAdditive]
theorem iterate_map_one (f : M →* M) (n : ℕ) : (f^[n]) 1 = 1 :=
  iterate_fixed f.map_one n

@[simp, toAdditive]
theorem iterate_map_mul (f : M →* M) (n : ℕ) x y : (f^[n]) (x*y) = (f^[n]) x*(f^[n]) y :=
  semiconj₂.iterate f.map_mul n x y

end 

variable [Monoidₓ M] [Monoidₓ N] [Groupₓ G] [Groupₓ H]

@[simp, toAdditive]
theorem iterate_map_inv (f : G →* G) (n : ℕ) x : (f^[n]) (x⁻¹) = (f^[n]) x⁻¹ :=
  commute.iterate_left f.map_inv n x

theorem iterate_map_pow (f : M →* M) a (n m : ℕ) : (f^[n]) (a ^ m) = (f^[n]) a ^ m :=
  commute.iterate_left (fun x => f.map_pow x m) n a

theorem iterate_map_zpow (f : G →* G) a (n : ℕ) (m : ℤ) : (f^[n]) (a ^ m) = (f^[n]) a ^ m :=
  commute.iterate_left (fun x => f.map_zpow x m) n a

theorem coe_pow {M} [CommMonoidₓ M] (f : Monoidₓ.End M) (n : ℕ) : «expr⇑ » (f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun f g => rfl) _ _

end MonoidHom

namespace AddMonoidHom

variable [AddMonoidₓ M] [AddMonoidₓ N] [AddGroupₓ G] [AddGroupₓ H]

@[simp]
theorem iterate_map_sub (f : G →+ G) (n : ℕ) x y : (f^[n]) (x - y) = (f^[n]) x - (f^[n]) y :=
  semiconj₂.iterate f.map_sub n x y

theorem iterate_map_smul (f : M →+ M) (n m : ℕ) (x : M) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.to_multiplicative.iterate_map_pow x n m

theorem iterate_map_zsmul (f : G →+ G) (n : ℕ) (m : ℤ) (x : G) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.to_multiplicative.iterate_map_zpow x n m

end AddMonoidHom

namespace RingHom

section Semiringₓ

variable {R : Type _} [Semiringₓ R] (f : R →+* R) (n : ℕ) (x y : R)

theorem coe_pow (n : ℕ) : «expr⇑ » (f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun f g => rfl) f n

theorem iterate_map_one : (f^[n]) 1 = 1 :=
  f.to_monoid_hom.iterate_map_one n

theorem iterate_map_zero : (f^[n]) 0 = 0 :=
  f.to_add_monoid_hom.iterate_map_zero n

theorem iterate_map_add : (f^[n]) (x+y) = (f^[n]) x+(f^[n]) y :=
  f.to_add_monoid_hom.iterate_map_add n x y

theorem iterate_map_mul : (f^[n]) (x*y) = (f^[n]) x*(f^[n]) y :=
  f.to_monoid_hom.iterate_map_mul n x y

theorem iterate_map_pow a (n m : ℕ) : (f^[n]) (a ^ m) = (f^[n]) a ^ m :=
  f.to_monoid_hom.iterate_map_pow a n m

theorem iterate_map_smul (n m : ℕ) (x : R) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.to_add_monoid_hom.iterate_map_smul n m x

end Semiringₓ

variable {R : Type _} [Ringₓ R] (f : R →+* R) (n : ℕ) (x y : R)

theorem iterate_map_sub : (f^[n]) (x - y) = (f^[n]) x - (f^[n]) y :=
  f.to_add_monoid_hom.iterate_map_sub n x y

theorem iterate_map_neg : (f^[n]) (-x) = -(f^[n]) x :=
  f.to_add_monoid_hom.iterate_map_neg n x

theorem iterate_map_zsmul (n : ℕ) (m : ℤ) (x : R) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.to_add_monoid_hom.iterate_map_zsmul n m x

end RingHom

theorem Equiv.Perm.coe_pow {α : Type _} (f : Equiv.Perm α) (n : ℕ) : «expr⇑ » (f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

section Monoidₓ

variable [Monoidₓ G] (a : G) (n : ℕ)

@[simp, toAdditive]
theorem mul_left_iterate : (·*·) a^[n] = (·*·) (a ^ n) :=
  Nat.recOn n
      (funext$
        fun x =>
          by 
            simp )$
    fun n ihn =>
      funext$
        fun x =>
          by 
            simp [iterate_succ, ihn, pow_succ'ₓ, mul_assocₓ]

@[simp, toAdditive]
theorem mul_right_iterate : (·*a)^[n] = ·*a ^ n :=
  by 
    induction' n with d hd
    ·
      simpa
    ·
      simp [←pow_succₓ, hd]

@[toAdditive]
theorem mul_right_iterate_apply_one : ((·*a)^[n]) 1 = a ^ n :=
  by 
    simp [mul_right_iterate]

end Monoidₓ

section Semigroupₓ

variable [Semigroupₓ G] {a b c : G}

@[toAdditive]
theorem SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) :
  Function.Semiconj ((·*·) a) ((·*·) b) ((·*·) c) :=
  fun j =>
    by 
      rw [←mul_assocₓ, h.eq, mul_assocₓ]

@[toAdditive]
theorem Commute.function_commute_mul_left (h : Commute a b) : Function.Commute ((·*·) a) ((·*·) b) :=
  SemiconjBy.function_semiconj_mul_left h

@[toAdditive]
theorem SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) : Function.Semiconj (·*a) (·*c) (·*b) :=
  fun j =>
    by 
      simpRw [mul_assocₓ, ←h.eq]

@[toAdditive]
theorem Commute.function_commute_mul_right (h : Commute a b) : Function.Commute (·*a) (·*b) :=
  SemiconjBy.function_semiconj_mul_right_swap h

end Semigroupₓ

