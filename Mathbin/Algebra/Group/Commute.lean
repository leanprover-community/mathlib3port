import Mathbin.Algebra.Group.Semiconj

/-!
# Commuting pairs of elements in monoids

We define the predicate `commute a b := a * b = b * a` and provide some operations on terms `(h :
commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that `hb : commute a b` and
`hc : commute a c`.  Then `hb.pow_left 5` proves `commute (a ^ 5) b` and `(hb.pow_right 2).add_right
(hb.mul_right hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `semiconj_by`.
-/


/-- Two elements commute if `a * b = b * a`. -/
@[toAdditive AddCommute "Two elements additively commute if `a + b = b + a`"]
def Commute {S : Type _} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b

namespace Commute

section Mul

variable{S : Type _}[Mul S]

/-- Equality behind `commute a b`; useful for rewriting. -/
@[toAdditive]
protected theorem Eq {a b : S} (h : Commute a b) : (a*b) = b*a :=
  h

/-- Any element commutes with itself. -/
@[refl, simp, toAdditive]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a*a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, toAdditive]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h

@[toAdditive]
protected theorem SemiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h

@[toAdditive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩

end Mul

section Semigroupₓ

variable{S : Type _}[Semigroupₓ S]{a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, toAdditive]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b*c) :=
  hab.mul_right hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, toAdditive]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a*b) c :=
  hac.mul_left hbc

@[toAdditive]
protected theorem right_comm (h : Commute b c) (a : S) : ((a*b)*c) = (a*c)*b :=
  by 
    simp only [mul_assocₓ, h.eq]

@[toAdditive]
protected theorem left_comm (h : Commute a b) c : (a*b*c) = b*a*c :=
  by 
    simp only [←mul_assocₓ, h.eq]

end Semigroupₓ

@[toAdditive]
protected theorem all {S : Type _} [CommSemigroupₓ S] (a b : S) : Commute a b :=
  mul_commₓ a b

section MulOneClass

variable{M : Type _}[MulOneClass M]

@[simp, toAdditive]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a

@[simp, toAdditive]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a

end MulOneClass

section Monoidₓ

variable{M : Type _}[Monoidₓ M]{a b : M}{u u₁ u₂ : Units M}

@[simp, toAdditive]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  h.pow_right n

@[simp, toAdditive]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm

@[simp, toAdditive]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n

@[simp, toAdditive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n

@[simp, toAdditive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n

@[simp, toAdditive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n

@[toAdditive succ_nsmul']
theorem _root_.pow_succ' (a : M) (n : ℕ) : (a ^ n+1) = (a ^ n)*a :=
  (pow_succₓ a n).trans (self_pow _ _)

@[toAdditive]
theorem units_inv_right : Commute a u → Commute a («expr↑ » (u⁻¹)) :=
  SemiconjBy.units_inv_right

@[simp, toAdditive]
theorem units_inv_right_iff : Commute a («expr↑ » (u⁻¹)) ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff

@[toAdditive]
theorem units_inv_left : Commute («expr↑ » u) a → Commute («expr↑ » (u⁻¹)) a :=
  SemiconjBy.units_inv_symm_left

@[simp, toAdditive]
theorem units_inv_left_iff : Commute («expr↑ » (u⁻¹)) a ↔ Commute («expr↑ » u) a :=
  SemiconjBy.units_inv_symm_left_iff

@[toAdditive]
theorem units_coe : Commute u₁ u₂ → Commute (u₁ : M) u₂ :=
  SemiconjBy.units_coe

@[toAdditive]
theorem units_of_coe : Commute (u₁ : M) u₂ → Commute u₁ u₂ :=
  SemiconjBy.units_of_coe

@[simp, toAdditive]
theorem units_coe_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_coe_iff

@[toAdditive]
theorem is_unit_mul_iff (h : Commute a b) : IsUnit (a*b) ↔ IsUnit a ∧ IsUnit b :=
  by 
    refine' ⟨_, fun H => H.1.mul H.2⟩
    rintro ⟨u, hu⟩
    have  : ((b*«expr↑ » (u⁻¹))*a) = 1
    ·
      have  : Commute a u := hu.symm ▸ (Commute.refl _).mul_right h 
      rw [←this.units_inv_right.right_comm, ←h.eq, ←hu, u.mul_inv]
    split 
    ·
      refine' ⟨⟨a, b*«expr↑ » (u⁻¹), _, this⟩, rfl⟩
      rw [←mul_assocₓ, ←hu, u.mul_inv]
    ·
      rw [mul_assocₓ] at this 
      refine' ⟨⟨b, «expr↑ » (u⁻¹)*a, this, _⟩, rfl⟩
      rw [mul_assocₓ, ←hu, u.inv_mul]

@[simp, toAdditive]
theorem _root_.is_unit_mul_self_iff : IsUnit (a*a) ↔ IsUnit a :=
  (Commute.refl a).is_unit_mul_iff.trans (and_selfₓ _)

end Monoidₓ

section Groupₓ

variable{G : Type _}[Groupₓ G]{a b : G}

@[toAdditive]
theorem inv_right : Commute a b → Commute a (b⁻¹) :=
  SemiconjBy.inv_right

@[simp, toAdditive]
theorem inv_right_iff : Commute a (b⁻¹) ↔ Commute a b :=
  SemiconjBy.inv_right_iff

@[toAdditive]
theorem inv_left : Commute a b → Commute (a⁻¹) b :=
  SemiconjBy.inv_symm_left

@[simp, toAdditive]
theorem inv_left_iff : Commute (a⁻¹) b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff

@[toAdditive]
theorem inv_invₓ : Commute a b → Commute (a⁻¹) (b⁻¹) :=
  SemiconjBy.inv_inv_symm

@[simp, toAdditive]
theorem inv_inv_iff : Commute (a⁻¹) (b⁻¹) ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff

@[toAdditive]
protected theorem inv_mul_cancel (h : Commute a b) : ((a⁻¹*b)*a) = b :=
  by 
    rw [h.inv_left.eq, inv_mul_cancel_right]

@[toAdditive]
theorem inv_mul_cancel_assoc (h : Commute a b) : (a⁻¹*b*a) = b :=
  by 
    rw [←mul_assocₓ, h.inv_mul_cancel]

@[toAdditive]
protected theorem mul_inv_cancel (h : Commute a b) : ((a*b)*a⁻¹) = b :=
  by 
    rw [h.eq, mul_inv_cancel_rightₓ]

@[toAdditive]
theorem mul_inv_cancel_assoc (h : Commute a b) : (a*b*a⁻¹) = b :=
  by 
    rw [←mul_assocₓ, h.mul_inv_cancel]

end Groupₓ

end Commute

section CommGroupₓ

variable{G : Type _}[CommGroupₓ G](a b : G)

@[simp, toAdditive]
theorem mul_inv_cancel_comm : ((a*b)*a⁻¹) = b :=
  (Commute.all a b).mul_inv_cancel

@[simp, toAdditive]
theorem mul_inv_cancel_comm_assoc : (a*b*a⁻¹) = b :=
  (Commute.all a b).mul_inv_cancel_assoc

@[simp, toAdditive]
theorem inv_mul_cancel_comm : ((a⁻¹*b)*a) = b :=
  (Commute.all a b).inv_mul_cancel

@[simp, toAdditive]
theorem inv_mul_cancel_comm_assoc : (a⁻¹*b*a) = b :=
  (Commute.all a b).inv_mul_cancel_assoc

end CommGroupₓ

