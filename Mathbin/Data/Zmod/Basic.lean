import Mathbin.Algebra.CharP.Basic 
import Mathbin.RingTheory.Ideal.Operations 
import Mathbin.Tactic.FinCases

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `zmod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

* `val_min_abs` returns the integer closest to zero in the equivalence class.

* A coercion `cast` is defined from `zmod n` into any ring.
This is a ring hom if the ring has characteristic dividing `n`

-/


namespace Finₓ

/-!
## Ring structure on `fin n`

We define a commutative ring structure on `fin n`, but we do not register it as instance.
Afterwords, when we define `zmod n` in terms of `fin n`, we use these definitions
to register the ring structure on `zmod n` as type class instance.
-/


open Nat.Modeq Int

/-- Multiplicative commutative semigroup structure on `fin (n+1)`. -/
instance (n : ℕ) : CommSemigroupₓ (Finₓ (n+1)) :=
  { Finₓ.hasMul with
    mul_assoc :=
      fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
        Finₓ.eq_of_veq
          (calc (((a*b) % n+1)*c) ≡ (a*b)*c [MOD n+1] := (Nat.mod_modeq _ _).mul_right _ 
            _ ≡ a*b*c [MOD n+1] :=
            by 
              rw [mul_assocₓ]
            _ ≡ a*(b*c) % n+1 [MOD n+1] := (Nat.mod_modeq _ _).symm.mul_left _
            ),
    mul_comm :=
      fun ⟨a, _⟩ ⟨b, _⟩ =>
        Finₓ.eq_of_veq
          (show ((a*b) % n+1) = (b*a) % n+1by 
            rw [mul_commₓ]) }

private theorem left_distrib_aux (n : ℕ) : ∀ a b c : Finₓ (n+1), (a*b+c) = (a*b)+a*c :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
    Finₓ.eq_of_veq
      (calc (a*(b+c) % n+1) ≡ a*b+c [MOD n+1] := (Nat.mod_modeq _ _).mul_left _ 
        _ ≡ (a*b)+a*c [MOD n+1] :=
        by 
          rw [mul_addₓ]
        _ ≡ ((a*b) % n+1)+(a*c) % n+1 [MOD n+1] := (Nat.mod_modeq _ _).symm.add (Nat.mod_modeq _ _).symm
        )

/-- Commutative ring structure on `fin (n+1)`. -/
instance (n : ℕ) : CommRingₓ (Finₓ (n+1)) :=
  { Finₓ.hasOne, Finₓ.addCommGroup n, Finₓ.commSemigroup n with one_mul := Finₓ.one_mul, mul_one := Finₓ.mul_one,
    left_distrib := left_distrib_aux n,
    right_distrib :=
      fun a b c =>
        by 
          rw [mul_commₓ, left_distrib_aux, mul_commₓ _ b, mul_commₓ] <;> rfl }

end Finₓ

/-- The integers modulo `n : ℕ`. -/
def Zmod : ℕ → Type
| 0 => ℤ
| n+1 => Finₓ (n+1)

namespace Zmod

instance Fintype : ∀ n : ℕ [Fact (0 < n)], Fintype (Zmod n)
| 0, h => False.elim$ Nat.not_lt_zeroₓ 0 h.1
| n+1, _ => Finₓ.fintype (n+1)

@[simp]
theorem card (n : ℕ) [Fact (0 < n)] : Fintype.card (Zmod n) = n :=
  by 
    cases' n
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 0 (Fact.out _)
    ·
      exact Fintype.card_fin (n+1)

instance DecidableEq : ∀ n : ℕ, DecidableEq (Zmod n)
| 0 => Int.decidableEq
| n+1 => Finₓ.decidableEq _

instance HasRepr : ∀ n : ℕ, HasRepr (Zmod n)
| 0 => Int.hasRepr
| n+1 => Finₓ.hasRepr _

instance CommRingₓ : ∀ n : ℕ, CommRingₓ (Zmod n)
| 0 => Int.commRing
| n+1 => Finₓ.commRing n

instance Inhabited (n : ℕ) : Inhabited (Zmod n) :=
  ⟨0⟩

/-- `val a` is a natural number defined as:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

See `zmod.val_min_abs` for a variant that takes values in the integers.
-/
def val : ∀ {n : ℕ}, Zmod n → ℕ
| 0 => Int.natAbs
| n+1 => (coeₓ : Finₓ (n+1) → ℕ)

theorem val_lt {n : ℕ} [Fact (0 < n)] (a : Zmod n) : a.val < n :=
  by 
    cases' n
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 0 (Fact.out _)
    exact Finₓ.is_lt a

theorem val_le {n : ℕ} [Fact (0 < n)] (a : Zmod n) : a.val ≤ n :=
  a.val_lt.le

@[simp]
theorem val_zero : ∀ {n}, (0 : Zmod n).val = 0
| 0 => rfl
| n+1 => rfl

@[simp]
theorem val_one' : (1 : Zmod 0).val = 1 :=
  rfl

@[simp]
theorem val_neg' {n : Zmod 0} : (-n).val = n.val :=
  by 
    simp [val]

@[simp]
theorem val_mul' {m n : Zmod 0} : (m*n).val = m.val*n.val :=
  by 
    simp [val, Int.nat_abs_mul]

theorem val_nat_cast {n : ℕ} (a : ℕ) : (a : Zmod n).val = a % n :=
  by 
    cases' n
    ·
      rw [Nat.mod_zeroₓ, Int.nat_cast_eq_coe_nat]
      exact Int.nat_abs_of_nat a 
    rw [←Finₓ.of_nat_eq_coe]
    rfl

instance (n : ℕ) : CharP (Zmod n) n :=
  { cast_eq_zero_iff :=
      by 
        intro k 
        cases n
        ·
          simp only [Int.nat_cast_eq_coe_nat, zero_dvd_iff, Int.coe_nat_eq_zero]
        rw [Finₓ.eq_iff_veq]
        show (k : Zmod (n+1)).val = (0 : Zmod (n+1)).val ↔ _ 
        rw [val_nat_cast, val_zero, Nat.dvd_iff_mod_eq_zeroₓ] }

@[simp]
theorem nat_cast_self (n : ℕ) : (n : Zmod n) = 0 :=
  CharP.cast_eq_zero (Zmod n) n

@[simp]
theorem nat_cast_self' (n : ℕ) : (n+1 : Zmod (n+1)) = 0 :=
  by 
    rw [←Nat.cast_add_one, nat_cast_self (n+1)]

section UniversalProperty

variable {n : ℕ} {R : Type _}

section 

variable [HasZero R] [HasOne R] [Add R] [Neg R]

/-- Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `zmod.cast_hom` for a bundled version. -/
def cast : ∀ {n : ℕ}, Zmod n → R
| 0 => Int.cast
| n+1 => fun i => i.val

instance (priority := 900) (n : ℕ) : CoeTₓ (Zmod n) R :=
  ⟨cast⟩

@[simp]
theorem cast_zero : ((0 : Zmod n) : R) = 0 :=
  by 
    cases n <;> rfl

variable {S : Type _} [HasZero S] [HasOne S] [Add S] [Neg S]

@[simp]
theorem _root_.prod.fst_zmod_cast (a : Zmod n) : (a : R × S).fst = a :=
  by 
    cases n <;> simp 

@[simp]
theorem _root_.prod.snd_zmod_cast (a : Zmod n) : (a : R × S).snd = a :=
  by 
    cases n <;> simp 

end 

/-- So-named because the coercion is `nat.cast` into `zmod`. For `nat.cast` into an arbitrary ring,
see `zmod.nat_cast_val`. -/
theorem nat_cast_zmod_val {n : ℕ} [Fact (0 < n)] (a : Zmod n) : (a.val : Zmod n) = a :=
  by 
    cases' n
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 0 (Fact.out _)
    ·
      apply Finₓ.coe_coe_eq_self

theorem nat_cast_right_inverse [Fact (0 < n)] : Function.RightInverse val (coeₓ : ℕ → Zmod n) :=
  nat_cast_zmod_val

theorem nat_cast_zmod_surjective [Fact (0 < n)] : Function.Surjective (coeₓ : ℕ → Zmod n) :=
  nat_cast_right_inverse.Surjective

/-- So-named because the outer coercion is `int.cast` into `zmod`. For `int.cast` into an arbitrary
ring, see `zmod.int_cast_cast`. -/
theorem int_cast_zmod_cast (a : Zmod n) : ((a : ℤ) : Zmod n) = a :=
  by 
    cases n
    ·
      rw [Int.cast_id a, Int.cast_id a]
    ·
      rw [coe_coe, Int.nat_cast_eq_coe_nat, Int.cast_coe_nat, Finₓ.coe_coe_eq_self]

theorem int_cast_right_inverse : Function.RightInverse (coeₓ : Zmod n → ℤ) (coeₓ : ℤ → Zmod n) :=
  int_cast_zmod_cast

theorem int_cast_surjective : Function.Surjective (coeₓ : ℤ → Zmod n) :=
  int_cast_right_inverse.Surjective

@[normCast]
theorem cast_id : ∀ n i : Zmod n, «expr↑ » i = i
| 0, i => Int.cast_id i
| n+1, i => nat_cast_zmod_val i

@[simp]
theorem cast_id' : (coeₓ : Zmod n → Zmod n) = id :=
  funext (cast_id n)

variable (R) [Ringₓ R]

/-- The coercions are respectively `nat.cast` and `zmod.cast`. -/
@[simp]
theorem nat_cast_comp_val [Fact (0 < n)] : (coeₓ : ℕ → R) ∘ (val : Zmod n → ℕ) = coeₓ :=
  by 
    cases' n
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 0 (Fact.out _)
    rfl

/-- The coercions are respectively `int.cast`, `zmod.cast`, and `zmod.cast`. -/
@[simp]
theorem int_cast_comp_cast : (coeₓ : ℤ → R) ∘ (coeₓ : Zmod n → ℤ) = coeₓ :=
  by 
    cases n
    ·
      exact congr_argₓ ((· ∘ ·) Int.cast) Zmod.cast_id'
    ·
      ext 
      simp 

variable {R}

@[simp]
theorem nat_cast_val [Fact (0 < n)] (i : Zmod n) : (i.val : R) = i :=
  congr_funₓ (nat_cast_comp_val R) i

@[simp]
theorem int_cast_cast (i : Zmod n) : ((i : ℤ) : R) = i :=
  congr_funₓ (int_cast_comp_cast R) i

theorem coe_add_eq_ite {n : ℕ} (a b : Zmod n) : («expr↑ » (a+b) : ℤ) = if (n : ℤ) ≤ a+b then (a+b) - n else a+b :=
  by 
    cases n
    ·
      simp 
    simp only [coe_coe, Finₓ.coe_add_eq_ite, Int.nat_cast_eq_coe_nat, ←Int.coe_nat_add, ←Int.coe_nat_succ,
      Int.coe_nat_le]
    splitIfs with h
    ·
      exact Int.coe_nat_subₓ h
    ·
      rfl

section CharDvd

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/


variable {n} {m : ℕ} [CharP R m]

@[simp]
theorem cast_one (h : m ∣ n) : ((1 : Zmod n) : R) = 1 :=
  by 
    cases' n
    ·
      exact Int.cast_one 
    show ((1 % n+1 : ℕ) : R) = 1
    cases n
    ·
      rw [Nat.dvd_one] at h 
      subst m 
      apply Subsingleton.elimₓ 
    rw [Nat.mod_eq_of_ltₓ]
    ·
      exact Nat.cast_one 
    exact Nat.lt_of_sub_eq_succₓ rfl

theorem cast_add (h : m ∣ n) (a b : Zmod n) : ((a+b : Zmod n) : R) = a+b :=
  by 
    cases' n
    ·
      apply Int.cast_add 
    simp only [coe_coe]
    symm 
    erw [Finₓ.coe_add, ←Nat.cast_add, ←sub_eq_zero, ←Nat.cast_sub (Nat.mod_leₓ _ _), @CharP.cast_eq_zero_iff R _ _ m]
    exact h.trans (Nat.dvd_sub_mod _)

theorem cast_mul (h : m ∣ n) (a b : Zmod n) : ((a*b : Zmod n) : R) = a*b :=
  by 
    cases' n
    ·
      apply Int.cast_mul 
    simp only [coe_coe]
    symm 
    erw [Finₓ.coe_mul, ←Nat.cast_mul, ←sub_eq_zero, ←Nat.cast_sub (Nat.mod_leₓ _ _), @CharP.cast_eq_zero_iff R _ _ m]
    exact h.trans (Nat.dvd_sub_mod _)

/-- The canonical ring homomorphism from `zmod n` to a ring of characteristic `n`.

See also `zmod.lift` (in `data.zmod.quotient`) for a generalized version working in `add_group`s.
-/
def cast_hom (h : m ∣ n) (R : Type _) [Ringₓ R] [CharP R m] : Zmod n →+* R :=
  { toFun := coeₓ, map_zero' := cast_zero, map_one' := cast_one h, map_add' := cast_add h, map_mul' := cast_mul h }

@[simp]
theorem cast_hom_apply {h : m ∣ n} (i : Zmod n) : cast_hom h R i = i :=
  rfl

@[simp, normCast]
theorem cast_sub (h : m ∣ n) (a b : Zmod n) : ((a - b : Zmod n) : R) = a - b :=
  (cast_hom h R).map_sub a b

@[simp, normCast]
theorem cast_neg (h : m ∣ n) (a : Zmod n) : ((-a : Zmod n) : R) = -a :=
  (cast_hom h R).map_neg a

@[simp, normCast]
theorem cast_pow (h : m ∣ n) (a : Zmod n) (k : ℕ) : ((a ^ k : Zmod n) : R) = a ^ k :=
  (cast_hom h R).map_pow a k

@[simp, normCast]
theorem cast_nat_cast (h : m ∣ n) (k : ℕ) : ((k : Zmod n) : R) = k :=
  (cast_hom h R).map_nat_cast k

@[simp, normCast]
theorem cast_int_cast (h : m ∣ n) (k : ℤ) : ((k : Zmod n) : R) = k :=
  (cast_hom h R).map_int_cast k

end CharDvd

section CharEq

/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/


variable [CharP R n]

@[simp]
theorem cast_one' : ((1 : Zmod n) : R) = 1 :=
  cast_one dvd_rfl

@[simp]
theorem cast_add' (a b : Zmod n) : ((a+b : Zmod n) : R) = a+b :=
  cast_add dvd_rfl a b

@[simp]
theorem cast_mul' (a b : Zmod n) : ((a*b : Zmod n) : R) = a*b :=
  cast_mul dvd_rfl a b

@[simp]
theorem cast_sub' (a b : Zmod n) : ((a - b : Zmod n) : R) = a - b :=
  cast_sub dvd_rfl a b

@[simp]
theorem cast_pow' (a : Zmod n) (k : ℕ) : ((a ^ k : Zmod n) : R) = a ^ k :=
  cast_pow dvd_rfl a k

@[simp, normCast]
theorem cast_nat_cast' (k : ℕ) : ((k : Zmod n) : R) = k :=
  cast_nat_cast dvd_rfl k

@[simp, normCast]
theorem cast_int_cast' (k : ℤ) : ((k : Zmod n) : R) = k :=
  cast_int_cast dvd_rfl k

variable (R)

theorem cast_hom_injective : Function.Injective (Zmod.castHom (dvd_refl n) R) :=
  by 
    rw [RingHom.injective_iff]
    intro x 
    obtain ⟨k, rfl⟩ := Zmod.int_cast_surjective x 
    rw [RingHom.map_int_cast, CharP.int_cast_eq_zero_iff R n, CharP.int_cast_eq_zero_iff (Zmod n) n]
    exact id

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cast_hom_bijective
[fintype R]
(h : «expr = »(fintype.card R, n)) : function.bijective (zmod.cast_hom (dvd_refl n) R) :=
begin
  haveI [] [":", expr fact «expr < »(0, n)] [":=", expr ⟨begin
      rw ["[", expr pos_iff_ne_zero, "]"] [],
      intro [ident hn],
      rw [expr hn] ["at", ident h],
      exact [expr (fintype.card_eq_zero_iff.mp h).elim' 0]
    end⟩],
  rw ["[", expr fintype.bijective_iff_injective_and_card, ",", expr zmod.card, ",", expr h, ",", expr eq_self_iff_true, ",", expr and_true, "]"] [],
  apply [expr zmod.cast_hom_injective]
end

/-- The unique ring isomorphism between `zmod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
noncomputable def RingEquiv [Fintype R] (h : Fintype.card R = n) : Zmod n ≃+* R :=
  RingEquiv.ofBijective _ (Zmod.cast_hom_bijective R h)

end CharEq

end UniversalProperty

theorem int_coe_eq_int_coe_iff (a b : ℤ) (c : ℕ) : (a : Zmod c) = (b : Zmod c) ↔ a ≡ b [ZMOD c] :=
  CharP.int_coe_eq_int_coe_iff (Zmod c) c a b

theorem int_coe_eq_int_coe_iff' (a b : ℤ) (c : ℕ) : (a : Zmod c) = (b : Zmod c) ↔ a % c = b % c :=
  Zmod.int_coe_eq_int_coe_iff a b c

theorem nat_coe_eq_nat_coe_iff (a b c : ℕ) : (a : Zmod c) = (b : Zmod c) ↔ a ≡ b [MOD c] :=
  by 
    convert Zmod.int_coe_eq_int_coe_iff a b c 
    simp [Nat.modeq_iff_dvd, Int.modeq_iff_dvd]

theorem nat_coe_eq_nat_coe_iff' (a b c : ℕ) : (a : Zmod c) = (b : Zmod c) ↔ a % c = b % c :=
  Zmod.nat_coe_eq_nat_coe_iff a b c

theorem int_coe_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : Zmod b) = 0 ↔ (b : ℤ) ∣ a :=
  by 
    change (a : Zmod b) = ((0 : ℤ) : Zmod b) ↔ (b : ℤ) ∣ a 
    rw [Zmod.int_coe_eq_int_coe_iff, Int.modeq_zero_iff_dvd]

theorem nat_coe_zmod_eq_zero_iff_dvd (a b : ℕ) : (a : Zmod b) = 0 ↔ b ∣ a :=
  by 
    change (a : Zmod b) = ((0 : ℕ) : Zmod b) ↔ b ∣ a 
    rw [Zmod.nat_coe_eq_nat_coe_iff, Nat.modeq_zero_iff_dvd]

@[push_cast, simp]
theorem int_cast_mod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : Zmod b) = (a : Zmod b) :=
  by 
    rw [Zmod.int_coe_eq_int_coe_iff]
    apply Int.mod_modeq

theorem ker_int_cast_add_hom (n : ℕ) : (Int.castAddHom (Zmod n)).ker = AddSubgroup.zmultiples n :=
  by 
    ext 
    rw [Int.mem_zmultiples_iff, AddMonoidHom.mem_ker, Int.coe_cast_add_hom, int_coe_zmod_eq_zero_iff_dvd]

theorem ker_int_cast_ring_hom (n : ℕ) : (Int.castRingHom (Zmod n)).ker = Ideal.span ({n} : Set ℤ) :=
  by 
    ext 
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, Int.coe_cast_ring_hom, int_coe_zmod_eq_zero_iff_dvd]

attribute [local semireducible] Int.Nonneg

@[simp]
theorem nat_cast_to_nat (p : ℕ) : ∀ {z : ℤ} h : 0 ≤ z, (z.to_nat : Zmod p) = z
| (n : ℕ), h =>
  by 
    simp only [Int.cast_coe_nat, Int.to_nat_coe_nat]
| -[1+ n], h => False.elim h

theorem val_injective (n : ℕ) [Fact (0 < n)] : Function.Injective (Zmod.val : Zmod n → ℕ) :=
  by 
    cases' n
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 0 (Fact.out _)
    intro a b h 
    ext 
    exact h

theorem val_one_eq_one_mod (n : ℕ) : (1 : Zmod n).val = 1 % n :=
  by 
    rw [←Nat.cast_one, val_nat_cast]

theorem val_one (n : ℕ) [Fact (1 < n)] : (1 : Zmod n).val = 1 :=
  by 
    rw [val_one_eq_one_mod]
    exact Nat.mod_eq_of_ltₓ (Fact.out _)

theorem val_add {n : ℕ} [Fact (0 < n)] (a b : Zmod n) : (a+b).val = (a.val+b.val) % n :=
  by 
    cases' n
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 0 (Fact.out _)
    ·
      apply Finₓ.val_add

theorem val_mul {n : ℕ} (a b : Zmod n) : (a*b).val = (a.val*b.val) % n :=
  by 
    cases n
    ·
      rw [Nat.mod_zeroₓ]
      apply Int.nat_abs_mul
    ·
      apply Finₓ.val_mul

instance Nontrivial (n : ℕ) [Fact (1 < n)] : Nontrivial (Zmod n) :=
  ⟨⟨0, 1,
      fun h =>
        zero_ne_one$
          calc 0 = (0 : Zmod n).val :=
            by 
              rw [val_zero]
            _ = (1 : Zmod n).val := congr_argₓ Zmod.val h 
            _ = 1 := val_one n
            ⟩⟩

/-- The inversion on `zmod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`. -/
def inv : ∀ n : ℕ, Zmod n → Zmod n
| 0, i => Int.sign i
| n+1, i => Nat.gcdA i.val (n+1)

instance (n : ℕ) : HasInv (Zmod n) :=
  ⟨inv n⟩

theorem inv_zero : ∀ n : ℕ, (0 : Zmod n)⁻¹ = 0
| 0 => Int.sign_zero
| n+1 =>
  show (Nat.gcdA _ (n+1) : Zmod (n+1)) = 0 by 
    rw [val_zero]
    unfold Nat.gcdA Nat.xgcd Nat.xgcdAux 
    rfl

theorem mul_inv_eq_gcd {n : ℕ} (a : Zmod n) : (a*a⁻¹) = Nat.gcdₓ a.val n :=
  by 
    cases n
    ·
      calc (a*a⁻¹) = a*Int.sign a := rfl _ = a.nat_abs :=
        by 
          rw [Int.mul_sign, Int.nat_cast_eq_coe_nat]_ = a.val.gcd 0 :=
        by 
          rw [Nat.gcd_zero_rightₓ] <;> rfl
    ·
      set k := n.succ 
      calc (a*a⁻¹) = (a*a⁻¹)+k*Nat.gcdB (val a) k :=
        by 
          rw [nat_cast_self, zero_mul,
            add_zeroₓ]_ = «expr↑ » ((«expr↑ » a.val*Nat.gcdA (val a) k)+k*Nat.gcdB (val a) k) :=
        by 
          pushCast 
          rw [nat_cast_zmod_val]
          rfl _ = Nat.gcdₓ a.val k :=
        (congr_argₓ coeₓ (Nat.gcd_eq_gcd_ab a.val k)).symm

@[simp]
theorem nat_cast_mod (n : ℕ) (a : ℕ) : ((a % n : ℕ) : Zmod n) = a :=
  by 
    conv  => toRHS rw [←Nat.mod_add_divₓ a n] <;> simp 

theorem eq_iff_modeq_nat (n : ℕ) {a b : ℕ} : (a : Zmod n) = b ↔ a ≡ b [MOD n] :=
  by 
    cases n
    ·
      simp only [Nat.Modeq, Int.coe_nat_inj', Nat.mod_zeroₓ, Int.nat_cast_eq_coe_nat]
    ·
      rw [Finₓ.ext_iff, Nat.Modeq, ←val_nat_cast, ←val_nat_cast]
      exact Iff.rfl

theorem coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (x*x⁻¹ : Zmod n) = 1 :=
  by 
    rw [Nat.Coprime, Nat.gcd_commₓ, Nat.gcd_recₓ] at h 
    rw [mul_inv_eq_gcd, val_nat_cast, h, Nat.cast_one]

/-- `unit_of_coprime` makes an element of `units (zmod n)` given
  a natural number `x` and a proof that `x` is coprime to `n`  -/
def unit_of_coprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : Units (Zmod n) :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one x h,
    by 
      rw [mul_commₓ, coe_mul_inv_eq_one x h]⟩

@[simp]
theorem coe_unit_of_coprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (unit_of_coprime x h : Zmod n) = x :=
  rfl

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem val_coe_unit_coprime {n : exprℕ()} (u : units (zmod n)) : nat.coprime (u : zmod n).val n :=
begin
  cases [expr n] [],
  { rcases [expr int.units_eq_one_or u, "with", ident rfl, "|", ident rfl]; simp [] [] [] [] [] [] },
  apply [expr nat.coprime_of_mul_modeq_one ((«expr ⁻¹»(u) : units (zmod «expr + »(n, 1))) : zmod «expr + »(n, 1)).val],
  have [] [] [":=", expr units.ext_iff.1 (mul_right_inv u)],
  rw ["[", expr units.coe_one, "]"] ["at", ident this],
  rw ["[", "<-", expr eq_iff_modeq_nat, ",", expr nat.cast_one, ",", "<-", expr this, "]"] [],
  clear [ident this],
  rw ["[", "<-", expr nat_cast_zmod_val ((«expr * »(u, «expr ⁻¹»(u)) : units (zmod «expr + »(n, 1))) : zmod «expr + »(n, 1)), "]"] [],
  rw ["[", expr units.coe_mul, ",", expr val_mul, ",", expr nat_cast_mod, "]"] []
end

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem inv_coe_unit
{n : exprℕ()}
(u : units (zmod n)) : «expr = »(«expr ⁻¹»((u : zmod n)), («expr ⁻¹»(u) : units (zmod n))) :=
begin
  have [] [] [":=", expr congr_arg (coe : exprℕ() → zmod n) (val_coe_unit_coprime u)],
  rw ["[", "<-", expr mul_inv_eq_gcd, ",", expr nat.cast_one, "]"] ["at", ident this],
  let [ident u'] [":", expr units (zmod n)] [":=", expr ⟨u, «expr ⁻¹»((u : zmod n)), this, by rwa [expr mul_comm] []⟩],
  have [ident h] [":", expr «expr = »(u, u')] [],
  { apply [expr units.ext],
    refl },
  rw [expr h] [],
  refl
end

theorem mul_inv_of_unit {n : ℕ} (a : Zmod n) (h : IsUnit a) : (a*a⁻¹) = 1 :=
  by 
    rcases h with ⟨u, rfl⟩
    rw [inv_coe_unit, u.mul_inv]

theorem inv_mul_of_unit {n : ℕ} (a : Zmod n) (h : IsUnit a) : (a⁻¹*a) = 1 :=
  by 
    rw [mul_commₓ, mul_inv_of_unit a h]

/-- Equivalence between the units of `zmod n` and
the subtype of terms `x : zmod n` for which `x.val` is comprime to `n` -/
def units_equiv_coprime {n : ℕ} [Fact (0 < n)] : Units (Zmod n) ≃ { x : Zmod n // Nat.Coprime x.val n } :=
  { toFun := fun x => ⟨x, val_coe_unit_coprime x⟩, invFun := fun x => unit_of_coprime x.1.val x.2,
    left_inv := fun ⟨_, _, _, _⟩ => Units.ext (nat_cast_zmod_val _),
    right_inv :=
      fun ⟨_, _⟩ =>
        by 
          simp  }

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The **Chinese remainder theorem**. For a pair of coprime natural numbers, `m` and `n`,
  the rings `zmod (m * n)` and `zmod m × zmod n` are isomorphic.

See `ideal.quotient_inf_ring_equiv_pi_quotient` for the Chinese remainder theorem for ideals in any
ring.
-/
def chinese_remainder
{m n : exprℕ()}
(h : m.coprime n) : «expr ≃+* »(zmod «expr * »(m, n), «expr × »(zmod m, zmod n)) :=
let to_fun : zmod «expr * »(m, n) → «expr × »(zmod m, zmod n) := zmod.cast_hom (show «expr ∣ »(m.lcm n, «expr * »(m, n)), by simp [] [] [] ["[", expr nat.lcm_dvd_iff, "]"] [] []) «expr × »(zmod m, zmod n) in
let inv_fun : «expr × »(zmod m, zmod n) → zmod «expr * »(m, n) := λ
    x, if «expr = »(«expr * »(m, n), 0) then if «expr = »(m, 1) then ring_hom.snd _ _ x else ring_hom.fst _ _ x else nat.chinese_remainder h x.1.val x.2.val in
have inv : «expr ∧ »(function.left_inverse inv_fun to_fun, function.right_inverse inv_fun to_fun) := if hmn0 : «expr = »(«expr * »(m, n), 0) then begin
  rcases [expr h.eq_of_mul_eq_zero hmn0, "with", "⟨", ident rfl, ",", ident rfl, "⟩", "|", "⟨", ident rfl, ",", ident rfl, "⟩"]; simp [] [] [] ["[", expr inv_fun, ",", expr to_fun, ",", expr function.left_inverse, ",", expr function.right_inverse, ",", expr ring_hom.eq_int_cast, ",", expr prod.ext_iff, "]"] [] []
end else begin
  haveI [] [":", expr fact «expr < »(0, «expr * »(m, n))] [":=", expr ⟨nat.pos_of_ne_zero hmn0⟩],
  haveI [] [":", expr fact «expr < »(0, m)] [":=", expr ⟨«expr $ »(nat.pos_of_ne_zero, left_ne_zero_of_mul hmn0)⟩],
  haveI [] [":", expr fact «expr < »(0, n)] [":=", expr ⟨«expr $ »(nat.pos_of_ne_zero, right_ne_zero_of_mul hmn0)⟩],
  have [ident left_inv] [":", expr function.left_inverse inv_fun to_fun] [],
  { intro [ident x],
    dsimp ["only"] ["[", expr dvd_mul_left, ",", expr dvd_mul_right, ",", expr zmod.cast_hom_apply, ",", expr coe_coe, ",", expr inv_fun, ",", expr to_fun, "]"] [] [],
    conv_rhs [] [] { rw ["<-", expr zmod.nat_cast_zmod_val x] },
    rw ["[", expr if_neg hmn0, ",", expr zmod.eq_iff_modeq_nat, ",", "<-", expr nat.modeq_and_modeq_iff_modeq_mul h, ",", expr prod.fst_zmod_cast, ",", expr prod.snd_zmod_cast, "]"] [],
    refine [expr ⟨(nat.chinese_remainder h (x : zmod m).val (x : zmod n).val).2.left.trans _, (nat.chinese_remainder h (x : zmod m).val (x : zmod n).val).2.right.trans _⟩],
    { rw ["[", "<-", expr zmod.eq_iff_modeq_nat, ",", expr zmod.nat_cast_zmod_val, ",", expr zmod.nat_cast_val, "]"] [] },
    { rw ["[", "<-", expr zmod.eq_iff_modeq_nat, ",", expr zmod.nat_cast_zmod_val, ",", expr zmod.nat_cast_val, "]"] [] } },
  exact [expr ⟨left_inv, fintype.right_inverse_of_left_inverse_of_card_le left_inv (by simp [] [] [] [] [] [])⟩]
end,
{ to_fun := to_fun,
  inv_fun := inv_fun,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _,
  left_inv := inv.1,
  right_inv := inv.2 }

instance subsingleton_units : Subsingleton (Units (Zmod 2)) :=
  ⟨fun x y =>
      by 
        ext1 
        cases' x with x xi hx1 hx2 
        cases' y with y yi hy1 hy2 
        revert hx1 hx2 hy1 hy2 
        finCases x <;> finCases y <;> simp ⟩

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_div_two_iff_lt_neg
(n : exprℕ())
[hn : fact «expr = »(«expr % »((n : exprℕ()), 2), 1)]
{x : zmod n}
(hx0 : «expr ≠ »(x, 0)) : «expr ↔ »(«expr ≤ »(x.val, («expr / »(n, 2) : exprℕ())), «expr < »((«expr / »(n, 2) : exprℕ()), «expr- »(x).val)) :=
begin
  haveI [ident npos] [":", expr fact «expr < »(0, n)] [":=", expr ⟨by { apply [expr (nat.eq_zero_or_pos n).resolve_left],
      unfreezingI { rintro [ident rfl] },
      simpa [] [] [] ["[", expr fact_iff, "]"] [] ["using", expr hn] }⟩],
  have [ident hn2] [":", expr «expr < »(«expr / »((n : exprℕ()), 2), n)] [":=", expr nat.div_lt_of_lt_mul ((lt_mul_iff_one_lt_left npos.1).2 exprdec_trivial())],
  have [ident hn2'] [":", expr «expr = »(«expr - »((n : exprℕ()), «expr / »(n, 2)), «expr + »(«expr / »(n, 2), 1))] [],
  { conv [] [] { to_lhs,
      congr,
      rw ["[", "<-", expr nat.succ_sub_one n, ",", expr nat.succ_sub npos.1, "]"] },
    rw ["[", "<-", expr nat.two_mul_odd_div_two hn.1, ",", expr two_mul, ",", "<-", expr nat.succ_add, ",", expr add_tsub_cancel_right, "]"] [] },
  have [ident hxn] [":", expr «expr < »(«expr - »((n : exprℕ()), x.val), n)] [],
  { rw ["[", expr tsub_lt_iff_tsub_lt x.val_le le_rfl, ",", expr tsub_self, "]"] [],
    rw ["<-", expr zmod.nat_cast_zmod_val x] ["at", ident hx0],
    exact [expr nat.pos_of_ne_zero (λ h, by simpa [] [] [] ["[", expr h, "]"] [] ["using", expr hx0])] },
  by conv [] [] { to_rhs,
    rw ["[", "<-", expr nat.succ_le_iff, ",", expr nat.succ_eq_add_one, ",", "<-", expr hn2', ",", "<-", expr zero_add «expr- »(x), ",", "<-", expr zmod.nat_cast_self, ",", "<-", expr sub_eq_add_neg, ",", "<-", expr zmod.nat_cast_zmod_val x, ",", "<-", expr nat.cast_sub x.val_le, ",", expr zmod.val_nat_cast, ",", expr nat.mod_eq_of_lt hxn, ",", expr tsub_le_tsub_iff_left x.val_le, "]"] }
end

theorem ne_neg_self (n : ℕ) [hn : Fact ((n : ℕ) % 2 = 1)] {a : Zmod n} (ha : a ≠ 0) : a ≠ -a :=
  fun h =>
    have  : a.val ≤ n / 2 ↔ (n : ℕ) / 2 < (-a).val := le_div_two_iff_lt_neg n ha 
    by 
      rwa [←h, ←not_ltₓ, not_iff_selfₓ] at this

theorem neg_one_ne_one {n : ℕ} [Fact (2 < n)] : (-1 : Zmod n) ≠ 1 :=
  CharP.neg_one_ne_one (Zmod n) n

@[simp]
theorem neg_eq_self_mod_two (a : Zmod 2) : -a = a :=
  by 
    finCases a <;> ext <;> simp [Finₓ.coe_neg, Int.natModₓ] <;> normNum

@[simp]
theorem nat_abs_mod_two (a : ℤ) : (a.nat_abs : Zmod 2) = a :=
  by 
    cases a
    ·
      simp only [Int.nat_abs_of_nat, Int.cast_coe_nat, Int.of_nat_eq_coe]
    ·
      simp only [neg_eq_self_mod_two, Nat.cast_succ, Int.natAbs, Int.cast_neg_succ_of_nat]

@[simp]
theorem val_eq_zero : ∀ {n : ℕ} a : Zmod n, a.val = 0 ↔ a = 0
| 0, a => Int.nat_abs_eq_zero
| n+1, a =>
  by 
    rw [Finₓ.ext_iff]
    exact Iff.rfl

theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : (a : Zmod n).val = a :=
  by 
    rw [val_nat_cast, Nat.mod_eq_of_ltₓ h]

theorem neg_val' {n : ℕ} [Fact (0 < n)] (a : Zmod n) : (-a).val = (n - a.val) % n :=
  calc (-a).val = val (-a) % n :=
    by 
      rw [Nat.mod_eq_of_ltₓ (-a).val_lt]
    _ = (n - val a) % n :=
    Nat.Modeq.add_right_cancel' _
      (by 
        rw [Nat.Modeq, ←val_add, add_left_negₓ, tsub_add_cancel_of_le a.val_le, Nat.mod_selfₓ, val_zero])
    

theorem neg_val {n : ℕ} [Fact (0 < n)] (a : Zmod n) : (-a).val = if a = 0 then 0 else n - a.val :=
  by 
    rw [neg_val']
    byCases' h : a = 0
    ·
      rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_selfₓ]
    rw [if_neg h]
    apply Nat.mod_eq_of_ltₓ 
    apply Nat.sub_ltₓ (Fact.out (0 < n))
    contrapose! h 
    rwa [Nat.le_zero_iff, val_eq_zero] at h

/-- `val_min_abs x` returns the integer in the same equivalence class as `x` that is closest to `0`,
  The result will be in the interval `(-n/2, n/2]`. -/
def val_min_abs : ∀ {n : ℕ}, Zmod n → ℤ
| 0, x => x
| n@(_+1), x => if x.val ≤ n / 2 then x.val else (x.val : ℤ) - n

@[simp]
theorem val_min_abs_def_zero (x : Zmod 0) : val_min_abs x = x :=
  rfl

theorem val_min_abs_def_pos {n : ℕ} [Fact (0 < n)] (x : Zmod n) :
  val_min_abs x = if x.val ≤ n / 2 then x.val else x.val - n :=
  by 
    cases' n
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 0 (Fact.out (0 < 0))
    ·
      rfl

@[simp]
theorem coe_val_min_abs : ∀ {n : ℕ} x : Zmod n, (x.val_min_abs : Zmod n) = x
| 0, x => Int.cast_id x
| k@(n+1), x =>
  by 
    rw [val_min_abs_def_pos]
    splitIfs
    ·
      rw [Int.cast_coe_nat, nat_cast_zmod_val]
    ·
      rw [Int.cast_sub, Int.cast_coe_nat, nat_cast_zmod_val, Int.cast_coe_nat, nat_cast_self, sub_zero]

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat_abs_val_min_abs_le
{n : exprℕ()}
[fact «expr < »(0, n)]
(x : zmod n) : «expr ≤ »(x.val_min_abs.nat_abs, «expr / »(n, 2)) :=
begin
  rw [expr zmod.val_min_abs_def_pos] [],
  split_ifs [] ["with", ident h],
  { exact [expr h] },
  have [] [":", expr «expr ≤ »((«expr - »(x.val, n) : exprℤ()), 0)] [],
  { rw ["[", expr sub_nonpos, ",", expr int.coe_nat_le, "]"] [],
    exact [expr x.val_le] },
  rw ["[", "<-", expr int.coe_nat_le, ",", expr int.of_nat_nat_abs_of_nonpos this, ",", expr neg_sub, "]"] [],
  conv_lhs [] [] { congr,
    rw ["[", "<-", expr nat.mod_add_div n 2, ",", expr int.coe_nat_add, ",", expr int.coe_nat_mul, ",", expr int.coe_nat_bit0, ",", expr int.coe_nat_one, "]"] },
  suffices [] [":", expr «expr ≤ »((«expr + »((«expr % »(n, 2) : exprℕ()), «expr / »(n, 2)) : exprℤ()), val x)],
  { rw ["<-", expr sub_nonneg] ["at", ident this, "⊢"],
    apply [expr le_trans this (le_of_eq _)],
    ring_nf [] [] [],
    ring [] },
  norm_cast [],
  calc
    «expr ≤ »(«expr + »(«expr % »((n : exprℕ()), 2), «expr / »(n, 2)), «expr + »(1, «expr / »(n, 2))) : nat.add_le_add_right (nat.le_of_lt_succ (nat.mod_lt _ exprdec_trivial())) _
    «expr ≤ »(..., x.val) : by { rw [expr add_comm] [],
      exact [expr nat.succ_le_of_lt (lt_of_not_ge h)] }
end

@[simp]
theorem val_min_abs_zero : ∀ n, (0 : Zmod n).valMinAbs = 0
| 0 =>
  by 
    simp only [val_min_abs_def_zero]
| n+1 =>
  by 
    simp only [val_min_abs_def_pos, if_true, Int.coe_nat_zero, zero_le, val_zero]

@[simp]
theorem val_min_abs_eq_zero {n : ℕ} (x : Zmod n) : x.val_min_abs = 0 ↔ x = 0 :=
  by 
    cases n
    ·
      simp 
    split 
    ·
      simp only [val_min_abs_def_pos, Int.coe_nat_succ]
      splitIfs with h h <;> intro h0
      ·
        apply val_injective 
        rwa [Int.coe_nat_eq_zero] at h0
      ·
        apply absurd h0 
        rw [sub_eq_zero]
        apply ne_of_ltₓ 
        exactModCast x.val_lt
    ·
      rintro rfl 
      rw [val_min_abs_zero]

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat_cast_nat_abs_val_min_abs
{n : exprℕ()}
[fact «expr < »(0, n)]
(a : zmod n) : «expr = »((a.val_min_abs.nat_abs : zmod n), if «expr ≤ »(a.val, «expr / »((n : exprℕ()), 2)) then a else «expr- »(a)) :=
begin
  have [] [":", expr «expr ≤ »(«expr - »((a.val : exprℤ()), n), 0)] [],
  by { erw ["[", expr sub_nonpos, ",", expr int.coe_nat_le, "]"] [],
    exact [expr a.val_le] },
  rw ["[", expr zmod.val_min_abs_def_pos, "]"] [],
  split_ifs [] [],
  { rw ["[", expr int.nat_abs_of_nat, ",", expr nat_cast_zmod_val, "]"] [] },
  { rw ["[", "<-", expr int.cast_coe_nat, ",", expr int.of_nat_nat_abs_of_nonpos this, ",", expr int.cast_neg, ",", expr int.cast_sub, "]"] [],
    rw ["[", expr int.cast_coe_nat, ",", expr int.cast_coe_nat, ",", expr nat_cast_self, ",", expr sub_zero, ",", expr nat_cast_zmod_val, "]"] [] }
end

@[simp]
theorem nat_abs_val_min_abs_neg {n : ℕ} (a : Zmod n) : (-a).valMinAbs.natAbs = a.val_min_abs.nat_abs :=
  by 
    cases n
    ·
      simp only [Int.nat_abs_neg, val_min_abs_def_zero]
    byCases' ha0 : a = 0
    ·
      rw [ha0, neg_zero]
    byCases' haa : -a = a
    ·
      rw [haa]
    suffices hpa : (n+1 : ℕ) - a.val ≤ (n+1) / 2 ↔ (n+1 : ℕ) / 2 < a.val
    ·
      rw [val_min_abs_def_pos, val_min_abs_def_pos]
      rw [←not_leₓ] at hpa 
      simp only [if_neg ha0, neg_val, hpa, Int.coe_nat_subₓ a.val_le]
      splitIfs 
      all_goals 
        rw [←Int.nat_abs_neg]
        congr 1
        ring 
    suffices  : (((n+1 : ℕ) % 2)+2*(n+1) / 2) - a.val ≤ (n+1) / 2 ↔ (n+1 : ℕ) / 2 < a.val
    ·
      rwa [Nat.mod_add_divₓ] at this 
    suffices  : (((n+1) % 2)+(n+1) / 2) ≤ val a ↔ (n+1) / 2 < val a
    ·
      rw [tsub_le_iff_tsub_le, two_mul, ←add_assocₓ, add_tsub_cancel_right, this]
    cases' (n+1 : ℕ).mod_two_eq_zero_or_one with hn0 hn1
    ·
      split 
      ·
        intro h 
        apply lt_of_le_of_neₓ (le_transₓ (Nat.le_add_leftₓ _ _) h)
        contrapose! haa 
        rw [←Zmod.nat_cast_zmod_val a, ←haa, neg_eq_iff_add_eq_zero, ←Nat.cast_add]
        rw [CharP.cast_eq_zero_iff (Zmod (n+1)) (n+1)]
        rw [←two_mul, ←zero_addₓ (2*_), ←hn0, Nat.mod_add_divₓ]
      ·
        rw [hn0, zero_addₓ]
        exact le_of_ltₓ
    ·
      rw [hn1, add_commₓ, Nat.succ_le_iff]

theorem val_eq_ite_val_min_abs {n : ℕ} [Fact (0 < n)] (a : Zmod n) :
  (a.val : ℤ) = a.val_min_abs+if a.val ≤ n / 2 then 0 else n :=
  by 
    rw [Zmod.val_min_abs_def_pos]
    splitIfs <;> simp only [add_zeroₓ, sub_add_cancel]

theorem prime_ne_zero (p q : ℕ) [hp : Fact p.prime] [hq : Fact q.prime] (hpq : p ≠ q) : (q : Zmod p) ≠ 0 :=
  by 
    rwa [←Nat.cast_zero, Ne.def, eq_iff_modeq_nat, Nat.modeq_zero_iff_dvd, ←hp.1.coprime_iff_not_dvd,
      Nat.coprime_primes hp.1 hq.1]

end Zmod

namespace Zmod

variable (p : ℕ) [Fact p.prime]

private theorem mul_inv_cancel_aux (a : Zmod p) (h : a ≠ 0) : (a*a⁻¹) = 1 :=
  by 
    obtain ⟨k, rfl⟩ := nat_cast_zmod_surjective a 
    apply coe_mul_inv_eq_one 
    apply Nat.Coprime.symm 
    rwa [Nat.Prime.coprime_iff_not_dvd (Fact.out p.prime), ←CharP.cast_eq_zero_iff (Zmod p)]

/-- Field structure on `zmod p` if `p` is prime. -/
instance : Field (Zmod p) :=
  { Zmod.commRing p, Zmod.hasInv p, Zmod.nontrivial p with mul_inv_cancel := mul_inv_cancel_aux p,
    inv_zero := inv_zero p }

/-- `zmod p` is an integral domain when `p` is prime. -/
instance (p : ℕ) [hp : Fact p.prime] : IsDomain (Zmod p) :=
  by 
    (
      cases p
      ·
        exfalso 
        rcases hp with ⟨⟨⟨⟩⟩⟩)
    exact @Field.is_domain (Zmod _) (Zmod.field _)

end Zmod

theorem RingHom.ext_zmod {n : ℕ} {R : Type _} [Semiringₓ R] (f g : Zmod n →+* R) : f = g :=
  by 
    ext a 
    obtain ⟨k, rfl⟩ := Zmod.int_cast_surjective a 
    let φ : ℤ →+* R := f.comp (Int.castRingHom (Zmod n))
    let ψ : ℤ →+* R := g.comp (Int.castRingHom (Zmod n))
    show φ k = ψ k 
    rw [φ.ext_int ψ]

namespace Zmod

variable {n : ℕ} {R : Type _}

instance subsingleton_ring_hom [Semiringₓ R] : Subsingleton (Zmod n →+* R) :=
  ⟨RingHom.ext_zmod⟩

instance subsingleton_ring_equiv [Semiringₓ R] : Subsingleton (Zmod n ≃+* R) :=
  ⟨fun f g =>
      by 
        rw [RingEquiv.coe_ring_hom_inj_iff]
        apply RingHom.ext_zmod _ _⟩

@[simp]
theorem ring_hom_map_cast [Ringₓ R] (f : R →+* Zmod n) (k : Zmod n) : f k = k :=
  by 
    cases n <;> simp 

theorem ring_hom_right_inverse [Ringₓ R] (f : R →+* Zmod n) : Function.RightInverse (coeₓ : Zmod n → R) f :=
  ring_hom_map_cast f

theorem RingHomSurjective [Ringₓ R] (f : R →+* Zmod n) : Function.Surjective f :=
  (ring_hom_right_inverse f).Surjective

-- error in Data.Zmod.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring_hom_eq_of_ker_eq
[comm_ring R]
(f g : «expr →+* »(R, zmod n))
(h : «expr = »(f.ker, g.ker)) : «expr = »(f, g) :=
begin
  have [] [] [":=", expr f.lift_of_right_inverse_comp _ (zmod.ring_hom_right_inverse f) ⟨g, le_of_eq h⟩],
  rw [expr subtype.coe_mk] ["at", ident this],
  rw ["[", "<-", expr this, ",", expr ring_hom.ext_zmod (f.lift_of_right_inverse _ _ _) (ring_hom.id _), ",", expr ring_hom.id_comp, "]"] []
end

section lift

variable (n) {A : Type _} [AddGroupₓ A]

/-- The map from `zmod n` induced by `f : ℤ →+ A` that maps `n` to `0`. -/
@[simps]
def lift : { f : ℤ →+ A // f n = 0 } ≃ (Zmod n →+ A) :=
  (Equiv.subtypeEquivRight$
        by 
          intro f 
          rw [ker_int_cast_add_hom]
          split 
          ·
            rintro hf _ ⟨x, rfl⟩
            simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
          ·
            intro h 
            refine' h (AddSubgroup.mem_zmultiples _)).trans$
    (Int.castAddHom (Zmod n)).liftOfRightInverse coeₓ int_cast_zmod_cast

variable (f : { f : ℤ →+ A // f n = 0 })

@[simp]
theorem lift_coe (x : ℤ) : lift n f (x : Zmod n) = f x :=
  AddMonoidHom.lift_of_right_inverse_comp_apply _ _ _ _ _

theorem lift_cast_add_hom (x : ℤ) : lift n f (Int.castAddHom (Zmod n) x) = f x :=
  AddMonoidHom.lift_of_right_inverse_comp_apply _ _ _ _ _

@[simp]
theorem lift_comp_coe : Zmod.lift n f ∘ coeₓ = f :=
  funext$ lift_coe _ _

@[simp]
theorem lift_comp_cast_add_hom : (Zmod.lift n f).comp (Int.castAddHom (Zmod n)) = f :=
  AddMonoidHom.ext$ lift_cast_add_hom _ _

end lift

end Zmod

