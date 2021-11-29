import Mathbin.Data.Int.Modeq 
import Mathbin.NumberTheory.Padics.PadicNumbers 
import Mathbin.RingTheory.DiscreteValuationRing 
import Mathbin.Topology.MetricSpace.CauSeqFilter

/-!
# p-adic integers

This file defines the p-adic integers `ℤ_p` as the subtype of `ℚ_p` with norm `≤ 1`.
We show that `ℤ_p`
* is complete
* is nonarchimedean
* is a normed ring
* is a local ring
* is a discrete valuation ring

The relation between `ℤ_[p]` and `zmod p` is established in another file.

## Important definitions

* `padic_int` : the type of p-adic numbers

## Notation

We introduce the notation `ℤ_[p]` for the p-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (nat.prime p)] as a type class argument.

Coercions into `ℤ_p` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/


open Padic Metric LocalRing

noncomputable theory

open_locale Classical

/-- The p-adic integers ℤ_p are the p-adic numbers with norm ≤ 1. -/
def PadicInt (p : ℕ) [Fact p.prime] :=
  { x : ℚ_[p] // ∥x∥ ≤ 1 }

notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt

/-! ### Ring structure and coercion to `ℚ_[p]` -/


variable {p : ℕ} [Fact p.prime]

instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩

theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext_iff_val.2

/-- Addition on ℤ_p is inherited from ℚ_p. -/
instance : Add ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x+y, le_transₓ (padicNormE.nonarchimedean _ _) (max_le_iff.2 ⟨hx, hy⟩)⟩⟩

/-- Multiplication on ℤ_p is inherited from ℚ_p. -/
instance : Mul ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨x*y,
        by 
          rw [padicNormE.mul]
          apply mul_le_one <;>
            ·
              first |
                assumption|
                apply norm_nonneg⟩⟩

/-- Negation on ℤ_p is inherited from ℚ_p. -/
instance : Neg ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ =>
      ⟨-x,
        by 
          simpa⟩⟩

/-- Subtraction on ℤ_p is inherited from ℚ_p. -/
instance : Sub ℤ_[p] :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨x - y,
        by 
          rw [sub_eq_add_neg]
          rw [←norm_neg] at hy 
          exact le_transₓ (padicNormE.nonarchimedean _ _) (max_le_iff.2 ⟨hx, hy⟩)⟩⟩

/-- Zero on ℤ_p is inherited from ℚ_p. -/
instance : HasZero ℤ_[p] :=
  ⟨⟨0,
      by 
        normNum⟩⟩

instance : Inhabited ℤ_[p] :=
  ⟨0⟩

/-- One on ℤ_p is inherited from ℚ_p. -/
instance : HasOne ℤ_[p] :=
  ⟨⟨1,
      by 
        normNum⟩⟩

@[simp]
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) :=
  rfl

@[simp]
theorem val_eq_coe (z : ℤ_[p]) : z.val = z :=
  rfl

@[simp, normCast]
theorem coe_add : ∀ z1 z2 : ℤ_[p], ((z1+z2 : ℤ_[p]) : ℚ_[p]) = z1+z2
| ⟨_, _⟩, ⟨_, _⟩ => rfl

@[simp, normCast]
theorem coe_mul : ∀ z1 z2 : ℤ_[p], ((z1*z2 : ℤ_[p]) : ℚ_[p]) = z1*z2
| ⟨_, _⟩, ⟨_, _⟩ => rfl

@[simp, normCast]
theorem coe_neg : ∀ z1 : ℤ_[p], ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1
| ⟨_, _⟩ => rfl

@[simp, normCast]
theorem coe_sub : ∀ z1 z2 : ℤ_[p], ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2
| ⟨_, _⟩, ⟨_, _⟩ => rfl

@[simp, normCast]
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 :=
  rfl

@[simp, normCast]
theorem coe_coe : ∀ n : ℕ, ((n : ℤ_[p]) : ℚ_[p]) = n
| 0 => rfl
| k+1 =>
  by 
    simp [coe_coe]

@[simp, normCast]
theorem coe_coe_int : ∀ z : ℤ, ((z : ℤ_[p]) : ℚ_[p]) = z
| Int.ofNat n =>
  by 
    simp 
| -[1+ n] =>
  by 
    simp 

@[simp, normCast]
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 :=
  rfl

instance : Ringₓ ℤ_[p] :=
  by 
    refineStruct
        { add := ·+·, mul := ·*·, neg := Neg.neg, zero := (0 : ℤ_[p]), one := 1, sub := Sub.sub,
          npow := @npowRec _ ⟨(1 : ℤ_[p])⟩ ⟨·*·⟩, nsmul := @nsmulRec _ ⟨(0 : ℤ_[p])⟩ ⟨·+·⟩,
          zsmul := @zsmulRec _ ⟨(0 : ℤ_[p])⟩ ⟨·+·⟩ ⟨Neg.neg⟩ } <;>
      intros  <;>
        try 
            rfl <;>
          ext <;> simp  <;> ring

/-- The coercion from ℤ[p] to ℚ[p] as a ring homomorphism. -/
def coe.ring_hom : ℤ_[p] →+* ℚ_[p] :=
  { toFun := (coeₓ : ℤ_[p] → ℚ_[p]), map_zero' := rfl, map_one' := rfl, map_mul' := coe_mul, map_add' := coe_add }

@[simp, normCast]
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : («expr↑ » (x^n) : ℚ_[p]) = ((«expr↑ » x : ℚ_[p])^n) :=
  coe.ring_hom.map_pow x n

@[simp]
theorem mk_coe : ∀ k : ℤ_[p], (⟨k, k.2⟩ : ℤ_[p]) = k
| ⟨_, _⟩ => rfl

/-- The inverse of a p-adic integer with norm equal to 1 is also a p-adic integer. Otherwise, the
inverse is defined to be 0. -/
def inv : ℤ_[p] → ℤ_[p]
| ⟨k, _⟩ =>
  if h : ∥k∥ = 1 then
    ⟨1 / k,
      by 
        simp [h]⟩
  else 0

instance : CharZero ℤ_[p] :=
  { cast_injective :=
      fun m n h =>
        Nat.cast_injective$
          show (m : ℚ_[p]) = n by 
            rw [Subtype.ext_iff] at h 
            normCast  at h 
            exact h }

@[simp, normCast]
theorem coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 :=
  suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2 from
    Iff.trans
      (by 
        normCast)
      this 
  by 
    normCast

/--
A sequence of integers that is Cauchy with respect to the `p`-adic norm
converges to a `p`-adic integer.
-/
def of_int_seq (seq : ℕ → ℤ) (h : IsCauSeq (padicNorm p) fun n => seq n) : ℤ_[p] :=
  ⟨«expr⟦ ⟧» ⟨_, h⟩,
    show «expr↑ » (PadicSeq.norm _) ≤ (1 : ℝ)by 
      rw [PadicSeq.norm]
      splitIfs with hne <;> normCast
      ·
        exact zero_le_one
      ·
        apply padicNorm.of_int⟩

end PadicInt

namespace PadicInt

/-!
### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/


variable (p : ℕ) [Fact p.prime]

instance : MetricSpace ℤ_[p] :=
  Subtype.metricSpace

instance CompleteSpace : CompleteSpace ℤ_[p] :=
  have  : IsClosed { x:ℚ_[p] | ∥x∥ ≤ 1 } := is_closed_le continuous_norm continuous_const 
  this.complete_space_coe

instance : HasNorm ℤ_[p] :=
  ⟨fun z => ∥(z : ℚ_[p])∥⟩

variable {p}

protected theorem mul_commₓ : ∀ z1 z2 : ℤ_[p], (z1*z2) = z2*z1
| ⟨q1, h1⟩, ⟨q2, h2⟩ =>
  show (⟨q1*q2, _⟩ : ℤ_[p]) = ⟨q2*q1, _⟩by 
    simp [_root_.mul_comm]

protected theorem zero_ne_one : (0 : ℤ_[p]) ≠ 1 :=
  show (⟨(0 : ℚ_[p]), _⟩ : ℤ_[p]) ≠ ⟨(1 : ℚ_[p]), _⟩ from mt Subtype.ext_iff_val.1 zero_ne_one

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : ℤ_[p], (a*b) = 0 → a = 0 ∨ b = 0
| ⟨a, ha⟩, ⟨b, hb⟩ =>
  fun h : (⟨a*b, _⟩ : ℤ_[p]) = ⟨0, _⟩ =>
    have  : (a*b) = 0 := Subtype.ext_iff_val.1 h
    (mul_eq_zero.1 this).elim
      (fun h1 =>
        Or.inl
          (by 
            simp [h1] <;> rfl))
      fun h2 =>
        Or.inr
          (by 
            simp [h2] <;> rfl)

theorem norm_def {z : ℤ_[p]} : ∥z∥ = ∥(z : ℚ_[p])∥ :=
  rfl

variable (p)

instance : NormedCommRing ℤ_[p] :=
  { dist_eq := fun ⟨_, _⟩ ⟨_, _⟩ => rfl, norm_mul := fun ⟨_, _⟩ ⟨_, _⟩ => norm_mul_le _ _,
    mul_comm := PadicInt.mul_comm }

instance : NormOneClass ℤ_[p] :=
  ⟨norm_def.trans norm_one⟩

instance IsAbsoluteValue : IsAbsoluteValue fun z : ℤ_[p] => ∥z∥ :=
  { abv_nonneg := norm_nonneg,
    abv_eq_zero :=
      fun ⟨_, _⟩ =>
        by 
          simp [norm_eq_zero],
    abv_add := fun ⟨_, _⟩ ⟨_, _⟩ => norm_add_le _ _,
    abv_mul :=
      fun _ _ =>
        by 
          simp only [norm_def, padicNormE.mul, PadicInt.coe_mul] }

variable {p}

instance : IsDomain ℤ_[p] :=
  { PadicInt.normedCommRing p with
    eq_zero_or_eq_zero_of_mul_eq_zero := fun x y => PadicInt.eq_zero_or_eq_zero_of_mul_eq_zero x y,
    exists_pair_ne := ⟨0, 1, PadicInt.zero_ne_one⟩ }

end PadicInt

namespace PadicInt

/-! ### Norm -/


variable {p : ℕ} [Fact p.prime]

theorem norm_le_one : ∀ z : ℤ_[p], ∥z∥ ≤ 1
| ⟨_, h⟩ => h

@[simp]
theorem norm_mul (z1 z2 : ℤ_[p]) : ∥z1*z2∥ = ∥z1∥*∥z2∥ :=
  by 
    simp [norm_def]

@[simp]
theorem norm_pow (z : ℤ_[p]) : ∀ n : ℕ, ∥z^n∥ = (∥z∥^n)
| 0 =>
  by 
    simp 
| k+1 =>
  by 
    rw [pow_succₓ, pow_succₓ, norm_mul]
    congr 
    apply norm_pow

theorem nonarchimedean : ∀ q r : ℤ_[p], ∥q+r∥ ≤ max ∥q∥ ∥r∥
| ⟨_, _⟩, ⟨_, _⟩ => padicNormE.nonarchimedean _ _

theorem norm_add_eq_max_of_ne : ∀ {q r : ℤ_[p]}, ∥q∥ ≠ ∥r∥ → ∥q+r∥ = max ∥q∥ ∥r∥
| ⟨_, _⟩, ⟨_, _⟩ => padicNormE.add_eq_max_of_ne

theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ∥z1+z2∥ < ∥z2∥) : ∥z1∥ = ∥z2∥ :=
  by_contradiction$
    fun hne =>
      not_lt_of_geₓ
        (by 
          rw [norm_add_eq_max_of_ne hne] <;> apply le_max_rightₓ)
        h

theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ∥z1+z2∥ < ∥z1∥) : ∥z1∥ = ∥z2∥ :=
  by_contradiction$
    fun hne =>
      not_lt_of_geₓ
        (by 
          rw [norm_add_eq_max_of_ne hne] <;> apply le_max_leftₓ)
        h

@[simp]
theorem padic_norm_e_of_padic_int (z : ℤ_[p]) : ∥(«expr↑ » z : ℚ_[p])∥ = ∥z∥ :=
  by 
    simp [norm_def]

theorem norm_int_cast_eq_padic_norm (z : ℤ) : ∥(z : ℤ_[p])∥ = ∥(z : ℚ_[p])∥ :=
  by 
    simp [norm_def]

@[simp]
theorem norm_eq_padic_norm {q : ℚ_[p]} (hq : ∥q∥ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ∥q∥ :=
  rfl

@[simp]
theorem norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ :=
  show ∥((p : ℤ_[p]) : ℚ_[p])∥ = p⁻¹by 
    exactModCast padicNormE.norm_p

@[simp]
theorem norm_p_pow (n : ℕ) : ∥(p : ℤ_[p])^n∥ = (p^(-n : ℤ)) :=
  show ∥((p^n : ℤ_[p]) : ℚ_[p])∥ = (p^(-n : ℤ))by 
    convert padicNormE.norm_p_pow n 
    simp 

private def cau_seq_to_rat_cau_seq (f : CauSeq ℤ_[p] norm) : CauSeq ℚ_[p] fun a => ∥a∥ :=
  ⟨fun n => f n,
    fun _ hε =>
      by 
        simpa [norm, norm_def] using f.cauchy hε⟩

variable (p)

instance complete : CauSeq.IsComplete ℤ_[p] norm :=
  ⟨fun f =>
      have hqn : ∥CauSeq.lim (cau_seq_to_rat_cau_seq f)∥ ≤ 1 := padic_norm_e_lim_le zero_lt_one fun _ => norm_le_one _
      ⟨⟨_, hqn⟩,
        fun ε =>
          by 
            simpa [norm, norm_def] using CauSeq.equiv_lim (cau_seq_to_rat_cau_seq f) ε⟩⟩

end PadicInt

namespace PadicInt

variable (p : ℕ) [hp_prime : Fact p.prime]

include hp_prime

theorem exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, («expr↑ » p^-((k : ℕ) : ℤ)) < ε :=
  by 
    obtain ⟨k, hk⟩ := exists_nat_gt (ε⁻¹)
    use k 
    rw [←inv_lt_inv hε (_root_.zpow_pos_of_pos _ _)]
    ·
      rw [zpow_neg₀, inv_inv₀, zpow_coe_nat]
      apply lt_of_lt_of_leₓ hk 
      normCast 
      apply le_of_ltₓ 
      convert Nat.lt_pow_self _ _ using 1 
      exact hp_prime.1.one_lt
    ·
      exactModCast hp_prime.1.Pos

theorem exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, («expr↑ » p^-((k : ℕ) : ℤ)) < ε :=
  by 
    obtain ⟨k, hk⟩ :=
      @exists_pow_neg_lt p _ ε
        (by 
          exactModCast hε)
    use k 
    rw
      [show (p : ℝ) = (p : ℚ)by 
        simp ] at
      hk 
    exactModCast hk

variable {p}

theorem norm_int_lt_one_iff_dvd (k : ℤ) : ∥(k : ℤ_[p])∥ < 1 ↔ «expr↑ » p ∣ k :=
  suffices ∥(k : ℚ_[p])∥ < 1 ↔ «expr↑ » p ∣ k by 
    rwa [norm_int_cast_eq_padic_norm]
  padicNormE.norm_int_lt_one_iff_dvd k

theorem norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} : ∥(k : ℤ_[p])∥ ≤ («expr↑ » p^(-n : ℤ)) ↔ («expr↑ » p^n) ∣ k :=
  suffices ∥(k : ℚ_[p])∥ ≤ («expr↑ » p^(-n : ℤ)) ↔ «expr↑ » (p^n) ∣ k by 
    simpa [norm_int_cast_eq_padic_norm]
  padicNormE.norm_int_le_pow_iff_dvd _ _

/-! ### Valuation on `ℤ_[p]` -/


/-- `padic_int.valuation` lifts the p-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def Valuation (x : ℤ_[p]) :=
  Padic.valuation (x : ℚ_[p])

theorem norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) : ∥x∥ = (p^-x.valuation) :=
  by 
    convert Padic.norm_eq_pow_val _ 
    contrapose! hx 
    exact Subtype.val_injective hx

@[simp]
theorem valuation_zero : Valuation (0 : ℤ_[p]) = 0 :=
  Padic.valuation_zero

@[simp]
theorem valuation_one : Valuation (1 : ℤ_[p]) = 0 :=
  Padic.valuation_one

@[simp]
theorem valuation_p : Valuation (p : ℤ_[p]) = 1 :=
  by 
    simp [Valuation, -cast_eq_of_rat_of_nat]

-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valuation_nonneg (x : «exprℤ_[ ]»(p)) : «expr ≤ »(0, x.valuation) :=
begin
  by_cases [expr hx, ":", expr «expr = »(x, 0)],
  { simp [] [] [] ["[", expr hx, "]"] [] [] },
  have [ident h] [":", expr «expr < »((1 : exprℝ()), p)] [":=", expr by exact_mod_cast [expr hp_prime.1.one_lt]],
  rw ["[", "<-", expr neg_nonpos, ",", "<-", expr (zpow_strict_mono h).le_iff_le, "]"] [],
  show [expr «expr ≤ »(«expr ^ »((p : exprℝ()), «expr- »(valuation x)), «expr ^ »(p, 0))],
  rw ["[", "<-", expr norm_eq_pow_val hx, "]"] [],
  simpa [] [] [] [] [] ["using", expr x.property]
end

-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem valuation_p_pow_mul
(n : exprℕ())
(c : «exprℤ_[ ]»(p))
(hc : «expr ≠ »(c, 0)) : «expr = »(«expr * »(«expr ^ »(«expr↑ »(p), n), c).valuation, «expr + »(n, c.valuation)) :=
begin
  have [] [":", expr «expr = »(«expr∥ ∥»(«expr * »(«expr ^ »(«expr↑ »(p), n), c)), «expr * »(«expr∥ ∥»((«expr ^ »(p, n) : «exprℤ_[ ]»(p))), «expr∥ ∥»(c)))] [],
  { exact [expr norm_mul _ _] },
  have [ident aux] [":", expr «expr ≠ »(«expr * »(«expr ^ »(«expr↑ »(p), n), c), 0)] [],
  { contrapose ["!"] [ident hc],
    rw [expr mul_eq_zero] ["at", ident hc],
    cases [expr hc] [],
    { refine [expr (hp_prime.1.ne_zero _).elim],
      exact_mod_cast [expr pow_eq_zero hc] },
    { exact [expr hc] } },
  rwa ["[", expr norm_eq_pow_val aux, ",", expr norm_p_pow, ",", expr norm_eq_pow_val hc, ",", "<-", expr zpow_add₀, ",", "<-", expr neg_add, ",", expr zpow_inj, ",", expr neg_inj, "]"] ["at", ident this],
  { exact_mod_cast [expr hp_prime.1.pos] },
  { exact_mod_cast [expr hp_prime.1.ne_one] },
  { exact_mod_cast [expr hp_prime.1.ne_zero] }
end

section Units

/-! ### Units of `ℤ_[p]` -/


attribute [local reducible] PadicInt

-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_inv : ∀ {z : «exprℤ_[ ]»(p)}, «expr = »(«expr∥ ∥»(z), 1) → «expr = »(«expr * »(z, z.inv), 1)
| ⟨k, _⟩, h := begin
  have [ident hk] [":", expr «expr ≠ »(k, 0)] [],
  from [expr λ h', @zero_ne_one «exprℚ_[ ]»(p) _ _ (by simpa [] [] [] ["[", expr h', "]"] [] ["using", expr h])],
  unfold [ident padic_int.inv] [],
  split_ifs [] [],
  { change [expr «expr = »((⟨«expr * »(k, «expr / »(1, k)), _⟩ : «exprℤ_[ ]»(p)), 1)] [] [],
    simp [] [] [] ["[", expr hk, "]"] [] [],
    refl },
  { apply [expr subtype.ext_iff_val.2],
    simp [] [] [] ["[", expr mul_inv_cancel hk, "]"] [] [] }
end

theorem inv_mul {z : ℤ_[p]} (hz : ∥z∥ = 1) : (z.inv*z) = 1 :=
  by 
    rw [mul_commₓ, mul_inv hz]

-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_unit_iff {z : «exprℤ_[ ]»(p)} : «expr ↔ »(is_unit z, «expr = »(«expr∥ ∥»(z), 1)) :=
⟨λ h, begin
   rcases [expr is_unit_iff_dvd_one.1 h, "with", "⟨", ident w, ",", ident eq, "⟩"],
   refine [expr le_antisymm (norm_le_one _) _],
   have [] [] [":=", expr mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)],
   rwa ["[", expr mul_one, ",", "<-", expr norm_mul, ",", "<-", expr eq, ",", expr norm_one, "]"] ["at", ident this]
 end, λ h, ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

theorem norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ∥z1∥ < 1) (hz2 : ∥z2∥ < 1) : ∥z1+z2∥ < 1 :=
  lt_of_le_of_ltₓ (nonarchimedean _ _) (max_ltₓ hz1 hz2)

theorem norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ∥z2∥ < 1) : ∥z1*z2∥ < 1 :=
  calc ∥z1*z2∥ = ∥z1∥*∥z2∥ :=
    by 
      simp 
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2
    

@[simp]
theorem mem_nonunits {z : ℤ_[p]} : z ∈ Nonunits ℤ_[p] ↔ ∥z∥ < 1 :=
  by 
    rw [lt_iff_le_and_ne] <;> simp [norm_le_one z, Nonunits, is_unit_iff]

/-- A `p`-adic number `u` with `∥u∥ = 1` is a unit of `ℤ_[p]`. -/
def mk_units {u : ℚ_[p]} (h : ∥u∥ = 1) : Units ℤ_[p] :=
  let z : ℤ_[p] := ⟨u, le_of_eqₓ h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
theorem mk_units_eq {u : ℚ_[p]} (h : ∥u∥ = 1) : ((mk_units h : ℤ_[p]) : ℚ_[p]) = u :=
  rfl

@[simp]
theorem norm_units (u : Units ℤ_[p]) : ∥(u : ℤ_[p])∥ = 1 :=
  is_unit_iff.mp$
    by 
      simp 

/-- `unit_coeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unit_coeff_spec`. -/
def unit_coeff {x : ℤ_[p]} (hx : x ≠ 0) : Units ℤ_[p] :=
  let u : ℚ_[p] := x*p^-x.valuation 
  have hu : ∥u∥ = 1 :=
    by 
      simp [hx,
        Nat.zpow_ne_zero_of_pos
          (by 
            exactModCast hp_prime.1.Pos)
          x.valuation,
        norm_eq_pow_val, zpow_neg, inv_mul_cancel, -cast_eq_of_rat_of_nat]
  mk_units hu

@[simp]
theorem unit_coeff_coe {x : ℤ_[p]} (hx : x ≠ 0) : (unit_coeff hx : ℚ_[p]) = x*p^-x.valuation :=
  rfl

-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unit_coeff_spec
{x : «exprℤ_[ ]»(p)}
(hx : «expr ≠ »(x, 0)) : «expr = »(x, «expr * »((unit_coeff hx : «exprℤ_[ ]»(p)), «expr ^ »(p, int.nat_abs (valuation x)))) :=
begin
  apply [expr subtype.coe_injective],
  push_cast [] [],
  have [ident repr] [":", expr «expr = »((x : «exprℚ_[ ]»(p)), «expr * »(unit_coeff hx, «expr ^ »(p, x.valuation)))] [],
  { rw ["[", expr unit_coeff_coe, ",", expr mul_assoc, ",", "<-", expr zpow_add₀, "]"] [],
    { simp [] [] [] [] [] [] },
    { exact_mod_cast [expr hp_prime.1.ne_zero] } },
  convert [] [expr repr] ["using", 2],
  rw ["[", "<-", expr zpow_coe_nat, ",", expr int.nat_abs_of_nonneg (valuation_nonneg x), "]"] []
end

end Units

section NormLeIff

/-! ### Various characterizations of open unit balls -/


-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_le_pow_iff_le_valuation
(x : «exprℤ_[ ]»(p))
(hx : «expr ≠ »(x, 0))
(n : exprℕ()) : «expr ↔ »(«expr ≤ »(«expr∥ ∥»(x), «expr ^ »(p, («expr- »(n) : exprℤ()))), «expr ≤ »(«expr↑ »(n), x.valuation)) :=
begin
  rw [expr norm_eq_pow_val hx] [],
  lift [expr x.valuation] ["to", expr exprℕ()] ["using", expr x.valuation_nonneg] ["with", ident k, ident hk],
  simp [] [] ["only"] ["[", expr int.coe_nat_le, ",", expr zpow_neg₀, ",", expr zpow_coe_nat, "]"] [] [],
  have [ident aux] [":", expr ∀ n : exprℕ(), «expr < »(0, («expr ^ »(p, n) : exprℝ()))] [],
  { apply [expr pow_pos],
    exact_mod_cast [expr hp_prime.1.pos] },
  rw ["[", expr inv_le_inv (aux _) (aux _), "]"] [],
  have [] [":", expr «expr ↔ »(«expr ≤ »(«expr ^ »(p, n), «expr ^ »(p, k)), «expr ≤ »(n, k))] [":=", expr (strict_mono_pow hp_prime.1.one_lt).le_iff_le],
  rw ["[", "<-", expr this, "]"] [],
  norm_cast []
end

theorem mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
  x ∈ (Ideal.span {p^n} : Ideal ℤ_[p]) ↔ «expr↑ » n ≤ x.valuation :=
  by 
    rw [Ideal.mem_span_singleton]
    split 
    ·
      rintro ⟨c, rfl⟩
      suffices  : c ≠ 0
      ·
        rw [valuation_p_pow_mul _ _ this, le_add_iff_nonneg_right]
        apply valuation_nonneg 
      contrapose! hx 
      rw [hx, mul_zero]
    ·
      rw [unit_coeff_spec hx]
      lift x.valuation to ℕ using x.valuation_nonneg with k hk 
      simp only [Int.nat_abs_of_nat, Units.is_unit, IsUnit.dvd_mul_left, Int.coe_nat_le]
      intro H 
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le H 
      simp only [pow_addₓ, dvd_mul_right]

theorem norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) : ∥x∥ ≤ (p^(-n : ℤ)) ↔ x ∈ (Ideal.span {p^n} : Ideal ℤ_[p]) :=
  by 
    byCases' hx : x = 0
    ·
      subst hx 
      simp only [norm_zero, zpow_neg₀, zpow_coe_nat, inv_nonneg, iff_trueₓ, Submodule.zero_mem]
      exactModCast Nat.zero_leₓ _ 
    rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx]

theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) : ∥x∥ ≤ (p^n) ↔ ∥x∥ < (p^n+1) :=
  by 
    rw [norm_def]
    exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _

theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) : ∥x∥ < (p^n) ↔ ∥x∥ ≤ (p^n - 1) :=
  by 
    rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]

-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_lt_one_iff_dvd (x : «exprℤ_[ ]»(p)) : «expr ↔ »(«expr < »(«expr∥ ∥»(x), 1), «expr ∣ »(«expr↑ »(p), x)) :=
begin
  have [] [] [":=", expr norm_le_pow_iff_mem_span_pow x 1],
  rw ["[", expr ideal.mem_span_singleton, ",", expr pow_one, "]"] ["at", ident this],
  rw ["[", "<-", expr this, ",", expr norm_le_pow_iff_norm_lt_pow_add_one, "]"] [],
  simp [] [] ["only"] ["[", expr zpow_zero, ",", expr int.coe_nat_zero, ",", expr int.coe_nat_succ, ",", expr add_left_neg, ",", expr zero_add, "]"] [] []
end

@[simp]
theorem pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p^n : ℤ_[p]) ∣ a ↔ («expr↑ » p^n) ∣ a :=
  by 
    rw [←norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

end NormLeIff

section Dvr

/-! ### Discrete valuation ring -/


instance : LocalRing ℤ_[p] :=
  local_of_nonunits_ideal zero_ne_one$
    fun x y =>
      by 
        simp  <;> exact norm_lt_one_add

theorem p_nonnunit : (p : ℤ_[p]) ∈ Nonunits ℤ_[p] :=
  have  : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one$
      by 
        exactModCast hp_prime.1.one_lt 
  by 
    simp [this]

theorem maximal_ideal_eq_span_p : maximal_ideal ℤ_[p] = Ideal.span {p} :=
  by 
    apply le_antisymmₓ
    ·
      intro x hx 
      rw [Ideal.mem_span_singleton]
      simp only [LocalRing.mem_maximal_ideal, mem_nonunits] at hx 
      rwa [←norm_lt_one_iff_dvd]
    ·
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact p_nonnunit

theorem prime_p : Prime (p : ℤ_[p]) :=
  by 
    rw [←Ideal.span_singleton_prime, ←maximal_ideal_eq_span_p]
    ·
      infer_instance
    ·
      exactModCast hp_prime.1.ne_zero

theorem irreducible_p : Irreducible (p : ℤ_[p]) :=
  Prime.irreducible prime_p

instance : DiscreteValuationRing ℤ_[p] :=
  DiscreteValuationRing.of_has_unit_mul_pow_irreducible_factorization
    ⟨p, irreducible_p,
      fun x hx =>
        ⟨x.valuation.nat_abs, unit_coeff hx,
          by 
            rw [mul_commₓ, ←unit_coeff_spec hx]⟩⟩

theorem ideal_eq_span_pow_p {s : Ideal ℤ_[p]} (hs : s ≠ ⊥) : ∃ n : ℕ, s = Ideal.span {p^n} :=
  DiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p

open CauSeq

-- error in NumberTheory.Padics.PadicIntegers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : is_adic_complete (maximal_ideal «exprℤ_[ ]»(p)) «exprℤ_[ ]»(p) :=
{ prec' := λ x hx, begin
    simp [] [] ["only"] ["[", "<-", expr ideal.one_eq_top, ",", expr smul_eq_mul, ",", expr mul_one, ",", expr smodeq.sub_mem, ",", expr maximal_ideal_eq_span_p, ",", expr ideal.span_singleton_pow, ",", "<-", expr norm_le_pow_iff_mem_span_pow, "]"] [] ["at", ident hx, "⊢"],
    let [ident x'] [":", expr cau_seq «exprℤ_[ ]»(p) norm] [":=", expr ⟨x, _⟩],
    swap,
    { intros [ident ε, ident hε],
      obtain ["⟨", ident m, ",", ident hm, "⟩", ":=", expr exists_pow_neg_lt p hε],
      refine [expr ⟨m, λ n hn, lt_of_le_of_lt _ hm⟩],
      rw ["[", "<-", expr neg_sub, ",", expr norm_neg, "]"] [],
      exact [expr hx hn] },
    { refine [expr ⟨x'.lim, λ n, _⟩],
      have [] [":", expr «expr < »((0 : exprℝ()), «expr ^ »(p, («expr- »(n) : exprℤ())))] [],
      { apply [expr zpow_pos_of_pos],
        exact_mod_cast [expr hp_prime.1.pos] },
      obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr equiv_def₃ (equiv_lim x') this],
      by_cases [expr hin, ":", expr «expr ≤ »(i, n)],
      { exact [expr (hi i le_rfl n hin).le] },
      { push_neg ["at", ident hin],
        specialize [expr hi i le_rfl i le_rfl],
        specialize [expr hx hin.le],
        have [] [] [":=", expr nonarchimedean «expr - »(x n, x i) «expr - »(x i, x'.lim)],
        rw ["[", expr sub_add_sub_cancel, "]"] ["at", ident this],
        refine [expr this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)] } }
  end }

end Dvr

end PadicInt

