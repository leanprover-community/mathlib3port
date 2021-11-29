import Mathbin.NumberTheory.Zsqrtd.Basic 
import Mathbin.Data.Complex.Basic 
import Mathbin.RingTheory.PrincipalIdealDomain 
import Mathbin.NumberTheory.QuadraticReciprocity

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `to_complex` into the complex numbers is also defined in this file.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notations

This file uses the local notation `ℤ[i]` for `gaussian_int`

## Implementation notes

Gaussian integers are implemented using the more general definition `zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `zsqrtd` can easily be used.
-/


open Zsqrtd Complex

@[reducible]
def GaussianInt : Type :=
  Zsqrtd (-1)

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

instance  : HasRepr ℤ[i] :=
  ⟨fun x => "⟨" ++ reprₓ x.re ++ ", " ++ reprₓ x.im ++ "⟩"⟩

instance  : CommRingₓ ℤ[i] :=
  Zsqrtd.commRing

section 

attribute [-instance] Complex.field

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def to_complex : ℤ[i] →+* ℂ :=
  Zsqrtd.lift
    ⟨I,
      by 
        simp ⟩

end 

instance  : Coe ℤ[i] ℂ :=
  ⟨to_complex⟩

theorem to_complex_def (x : ℤ[i]) : (x : ℂ) = x.re+x.im*I :=
  rfl

theorem to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x+y*I :=
  by 
    simp [to_complex_def]

theorem to_complex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ :=
  by 
    apply Complex.ext <;> simp [to_complex_def]

@[simp]
theorem to_real_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re :=
  by 
    simp [to_complex_def]

@[simp]
theorem to_real_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im :=
  by 
    simp [to_complex_def]

@[simp]
theorem to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x :=
  by 
    simp [to_complex_def]

@[simp]
theorem to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y :=
  by 
    simp [to_complex_def]

@[simp]
theorem to_complex_add (x y : ℤ[i]) : ((x+y : ℤ[i]) : ℂ) = x+y :=
  to_complex.map_add _ _

@[simp]
theorem to_complex_mul (x y : ℤ[i]) : ((x*y : ℤ[i]) : ℂ) = x*y :=
  to_complex.map_mul _ _

@[simp]
theorem to_complex_one : ((1 : ℤ[i]) : ℂ) = 1 :=
  to_complex.map_one

@[simp]
theorem to_complex_zero : ((0 : ℤ[i]) : ℂ) = 0 :=
  to_complex.map_zero

@[simp]
theorem to_complex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x :=
  to_complex.map_neg _

@[simp]
theorem to_complex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y :=
  to_complex.map_sub _ _

@[simp]
theorem to_complex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y :=
  by 
    cases x <;> cases y <;> simp [to_complex_def₂]

@[simp]
theorem to_complex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 :=
  by 
    rw [←to_complex_zero, to_complex_inj]

@[simp]
theorem nat_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = (x : ℂ).normSq :=
  by 
    rw [norm, norm_sq] <;> simp 

@[simp]
theorem nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).normSq :=
  by 
    cases x <;> rw [norm, norm_sq] <;> simp 

theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
  norm_nonneg
    (by 
      normNum)
    _

@[simp]
theorem norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 :=
  by 
    rw [←@Int.cast_inj ℝ _ _ _] <;> simp 

theorem norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 :=
  by 
    rw [lt_iff_le_and_ne, Ne.def, eq_comm, norm_eq_zero] <;> simp [norm_nonneg]

@[simp]
theorem coe_nat_abs_norm (x : ℤ[i]) : (x.norm.nat_abs : ℤ) = x.norm :=
  Int.nat_abs_of_nonneg (norm_nonneg _)

@[simp]
theorem nat_cast_nat_abs_norm {α : Type _} [Ringₓ α] (x : ℤ[i]) : (x.norm.nat_abs : α) = x.norm :=
  by 
    rw [←Int.cast_coe_nat, coe_nat_abs_norm]

theorem nat_abs_norm_eq (x : ℤ[i]) : x.norm.nat_abs = (x.re.nat_abs*x.re.nat_abs)+x.im.nat_abs*x.im.nat_abs :=
  Int.coe_nat_inj$
    by 
      simp 
      simp [norm]

protected def div (x y : ℤ[i]) : ℤ[i] :=
  let n := Rat.ofInt (norm y)⁻¹
  let c := y.conj
  ⟨round (Rat.ofInt (x*c).re*n : ℚ), round (Rat.ofInt (x*c).im*n : ℚ)⟩

instance  : Div ℤ[i] :=
  ⟨GaussianInt.div⟩

theorem div_def (x y : ℤ[i]) : x / y = ⟨round ((x*conj y).re / norm y : ℚ), round ((x*conj y).im / norm y : ℚ)⟩ :=
  show Zsqrtd.mk _ _ = _ by 
    simp [Rat.of_int_eq_mk, Rat.mk_eq_div, div_eq_mul_inv]

theorem to_complex_div_re (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round (x / y : ℂ).re :=
  by 
    rw [div_def, ←@Rat.round_cast ℝ _ _] <;> simp [-Rat.round_cast, mul_assocₓ, div_eq_mul_inv, mul_addₓ, add_mulₓ]

theorem to_complex_div_im (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round (x / y : ℂ).im :=
  by 
    rw [div_def, ←@Rat.round_cast ℝ _ _, ←@Rat.round_cast ℝ _ _] <;>
      simp [-Rat.round_cast, mul_assocₓ, div_eq_mul_inv, mul_addₓ, add_mulₓ]

theorem norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|) (him : |x.im| ≤ |y.im|) :
  x.norm_sq ≤ y.norm_sq :=
  by 
    rw [norm_sq_apply, norm_sq_apply, ←_root_.abs_mul_self, _root_.abs_mul, ←_root_.abs_mul_self y.re,
        _root_.abs_mul y.re, ←_root_.abs_mul_self x.im, _root_.abs_mul x.im, ←_root_.abs_mul_self y.im,
        _root_.abs_mul y.im] <;>
      exact add_le_add (mul_self_le_mul_self (abs_nonneg _) hre) (mul_self_le_mul_self (abs_nonneg _) him)

theorem norm_sq_div_sub_div_lt_one (x y : ℤ[i]) : ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).normSq < 1 :=
  calc
    ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).normSq =
      (((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re)+((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im)*I : ℂ).normSq :=
    congr_argₓ _$
      by 
        apply Complex.ext <;> simp 
    _ ≤ ((1 / 2)+(1 / 2)*I).normSq :=
    have  : |(2⁻¹ : ℝ)| = 2⁻¹ :=
      _root_.abs_of_nonneg
        (by 
          normNum)
    norm_sq_le_norm_sq_of_re_le_of_im_le
      (by 
        rw [to_complex_div_re] <;> simp [norm_sq, this] <;> simpa using abs_sub_round (x / y : ℂ).re)
      (by 
        rw [to_complex_div_im] <;> simp [norm_sq, this] <;> simpa using abs_sub_round (x / y : ℂ).im)
    _ < 1 :=
    by 
      simp [norm_sq] <;> normNum
    

protected def mod (x y : ℤ[i]) : ℤ[i] :=
  x - y*x / y

instance  : Mod ℤ[i] :=
  ⟨GaussianInt.mod⟩

theorem mod_def (x y : ℤ[i]) : x % y = x - y*x / y :=
  rfl

theorem norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
  have  : (y : ℂ) ≠ 0 :=
    by 
      rwa [Ne.def, ←to_complex_zero, to_complex_inj]
  (@Int.cast_lt ℝ _ _ _ _).1$
    calc «expr↑ » (norm (x % y)) = (x - y*(x / y : ℤ[i]) : ℂ).normSq :=
      by 
        simp [mod_def]
      _ = (y : ℂ).normSq*(x / y - (x / y : ℤ[i]) : ℂ).normSq :=
      by 
        rw [←norm_sq_mul, mul_sub, mul_div_cancel' _ this]
      _ < (y : ℂ).normSq*1 := mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _) (norm_sq_pos.2 this)
      _ = norm y :=
      by 
        simp 
      

theorem nat_abs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm.natAbs < y.norm.nat_abs :=
  Int.coe_nat_lt.1
    (by 
      simp [-Int.coe_nat_lt, norm_mod_lt x hy])

theorem norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (norm x).natAbs ≤ (norm (x*y)).natAbs :=
  by 
    rw [norm_mul, Int.nat_abs_mul] <;>
      exact
        le_mul_of_one_le_right (Nat.zero_leₓ _)
          (Int.coe_nat_le.1
            (by 
              rw [coe_nat_abs_norm] <;> exact Int.add_one_le_of_lt (norm_pos.2 hy)))

instance  : Nontrivial ℤ[i] :=
  ⟨⟨0, 1,
      by 
        decide⟩⟩

instance  : EuclideanDomain ℤ[i] :=
  { GaussianInt.commRing, GaussianInt.nontrivial with Quotient := · / ·, remainder := · % ·,
    quotient_zero :=
      by 
        simp [div_def]
        rfl,
    quotient_mul_add_remainder_eq :=
      fun _ _ =>
        by 
          simp [mod_def],
    R := _, r_well_founded := measure_wf (Int.natAbs ∘ norm), remainder_lt := nat_abs_norm_mod_lt,
    mul_left_not_lt := fun a b hb0 => not_lt_of_geₓ$ norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing

-- error in NumberTheory.Zsqrtd.GaussianInt: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mod_four_eq_three_of_nat_prime_of_prime
(p : exprℕ())
[hp : fact p.prime]
(hpi : prime (p : «exprℤ[i]»())) : «expr = »(«expr % »(p, 4), 3) :=
hp.1.eq_two_or_odd.elim (λ
 hp2, absurd hpi «expr $ »(mt irreducible_iff_prime.2, λ ⟨hu, h⟩, begin
    have [] [] [":=", expr h ⟨1, 1⟩ ⟨1, «expr- »(1)⟩ «expr ▸ »(hp2.symm, rfl)],
    rw ["[", "<-", expr norm_eq_one_iff, ",", "<-", expr norm_eq_one_iff, "]"] ["at", ident this],
    exact [expr absurd this exprdec_trivial()]
  end)) (λ
 hp1, «expr $ »(by_contradiction, λ
  hp3 : «expr ≠ »(«expr % »(p, 4), 3), have hp41 : «expr = »(«expr % »(p, 4), 1), begin
    rw ["[", "<-", expr nat.mod_mul_left_mod p 2 2, ",", expr show «expr = »(«expr * »(2, 2), 4), from rfl, "]"] ["at", ident hp1],
    have [] [] [":=", expr nat.mod_lt p (show «expr < »(0, 4), from exprdec_trivial())],
    revert [ident this, ident hp3, ident hp1],
    generalize [] [":"] [expr «expr = »(«expr % »(p, 4), m)],
    dec_trivial ["!"]
  end,
  let ⟨k, hk⟩ := «expr $ »((zmod.exists_sq_eq_neg_one_iff_mod_four_ne_three p).2, by rw [expr hp41] []; exact [expr exprdec_trivial()]) in
  begin
    obtain ["⟨", ident k, ",", ident k_lt_p, ",", ident rfl, "⟩", ":", expr «expr∃ , »((k' : exprℕ())
      (h : «expr < »(k', p)), «expr = »((k' : zmod p), k))],
    { refine [expr ⟨k.val, k.val_lt, zmod.nat_cast_zmod_val k⟩] },
    have [ident hpk] [":", expr «expr ∣ »(p, «expr + »(«expr ^ »(k, 2), 1))] [],
    by rw ["[", "<-", expr char_p.cast_eq_zero_iff (zmod p) p, "]"] []; simp [] [] [] ["*"] [] [],
    have [ident hkmul] [":", expr «expr = »((«expr + »(«expr ^ »(k, 2), 1) : «exprℤ[i]»()), «expr * »(⟨k, 1⟩, ⟨k, «expr- »(1)⟩))] [":=", expr by simp [] [] [] ["[", expr sq, ",", expr zsqrtd.ext, "]"] [] []],
    have [ident hpne1] [":", expr «expr ≠ »(p, 1)] [":=", expr ne_of_gt hp.1.one_lt],
    have [ident hkltp] [":", expr «expr < »(«expr + »(1, «expr * »(k, k)), «expr * »(p, p))] [],
    from [expr calc
       «expr ≤ »(«expr + »(1, «expr * »(k, k)), «expr + »(k, «expr * »(k, k))) : add_le_add_right (nat.pos_of_ne_zero (λ
         hk0, by clear_aux_decl; simp [] [] [] ["[", "*", ",", expr pow_succ', "]"] [] ["at", "*"])) _
       «expr = »(..., «expr * »(k, «expr + »(k, 1))) : by simp [] [] [] ["[", expr add_comm, ",", expr mul_add, "]"] [] []
       «expr < »(..., «expr * »(p, p)) : mul_lt_mul k_lt_p k_lt_p (nat.succ_pos _) (nat.zero_le _)],
    have [ident hpk₁] [":", expr «expr¬ »(«expr ∣ »((p : «exprℤ[i]»()), ⟨k, «expr- »(1)⟩))] [":=", expr λ
     ⟨x, hx⟩, «expr $ »(lt_irrefl («expr * »(p, x) : «exprℤ[i]»()).norm.nat_abs, calc
        «expr = »((norm («expr * »(p, x) : «exprℤ[i]»())).nat_abs, (norm ⟨k, «expr- »(1)⟩).nat_abs) : by rw [expr hx] []
        «expr < »(..., (norm (p : «exprℤ[i]»())).nat_abs) : by simpa [] [] [] ["[", expr add_comm, ",", expr norm, "]"] [] ["using", expr hkltp]
        «expr ≤ »(..., (norm («expr * »(p, x) : «exprℤ[i]»())).nat_abs) : norm_le_norm_mul_left _ (λ
         hx0, «expr $ »(show «expr ≠ »((«expr- »(1) : exprℤ()), 0), from exprdec_trivial(), by simpa [] [] [] ["[", expr hx0, "]"] [] ["using", expr congr_arg zsqrtd.im hx])))],
    have [ident hpk₂] [":", expr «expr¬ »(«expr ∣ »((p : «exprℤ[i]»()), ⟨k, 1⟩))] [":=", expr λ
     ⟨x, hx⟩, «expr $ »(lt_irrefl («expr * »(p, x) : «exprℤ[i]»()).norm.nat_abs, calc
        «expr = »((norm («expr * »(p, x) : «exprℤ[i]»())).nat_abs, (norm ⟨k, 1⟩).nat_abs) : by rw [expr hx] []
        «expr < »(..., (norm (p : «exprℤ[i]»())).nat_abs) : by simpa [] [] [] ["[", expr add_comm, ",", expr norm, "]"] [] ["using", expr hkltp]
        «expr ≤ »(..., (norm («expr * »(p, x) : «exprℤ[i]»())).nat_abs) : norm_le_norm_mul_left _ (λ
         hx0, «expr $ »(show «expr ≠ »((1 : exprℤ()), 0), from exprdec_trivial(), by simpa [] [] [] ["[", expr hx0, "]"] [] ["using", expr congr_arg zsqrtd.im hx])))],
    have [ident hpu] [":", expr «expr¬ »(is_unit (p : «exprℤ[i]»()))] [],
    from [expr mt norm_eq_one_iff.2 (by rw ["[", expr norm_nat_cast, ",", expr int.nat_abs_mul, ",", expr nat.mul_eq_one_iff, "]"] []; exact [expr λ
       h, (ne_of_lt hp.1.one_lt).symm h.1])],
    obtain ["⟨", ident y, ",", ident hy, "⟩", ":=", expr hpk],
    have [] [] [":=", expr hpi.2.2 ⟨k, 1⟩ ⟨k, «expr- »(1)⟩ ⟨y, by rw ["[", "<-", expr hkmul, ",", "<-", expr nat.cast_mul p, ",", "<-", expr hy, "]"] []; simp [] [] [] [] [] []⟩],
    clear_aux_decl,
    tauto []
  end))

theorem sq_add_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.prime] (hpi : ¬Irreducible (p : ℤ[i])) :
  ∃ a b, ((a^2)+b^2) = p :=
  have hpu : ¬IsUnit (p : ℤ[i]) :=
    mt norm_eq_one_iff.2$
      by 
        rw [norm_nat_cast, Int.nat_abs_mul, Nat.mul_eq_one_iff] <;> exact fun h => (ne_of_ltₓ hp.1.one_lt).symm h.1
  have hab : ∃ a b, ((p : ℤ[i]) = a*b) ∧ ¬IsUnit a ∧ ¬IsUnit b :=
    by 
      simpa [irreducible_iff, hpu, not_forall, not_or_distrib] using hpi 
  let ⟨a, b, hpab, hau, hbu⟩ := hab 
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1$
        by 
          rw [←Int.coe_nat_inj', Int.coe_nat_pow, sq, ←@norm_nat_cast (-1), hpab] <;> simp ).1
  ⟨a.re.nat_abs, a.im.nat_abs,
    by 
      simpa [nat_abs_norm_eq, sq] using hnap⟩

theorem prime_of_nat_prime_of_mod_four_eq_three (p : ℕ) [hp : Fact p.prime] (hp3 : p % 4 = 3) : Prime (p : ℤ[i]) :=
  irreducible_iff_prime.1$
    Classical.by_contradiction$
      fun hpi =>
        let ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi 
        have  : ∀ (a b : Zmod 4), ((a^2)+b^2) ≠ p :=
          by 
            erw [←Zmod.nat_cast_mod 4 p, hp3] <;>
              exact
                by 
                  decide 
        this a b
          (hab ▸
            by 
              simp )

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
theorem prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [hp : Fact p.prime] : Prime (p : ℤ[i]) ↔ p % 4 = 3 :=
  ⟨mod_four_eq_three_of_nat_prime_of_prime p, prime_of_nat_prime_of_mod_four_eq_three p⟩

end GaussianInt

