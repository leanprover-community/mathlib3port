import Mathbin.Data.Real.CauSeq

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a commutative ring
with absolute value.
-/


namespace CauSeq.Completion

open CauSeq

section 

parameter {α : Type _}[LinearOrderedField α]

parameter {β : Type _}[CommRingₓ β]{abv : β → α}[IsAbsoluteValue abv]

/-- The Cauchy completion of a commutative ring with absolute value. -/
def Cauchy :=
  @Quotientₓ (CauSeq _ abv) CauSeq.equiv

/-- The map from Cauchy sequences into the Cauchy completion. -/
def mk : CauSeq _ abv → Cauchy :=
  Quotientₓ.mk

@[simp]
theorem mk_eq_mk f : @Eq Cauchy («expr⟦ ⟧» f) (mk f) :=
  rfl

theorem mk_eq {f g} : mk f = mk g ↔ f ≈ g :=
  Quotientₓ.eq

/-- The map from the original ring into the Cauchy completion. -/
def of_rat (x : β) : Cauchy :=
  mk (const abv x)

instance : HasZero Cauchy :=
  ⟨of_rat 0⟩

instance : HasOne Cauchy :=
  ⟨of_rat 1⟩

instance : Inhabited Cauchy :=
  ⟨0⟩

theorem of_rat_zero : of_rat 0 = 0 :=
  rfl

theorem of_rat_one : of_rat 1 = 1 :=
  rfl

-- error in Data.Real.CauSeqCompletion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem mk_eq_zero {f} : «expr ↔ »(«expr = »(mk f, 0), lim_zero f) :=
by have [] [":", expr «expr ↔ »(«expr = »(mk f, 0), lim_zero «expr - »(f, 0))] [":=", expr quotient.eq]; rwa [expr sub_zero] ["at", ident this]

instance : Add Cauchy :=
  ⟨fun x y =>
      (Quotientₓ.liftOn₂ x y fun f g => mk (f+g))$
        fun f₁ g₁ f₂ g₂ hf hg =>
          Quotientₓ.sound$
            by 
              simpa [· ≈ ·, Setoidₓ.R, sub_eq_add_neg, add_commₓ, add_left_commₓ, add_assocₓ] using add_lim_zero hf hg⟩

@[simp]
theorem mk_add (f g : CauSeq β abv) : (mk f+mk g) = mk (f+g) :=
  rfl

instance : Neg Cauchy :=
  ⟨fun x =>
      (Quotientₓ.liftOn x fun f => mk (-f))$
        fun f₁ f₂ hf =>
          Quotientₓ.sound$
            by 
              simpa [· ≈ ·, Setoidₓ.R] using neg_lim_zero hf⟩

@[simp]
theorem mk_neg (f : CauSeq β abv) : -mk f = mk (-f) :=
  rfl

instance : Mul Cauchy :=
  ⟨fun x y =>
      (Quotientₓ.liftOn₂ x y fun f g => mk (f*g))$
        fun f₁ g₁ f₂ g₂ hf hg =>
          Quotientₓ.sound$
            by 
              simpa [· ≈ ·, Setoidₓ.R, mul_addₓ, mul_commₓ, add_assocₓ, sub_eq_add_neg] using
                add_lim_zero (mul_lim_zero_right g₁ hf) (mul_lim_zero_right f₂ hg)⟩

@[simp]
theorem mk_mul (f g : CauSeq β abv) : (mk f*mk g) = mk (f*g) :=
  rfl

instance : Sub Cauchy :=
  ⟨fun x y =>
      (Quotientₓ.liftOn₂ x y fun f g => mk (f - g))$
        fun f₁ g₁ f₂ g₂ hf hg =>
          Quotientₓ.sound$
            show (f₁ - g₁ - (f₂ - g₂)).LimZero by 
              simpa [sub_eq_add_neg, add_assocₓ, add_commₓ, add_left_commₓ] using sub_lim_zero hf hg⟩

@[simp]
theorem mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g) :=
  rfl

theorem of_rat_add (x y : β) : of_rat (x+y) = of_rat x+of_rat y :=
  congr_argₓ mk (const_add _ _)

theorem of_rat_neg (x : β) : of_rat (-x) = -of_rat x :=
  congr_argₓ mk (const_neg _)

theorem of_rat_mul (x y : β) : of_rat (x*y) = of_rat x*of_rat y :=
  congr_argₓ mk (const_mul _ _)

private theorem zero_def : 0 = mk 0 :=
  rfl

private theorem one_def : 1 = mk 1 :=
  rfl

instance : CommRingₓ Cauchy :=
  by 
    refine'
        { neg := Neg.neg, sub := Sub.sub, sub_eq_add_neg := _, add := ·+·, zero := (0 : Cauchy), mul := ·*·, one := 1,
          nsmul := nsmulRec, npow := npowRec, zsmul := zsmulRec, .. } <;>
      try 
          intros  <;> rfl <;>
        ·
          repeat' 
            refine' fun a => Quotientₓ.induction_on a fun _ => _ 
          simp [zero_def, one_def, mul_left_commₓ, mul_commₓ, mul_addₓ, add_commₓ, add_left_commₓ, sub_eq_add_neg]

theorem of_rat_sub (x y : β) : of_rat (x - y) = of_rat x - of_rat y :=
  congr_argₓ mk (const_sub _ _)

end 

open_locale Classical

section 

parameter {α : Type _}[LinearOrderedField α]

parameter {β : Type _}[Field β]{abv : β → α}[IsAbsoluteValue abv]

local notation "Cauchy" => @Cauchy _ _ _ _ abv _

-- error in Data.Real.CauSeqCompletion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
noncomputable instance : has_inv exprCauchy() :=
⟨λ
 x, «expr $ »(quotient.lift_on x (λ f, «expr $ »(mk, if h : lim_zero f then 0 else inv f h)), λ f g fg, begin
    have [] [] [":=", expr lim_zero_congr fg],
    by_cases [expr hf, ":", expr lim_zero f],
    { simp [] [] [] ["[", expr hf, ",", expr this.1 hf, ",", expr setoid.refl, "]"] [] [] },
    { have [ident hg] [] [":=", expr mt this.2 hf],
      simp [] [] [] ["[", expr hf, ",", expr hg, "]"] [] [],
      have [ident If] [":", expr «expr = »(«expr * »(mk (inv f hf), mk f), 1)] [":=", expr mk_eq.2 (inv_mul_cancel hf)],
      have [ident Ig] [":", expr «expr = »(«expr * »(mk (inv g hg), mk g), 1)] [":=", expr mk_eq.2 (inv_mul_cancel hg)],
      rw ["[", expr mk_eq.2 fg, ",", "<-", expr Ig, "]"] ["at", ident If],
      rw [expr mul_comm] ["at", ident Ig],
      rw ["[", "<-", expr mul_one (mk (inv f hf)), ",", "<-", expr Ig, ",", "<-", expr mul_assoc, ",", expr If, ",", expr mul_assoc, ",", expr Ig, ",", expr mul_one, "]"] [] }
  end)⟩

@[simp]
theorem inv_zero : (0 : Cauchy)⁻¹ = 0 :=
  congr_argₓ mk$
    by 
      rw [dif_pos] <;> [rfl, exact zero_lim_zero]

@[simp]
theorem inv_mk {f} hf : @mk α _ β _ abv _ f⁻¹ = mk (inv f hf) :=
  congr_argₓ mk$
    by 
      rw [dif_neg]

theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 :=
  fun h =>
    have  : lim_zero (1 - 0) := Setoidₓ.symm h 
    have  : lim_zero 1 :=
      by 
        simpa 
    one_ne_zero$ const_lim_zero.1 this

theorem zero_ne_one : (0 : Cauchy) ≠ 1 :=
  fun h => cau_seq_zero_ne_one$ mk_eq.1 h

protected theorem inv_mul_cancel {x : Cauchy} : x ≠ 0 → (x⁻¹*x) = 1 :=
  Quotientₓ.induction_on x$
    fun f hf =>
      by 
        simp  at hf 
        simp [hf]
        exact Quotientₓ.sound (CauSeq.inv_mul_cancel hf)

/-- The Cauchy completion forms a field.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def Field : Field Cauchy :=
  { Cauchy.comm_ring with inv := HasInv.inv,
    mul_inv_cancel :=
      fun x x0 =>
        by 
          rw [mul_commₓ, CauSeq.Completion.inv_mul_cancel x0],
    exists_pair_ne := ⟨0, 1, zero_ne_one⟩, inv_zero }

attribute [local instance] Field

theorem of_rat_inv (x : β) : of_rat (x⁻¹) = (of_rat x⁻¹ : Cauchy) :=
  congr_argₓ mk$
    by 
      splitIfs with h <;> [simp [const_lim_zero.1 h], rfl]

theorem of_rat_div (x y : β) : of_rat (x / y) = (of_rat x / of_rat y : Cauchy) :=
  by 
    simp only [div_eq_inv_mul, of_rat_inv, of_rat_mul]

end 

end CauSeq.Completion

variable {α : Type _} [LinearOrderedField α]

namespace CauSeq

section 

variable (β : Type _) [Ringₓ β] (abv : β → α) [IsAbsoluteValue abv]

/-- A class stating that a ring with an absolute value is complete, i.e. every Cauchy
sequence has a limit. -/
class is_complete where 
  IsComplete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b

end 

section 

variable {β : Type _} [Ringₓ β] {abv : β → α} [IsAbsoluteValue abv]

variable [is_complete β abv]

theorem complete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b :=
  is_complete.is_complete

/-- The limit of a Cauchy sequence in a complete ring. Chosen non-computably. -/
noncomputable def lim (s : CauSeq β abv) : β :=
  Classical.some (complete s)

theorem equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s) :=
  Classical.some_spec (complete s)

theorem eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f) : x = lim f :=
  const_equiv.mp$ Setoidₓ.trans h$ equiv_lim f

theorem lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x) : lim f = x :=
  (eq_lim_of_const_equiv$ Setoidₓ.symm h).symm

theorem lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : lim f = lim g :=
  lim_eq_of_equiv_const$ Setoidₓ.trans h$ equiv_lim g

@[simp]
theorem lim_const (x : β) : lim (const abv x) = x :=
  lim_eq_of_equiv_const$ Setoidₓ.refl _

theorem lim_add (f g : CauSeq β abv) : (lim f+lim g) = lim (f+g) :=
  eq_lim_of_const_equiv$
    show lim_zero (const abv (lim f+lim g) - f+g)by 
      rw [const_add, add_sub_comm] <;> exact add_lim_zero (Setoidₓ.symm (equiv_lim f)) (Setoidₓ.symm (equiv_lim g))

theorem lim_mul_lim (f g : CauSeq β abv) : (lim f*lim g) = lim (f*g) :=
  eq_lim_of_const_equiv$
    show lim_zero (const abv (lim f*lim g) - f*g) from
      have h : (const abv (lim f*lim g) - f*g) = ((const abv (lim f) - f)*g)+const abv (lim f)*const abv (lim g) - g :=
        by 
          simp [const_mul (lim f), mul_addₓ, add_mulₓ, sub_eq_add_neg, add_commₓ, add_left_commₓ]
      by 
        rw [h] <;>
          exact
            add_lim_zero (mul_lim_zero_left _ (Setoidₓ.symm (equiv_lim _)))
              (mul_lim_zero_right _ (Setoidₓ.symm (equiv_lim _)))

theorem lim_mul (f : CauSeq β abv) (x : β) : (lim f*x) = lim (f*const abv x) :=
  by 
    rw [←lim_mul_lim, lim_const]

theorem lim_neg (f : CauSeq β abv) : lim (-f) = -lim f :=
  lim_eq_of_equiv_const
    (show lim_zero (-f - const abv (-lim f))by 
      rw [const_neg, sub_neg_eq_add, add_commₓ, ←sub_eq_add_neg] <;> exact Setoidₓ.symm (equiv_lim f))

-- error in Data.Real.CauSeqCompletion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lim_eq_zero_iff (f : cau_seq β abv) : «expr ↔ »(«expr = »(lim f, 0), lim_zero f) :=
⟨assume
 h, by have [ident hf] [] [":=", expr equiv_lim f]; rw [expr h] ["at", ident hf]; exact [expr (lim_zero_congr hf).mpr (const_lim_zero.mpr rfl)], assume
 h, have h₁ : «expr = »(f, «expr - »(f, const abv 0)) := ext (λ
  n, by simp [] [] [] ["[", expr sub_apply, ",", expr const_apply, "]"] [] []),
 by rw [expr h₁] ["at", ident h]; exact [expr lim_eq_of_equiv_const h]⟩

end 

section 

variable {β : Type _} [Field β] {abv : β → α} [IsAbsoluteValue abv] [is_complete β abv]

theorem lim_inv {f : CauSeq β abv} (hf : ¬lim_zero f) : lim (inv f hf) = lim f⁻¹ :=
  have hl : lim f ≠ 0 :=
    by 
      rwa [←lim_eq_zero_iff] at hf 
  lim_eq_of_equiv_const$
    show lim_zero (inv f hf - const abv (lim f⁻¹)) from
      have h₁ : ∀ g f : CauSeq β abv hf : ¬lim_zero f, lim_zero (g - (f*inv f hf)*g) :=
        fun g f hf =>
          by 
            rw [←one_mulₓ g, ←mul_assocₓ, ←sub_mul, mul_oneₓ, mul_commₓ, mul_commₓ f] <;>
              exact mul_lim_zero_right _ (Setoidₓ.symm (CauSeq.inv_mul_cancel _))
      have h₂ : lim_zero (inv f hf - const abv (lim f⁻¹) - (const abv (lim f) - f)*inv f hf*const abv (lim f⁻¹)) :=
        by 
          rw [sub_mul, ←sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add] <;>
            exact
              show
                lim_zero
                  ((inv f hf - const abv (lim f)*inv f hf*const abv (lim f⁻¹)) -
                    (const abv (lim f⁻¹) - f*inv f hf*const abv (lim f⁻¹))) from
                sub_lim_zero
                  (by 
                    rw [←mul_assocₓ, mul_right_commₓ, const_inv hl] <;> exact h₁ _ _ _)
                  (by 
                    rw [←mul_assocₓ] <;> exact h₁ _ _ _)
      (lim_zero_congr h₂).mpr$ mul_lim_zero_left _ (Setoidₓ.symm (equiv_lim f))

end 

section 

variable [is_complete α abs]

theorem lim_le {f : CauSeq α abs} {x : α} (h : f ≤ CauSeq.const abs x) : lim f ≤ x :=
  CauSeq.const_le.1$ CauSeq.le_of_eq_of_le (Setoidₓ.symm (equiv_lim f)) h

theorem le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x ≤ f) : x ≤ lim f :=
  CauSeq.const_le.1$ CauSeq.le_of_le_of_eq h (equiv_lim f)

theorem lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < lim f :=
  CauSeq.const_lt.1$ CauSeq.lt_of_lt_of_eq h (equiv_lim f)

theorem lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : lim f < x :=
  CauSeq.const_lt.1$ CauSeq.lt_of_eq_of_lt (Setoidₓ.symm (equiv_lim f)) h

end 

end CauSeq

