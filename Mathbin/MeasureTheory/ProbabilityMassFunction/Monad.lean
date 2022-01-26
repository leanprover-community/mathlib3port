import Mathbin.MeasureTheory.ProbabilityMassFunction.Basic

/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `pmf` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : pmf β` is the distribution given by sampling `a : α` from `pa : pmf α`,
and then sampling from `pb a : pmf β` to get a final result `b : β`.

`bind_on_support` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/


noncomputable section

variable {α β γ : Type _}

open_locale Classical BigOperators Nnreal Ennreal

namespace Pmf

section Pure

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : Pmf α :=
  ⟨fun a' => if a' = a then 1 else 0, has_sum_ite_eq _ _⟩

variable (a a' : α)

@[simp]
theorem pure_apply : pure a a' = if a' = a then 1 else 0 :=
  rfl

@[simp]
theorem support_pure : (pure a).Support = {a} :=
  Set.ext fun a' => by
    simp [mem_support_iff]

theorem mem_support_pure_iff : a' ∈ (pure a).Support ↔ a' = a := by
  simp

instance [Inhabited α] : Inhabited (Pmf α) :=
  ⟨pure default⟩

end Pure

section Bind

protected theorem bind.summable (p : Pmf α) (f : α → Pmf β) (b : β) : Summable fun a : α => p a * f a b := by
  refine' Nnreal.summable_of_le (fun a => _) p.summable_coe
  suffices p a * f a b ≤ p a * 1 by
    simpa
  exact mul_le_mul_of_nonneg_left ((f a).coe_le_one _) (p a).2

/-- The monadic bind operation for `pmf`. -/
def bind (p : Pmf α) (f : α → Pmf β) : Pmf β :=
  ⟨fun b => ∑' a, p a * f a b, by
    apply Ennreal.has_sum_coe.1
    simp only [Ennreal.coe_tsum (bind.summable p f _)]
    rw [ennreal.summable.has_sum_iff, Ennreal.tsum_comm]
    simp [Ennreal.tsum_mul_left, (Ennreal.coe_tsum (f _).summable_coe).symm, (Ennreal.coe_tsum p.summable_coe).symm]⟩

variable (p : Pmf α) (f : α → Pmf β)

@[simp]
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b :=
  rfl

@[simp]
theorem support_bind : (p.bind f).Support = { b | ∃ a ∈ p.support, b ∈ (f a).Support } :=
  Set.ext fun b => by
    simp [mem_support_iff, tsum_eq_zero_iff (bind.summable p f b), not_or_distrib]

theorem mem_support_bind_iff (b : β) : b ∈ (p.bind f).Support ↔ ∃ a ∈ p.support, b ∈ (f a).Support := by
  simp

theorem coe_bind_apply (p : Pmf α) (f : α → Pmf β) (b : β) : (p.bind f b : ℝ≥0∞) = ∑' a, p a * f a b :=
  Eq.trans (Ennreal.coe_tsum <| bind.summable p f b) <| by
    simp

@[simp]
theorem pure_bind (a : α) (f : α → Pmf β) : (pure a).bind f = f a := by
  have : ∀ b a', ite (a' = a) 1 0 * f a' b = ite (a' = a) (f a b) 0 := fun b a' => by
    split_ifs <;> simp <;> subst h <;> simp
  ext b <;> simp [this]

@[simp]
theorem bind_pureₓ (p : Pmf α) : p.bind pure = p := by
  have : ∀ a a', p a * ite (a' = a) 1 0 = ite (a = a') (p a') 0 := fun a a' => by
    split_ifs <;>
      try
          subst a <;>
        try
            subst a' <;>
          simp_all
  ext b <;> simp [this]

@[simp]
theorem bind_bind (p : Pmf α) (f : α → Pmf β) (g : β → Pmf γ) : (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  ext1 b
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm]
  rw [Ennreal.tsum_comm]
  simp [mul_assoc, mul_left_commₓ, mul_comm]

theorem bind_comm (p : Pmf α) (q : Pmf β) (f : α → β → Pmf γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b := by
  ext1 b
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm]
  rw [Ennreal.tsum_comm]
  simp [mul_assoc, mul_left_commₓ, mul_comm]

end Bind

instance : Monadₓ Pmf where
  pure := fun A a => pure a
  bind := fun A B pa pb => pa.bind pb

section BindOnSupport

protected theorem bind_on_support.summable (p : Pmf α) (f : ∀, ∀ a ∈ p.support, ∀, Pmf β) (b : β) :
    Summable fun a : α => p a * if h : p a = 0 then 0 else f a h b := by
  refine' Nnreal.summable_of_le (fun a => _) p.summable_coe
  split_ifs
  · refine' (mul_zero (p a)).symm ▸ le_of_eqₓ h.symm
    
  · suffices p a * f a h b ≤ p a * 1 by
      simpa
    exact mul_le_mul_of_nonneg_left ((f a h).coe_le_one _) (p a).2
    

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bind_on_support (λ a _, f a)`, see `bind_on_support_eq_bind` -/
def bind_on_support (p : Pmf α) (f : ∀, ∀ a ∈ p.support, ∀, Pmf β) : Pmf β :=
  ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b,
    Ennreal.has_sum_coe.1
      (by
        simp only [Ennreal.coe_tsum (bind_on_support.summable p f _)]
        rw [ennreal.summable.has_sum_iff, Ennreal.tsum_comm]
        simp only [Ennreal.coe_mul, Ennreal.coe_one, Ennreal.tsum_mul_left]
        have : (∑' a : α, (p a : Ennreal)) = 1 := by
          simp only [← Ennreal.coe_tsum p.summable_coe, Ennreal.coe_one, tsum_coe]
        refine' trans (tsum_congr fun a => _) this
        split_ifs with h
        · simp [h]
          
        · simp [← Ennreal.coe_tsum (f a h).summable_coe, (f a h).tsum_coe]
          )⟩

variable {p : Pmf α} (f : ∀, ∀ a ∈ p.support, ∀, Pmf β)

@[simp]
theorem bind_on_support_apply (b : β) : p.bind_on_support f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b :=
  rfl

@[simp]
theorem support_bind_on_support :
    (p.bind_on_support f).Support = { b | ∃ (a : α)(h : a ∈ p.support), b ∈ (f a h).Support } := by
  refine' Set.ext fun b => _
  simp only [tsum_eq_zero_iff (bind_on_support.summable p f b), not_or_distrib, mem_support_iff, bind_on_support_apply,
    Ne.def, not_forall, mul_eq_zero]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by
        simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a,
        ⟨ha, by
          simpa [(mem_support_iff _ a).1 ha] using ha'⟩⟩⟩

theorem mem_support_bind_on_support_iff (b : β) :
    b ∈ (p.bind_on_support f).Support ↔ ∃ (a : α)(h : a ∈ p.support), b ∈ (f a h).Support := by
  simp

/-- `bind_on_support` reduces to `bind` if `f` doesn't depend on the additional hypothesis -/
@[simp]
theorem bind_on_support_eq_bind (p : Pmf α) (f : α → Pmf β) : (p.bind_on_support fun a _ => f a) = p.bind f := by
  ext b
  simp only [bind_on_support_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, Nnreal.coe_eq, mul_ite, mul_zero]
  refine' congr_argₓ _ (funext fun a => _)
  split_ifs with h <;> simp [h]

theorem coe_bind_on_support_apply (b : β) :
    (p.bind_on_support f b : ℝ≥0∞) = ∑' a, p a * if h : p a = 0 then 0 else f a h b := by
  simp only [bind_on_support_apply, Ennreal.coe_tsum (bind_on_support.summable p f b), dite_cast, Ennreal.coe_mul,
    Ennreal.coe_zero]

theorem bind_on_support_eq_zero_iff (b : β) : p.bind_on_support f b = 0 ↔ ∀ a ha : p a ≠ 0, f a ha b = 0 := by
  simp only [bind_on_support_apply, tsum_eq_zero_iff (bind_on_support.summable p f b), mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => trans (dif_neg ha).symm (h a ha), fun h a ha => trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem pure_bind_on_support (a : α) (f : ∀ a' : α ha : a' ∈ (pure a).Support, Pmf β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) := by
  refine' Pmf.ext fun b => _
  simp only [Nnreal.coe_eq, bind_on_support_apply, pure_apply]
  refine' trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases' h : a' = a <;> simp [h]

theorem bind_on_support_pure (p : Pmf α) : (p.bind_on_support fun a _ => pure a) = p := by
  simp only [Pmf.bind_pure, Pmf.bind_on_support_eq_bind]

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:57:31: expecting tactic arg
@[simp]
theorem bind_on_support_bind_on_support (p : Pmf α) (f : ∀, ∀ a ∈ p.support, ∀, Pmf β)
    (g : ∀, ∀ b ∈ (p.bind_on_support f).Support, ∀, Pmf γ) :
    (p.bind_on_support f).bindOnSupport g =
      p.bind_on_support fun a ha =>
        (f a ha).bindOnSupport fun b hb => g b ((mem_support_bind_on_support_iff f b).mpr ⟨a, ha, hb⟩) :=
  by
  refine' Pmf.ext fun a => _
  simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ← tsum_dite_right, ennreal.tsum_mul_left.symm,
    ennreal.tsum_mul_right.symm]
  simp only [Ennreal.tsum_eq_zero, Ennreal.coe_eq_coe, Ennreal.coe_eq_zero, Ennreal.coe_zero, dite_eq_left_iff,
    mul_eq_zero]
  refine' ennreal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  split_ifs
  any_goals {
  }
  · have := h_1 a'
    simp [h] at this
    contradiction
    
  · simp [h_2]
    

theorem bind_on_support_comm (p : Pmf α) (q : Pmf β) (f : ∀, ∀ a ∈ p.support, ∀, ∀ b ∈ q.support, ∀, Pmf γ) :
    (p.bind_on_support fun a ha => q.bind_on_support (f a ha)) =
      q.bind_on_support fun b hb => p.bind_on_support fun a ha => f a ha b hb :=
  by
  apply Pmf.ext
  rintro c
  simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ← tsum_dite_right, ennreal.tsum_mul_left.symm,
    ennreal.tsum_mul_right.symm]
  refine' trans Ennreal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
  split_ifs with h1 h2 h2 <;> ring

end BindOnSupport

end Pmf

