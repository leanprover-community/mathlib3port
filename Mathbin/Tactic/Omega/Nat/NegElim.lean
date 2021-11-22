import Mathbin.Tactic.Omega.Nat.Form

namespace Omega

namespace Nat

open_locale Omega.Nat

/-- push_neg p returns the result of normalizing ¬ p by
    pushing the outermost negation all the way down,
    until it reaches either a negation or an atom -/
@[simp]
def push_neg : preform → preform
| p ∨* q => push_neg p ∧* push_neg q
| p ∧* q => push_neg p ∨* push_neg q
| ¬* p => p
| p => ¬* p

theorem push_neg_equiv : ∀ {p : preform}, preform.equiv (push_neg p) (¬* p) :=
  by 
    runTac 
      preform.induce sorry
    ·
      simp only [not_not, preform.holds, push_neg]
    ·
      simp only [preform.holds, push_neg, not_or_distrib, ihp v, ihq v]
    ·
      simp only [preform.holds, push_neg, not_and_distrib, ihp v, ihq v]

/-- NNF transformation -/
def nnf : preform → preform
| ¬* p => push_neg (nnf p)
| p ∨* q => nnf p ∨* nnf q
| p ∧* q => nnf p ∧* nnf q
| a => a

/-- Asserts that the given preform is in NNF -/
def is_nnf : preform → Prop
| t =* s => True
| t ≤* s => True
| ¬* t =* s => True
| ¬* t ≤* s => True
| p ∨* q => is_nnf p ∧ is_nnf q
| p ∧* q => is_nnf p ∧ is_nnf q
| _ => False

theorem is_nnf_push_neg : ∀ p : preform, is_nnf p → is_nnf (push_neg p) :=
  by 
    runTac 
      preform.induce sorry
    ·
      cases p <;>
        try 
            cases h1 <;>
          trivial
    ·
      cases h1 
      constructor <;>
          [·
            apply ihp,
          ·
            apply ihq] <;>
        assumption
    ·
      cases h1 
      constructor <;>
          [·
            apply ihp,
          ·
            apply ihq] <;>
        assumption

theorem is_nnf_nnf : ∀ p : preform, is_nnf (nnf p) :=
  by 
    runTac 
      preform.induce sorry
    ·
      apply is_nnf_push_neg _ ih
    ·
      constructor <;> assumption
    ·
      constructor <;> assumption

theorem nnf_equiv : ∀ {p : preform}, preform.equiv (nnf p) p :=
  by 
    runTac 
      preform.induce sorry
    ·
      rw [push_neg_equiv]
      apply not_iff_not_of_iff 
      apply ih
    ·
      apply pred_mono_2' (ihp v) (ihq v)
    ·
      apply pred_mono_2' (ihp v) (ihq v)

@[simp]
def neg_elim_core : preform → preform
| ¬* t =* s => (t.add_one ≤* s) ∨* s.add_one ≤* t
| ¬* t ≤* s => s.add_one ≤* t
| p ∨* q => neg_elim_core p ∨* neg_elim_core q
| p ∧* q => neg_elim_core p ∧* neg_elim_core q
| p => p

theorem neg_free_neg_elim_core : ∀ p, is_nnf p → (neg_elim_core p).NegFree :=
  by 
    runTac 
      preform.induce sorry
    ·
      cases p <;>
        try 
            cases h1 <;>
          try 
            trivial 
      constructor <;> trivial
    ·
      cases h1 
      constructor <;>
          [·
            apply ihp,
          ·
            apply ihq] <;>
        assumption
    ·
      cases h1 
      constructor <;>
          [·
            apply ihp,
          ·
            apply ihq] <;>
        assumption

theorem le_and_le_iff_eq {α : Type} [PartialOrderₓ α] {a b : α} : a ≤ b ∧ b ≤ a ↔ a = b :=
  by 
    constructor <;> intro h1
    ·
      cases h1 
      apply le_antisymmₓ <;> assumption
    ·
      constructor <;> apply le_of_eqₓ <;> rw [h1]

theorem implies_neg_elim_core : ∀ {p : preform}, preform.implies p (neg_elim_core p) :=
  by 
    runTac 
      preform.induce sorry
    ·
      cases' p with t s t s <;>
        try 
          apply h
      ·
        apply Or.symm 
        simpa only [preform.holds, le_and_le_iff_eq.symm, not_and_distrib, not_leₓ] using h 
      simpa only [preform.holds, not_leₓ, Int.add_one_le_iff] using h
    ·
      simp only [neg_elim_core]
      cases h <;>
          [·
            left 
            apply ihp,
          ·
            right 
            apply ihq] <;>
        assumption 
    apply And.imp (ihp _) (ihq _) h

/-- Eliminate all negations in a preform -/
def neg_elim : preform → preform :=
  neg_elim_core ∘ nnf

theorem neg_free_neg_elim {p : preform} : (neg_elim p).NegFree :=
  neg_free_neg_elim_core _ (is_nnf_nnf _)

theorem implies_neg_elim {p : preform} : preform.implies p (neg_elim p) :=
  by 
    intro v h1 
    apply implies_neg_elim_core 
    apply (nnf_equiv v).elim_right h1

end Nat

end Omega

