/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.real.cau_seq
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Algebra.Order.Group.MinMax
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Algebra.Ring.Pi
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.

There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `is_cau_seq`: a predicate that says `f : ℕ → β` is Cauchy.
* `cau_seq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/


open IsAbsoluteValue

variable {G α β : Type _}

theorem exists_forall_ge_and {α} [LinearOrder α] {P Q : α → Prop} :
    (∃ i, ∀ j ≥ i, P j) → (∃ i, ∀ j ≥ i, Q j) → ∃ i, ∀ j ≥ i, P j ∧ Q j
  | ⟨a, h₁⟩, ⟨b, h₂⟩ =>
    let ⟨c, ac, bc⟩ := exists_ge_of_linear a b
    ⟨c, fun j hj => ⟨h₁ _ (le_trans ac hj), h₂ _ (le_trans bc hj)⟩⟩
#align exists_forall_ge_and exists_forall_ge_and

section

variable [LinearOrderedField α] [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    ∃ δ > 0,
      ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
  ⟨ε / 2, half_pos ε0, fun a₁ a₂ b₁ b₂ h₁ h₂ => by
    simpa [add_halves, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      lt_of_le_of_lt (abv_add abv _ _) (add_lt_add h₁ h₂)⟩
#align rat_add_continuous_lemma rat_add_continuous_lemma

theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    ∃ δ > 0,
      ∀ {a₁ a₂ b₁ b₂ : β},
        abv a₁ < K₁ →
          abv b₂ < K₂ → abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε :=
  by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have εK := div_pos (half_pos ε0) K0
  refine' ⟨_, εK, fun a₁ a₂ b₁ b₂ ha₁ hb₂ h₁ h₂ => _⟩
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  replace hb₂ := lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _))
  have :=
    add_lt_add (mul_lt_mul' (le_of_lt h₁) hb₂ (abv_nonneg abv _) εK)
      (mul_lt_mul' (le_of_lt h₂) ha₁ (abv_nonneg abv _) εK)
  rw [← abv_mul abv, mul_comm, div_mul_cancel _ (ne_of_gt K0), ← abv_mul abv, add_halves] at this
  simpa [mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm] using
    lt_of_le_of_lt (abv_add abv _ _) this
#align rat_mul_continuous_lemma rat_mul_continuous_lemma

theorem rat_inv_continuous_lemma {β : Type _} [DivisionRing β] (abv : β → α) [IsAbsoluteValue abv]
    {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
    ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε :=
  by
  refine' ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun a b ha hb h => _⟩
  have a0 := K0.trans_le ha
  have b0 := K0.trans_le hb
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), abv_mul abv, abv_mul abv, abv_inv abv,
    abv_inv abv, abv_sub abv]
  refine' lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_right _ b0.le) a0.le
  rw [mul_assoc, inv_mul_cancel_right₀ b0.ne', ← mul_assoc, mul_inv_cancel a0.ne', one_mul]
  refine' h.trans_le _
  exact mul_le_mul (mul_le_mul ha le_rfl ε0.le a0.le) hb K0.le (mul_nonneg a0.le ε0.le)
#align rat_inv_continuous_lemma rat_inv_continuous_lemma

end

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
def IsCauSeq {α : Type _} [LinearOrderedField α] {β : Type _} [Ring β] (abv : β → α) (f : ℕ → β) :
    Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε
#align is_cau_seq IsCauSeq

namespace IsCauSeq

variable [LinearOrderedField α] [Ring β] {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j k «expr ≥ » i) -/
-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ (j) (_ : j ≥ i) (k) (_ : k ≥ i), abv (f j - f k) < ε :=
  by
  refine' (hf _ (half_pos ε0)).imp fun i hi j ij k ik => _
  rw [← add_halves ε]
  refine' lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) _)
  rw [abv_sub abv]; exact hi _ ik
#align is_cau_seq.cauchy₂ IsCauSeq.cauchy₂

theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun j ij k jk => H _ (le_trans ij jk) _ ij⟩
#align is_cau_seq.cauchy₃ IsCauSeq.cauchy₃

theorem add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g) := fun ε ε0 =>
  let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (H₁ _ ij) (H₂ _ ij)⟩
#align is_cau_seq.add IsCauSeq.add

end IsCauSeq

/-- `cau_seq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def CauSeq {α : Type _} [LinearOrderedField α] (β : Type _) [Ring β] (abv : β → α) : Type _ :=
  { f : ℕ → β // IsCauSeq abv f }
#align cau_seq CauSeq

namespace CauSeq

variable [LinearOrderedField α]

section Ring

variable [Ring β] {abv : β → α}

instance : CoeFun (CauSeq β abv) fun _ => ℕ → β :=
  ⟨Subtype.val⟩

@[simp]
theorem mk_to_fun (f) (hf : IsCauSeq abv f) : @coeFn (CauSeq β abv) _ _ ⟨f, hf⟩ = f :=
  rfl
#align cau_seq.mk_to_fun CauSeq.mk_to_fun

theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g :=
  Subtype.eq (funext h)
#align cau_seq.ext CauSeq.ext

theorem is_cau (f : CauSeq β abv) : IsCauSeq abv f :=
  f.2
#align cau_seq.is_cau CauSeq.is_cau

theorem cauchy (f : CauSeq β abv) : ∀ {ε}, 0 < ε → ∃ i, ∀ j ≥ i, abv (f j - f i) < ε :=
  f.2
#align cau_seq.cauchy CauSeq.cauchy

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def ofEq (f : CauSeq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : CauSeq β abv :=
  ⟨g, fun ε => by rw [show g = f from (funext e).symm] <;> exact f.cauchy⟩
#align cau_seq.of_eq CauSeq.ofEq

variable [IsAbsoluteValue abv]

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j k «expr ≥ » i) -/
-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem cauchy₂ (f : CauSeq β abv) {ε} :
    0 < ε → ∃ i, ∀ (j) (_ : j ≥ i) (k) (_ : k ≥ i), abv (f j - f k) < ε :=
  f.2.cauchy₂
#align cau_seq.cauchy₂ CauSeq.cauchy₂

theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  f.2.cauchy₃
#align cau_seq.cauchy₃ CauSeq.cauchy₃

theorem bounded (f : CauSeq β abv) : ∃ r, ∀ i, abv (f i) < r :=
  by
  cases' f.cauchy zero_lt_one with i h
  set R : ℕ → α := @Nat.rec (fun n => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : ∀ i, ∀ j ≤ i, abv (f j) ≤ R i :=
    by
    refine' Nat.rec (by simp [hR]) _
    rintro i hi j (rfl | hj)
    · simp
    exact (hi j hj).trans (le_max_left _ _)
  refine' ⟨R i + 1, fun j => _⟩
  cases' lt_or_le j i with ij ij
  · exact lt_of_le_of_lt (this i _ (le_of_lt ij)) (lt_add_one _)
  · have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ ij))
    rw [add_sub, add_comm] at this
    simpa
#align cau_seq.bounded CauSeq.bounded

theorem bounded' (f : CauSeq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
  let ⟨r, h⟩ := f.Bounded
  ⟨max r (x + 1), lt_of_lt_of_le (lt_add_one _) (le_max_right _ _), fun i =>
    lt_of_lt_of_le (h i) (le_max_left _ _)⟩
#align cau_seq.bounded' CauSeq.bounded'

instance : Add (CauSeq β abv) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp, norm_cast]
theorem coe_add (f g : CauSeq β abv) : ⇑(f + g) = f + g :=
  rfl
#align cau_seq.coe_add CauSeq.coe_add

@[simp, norm_cast]
theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
  rfl
#align cau_seq.add_apply CauSeq.add_apply

variable (abv)

/-- The constant Cauchy sequence. -/
def const (x : β) : CauSeq β abv :=
  ⟨fun i => x, fun ε ε0 => ⟨0, fun j ij => by simpa [abv_zero abv] using ε0⟩⟩
#align cau_seq.const CauSeq.const

variable {abv}

-- mathport name: exprconst
local notation "const" => const abv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (Std.Tactic.NormCast.Attr.norm_cast "norm_cast" [] []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_const [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Init.Coe.«term⇑_» "⇑" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]))
         "="
         (Term.app `Function.const [(Term.hole "_") `x]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Init.Coe.«term⇑_» "⇑" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]))
       "="
       (Term.app `Function.const [(Term.hole "_") `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Function.const [(Term.hole "_") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Function.const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term⇑_» "⇑" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , norm_cast ] theorem coe_const ( x : β ) : ⇑ const x = Function.const _ x := rfl
#align cau_seq.coe_const CauSeq.coe_const

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (Std.Tactic.NormCast.Attr.norm_cast "norm_cast" [] []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `β] [] ")")
        (Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.typeAscription
           "("
           (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
           ":"
           [(Term.arrow (termℕ "ℕ") "→" `β)]
           ")")
          [`i])
         "="
         `x)))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.typeAscription
         "("
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
         ":"
         [(Term.arrow (termℕ "ℕ") "→" `β)]
         ")")
        [`i])
       "="
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.typeAscription
        "("
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
        ":"
        [(Term.arrow (termℕ "ℕ") "→" `β)]
        ")")
       [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription
       "("
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
       ":"
       [(Term.arrow (termℕ "ℕ") "→" `β)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℕ "ℕ") "→" `β)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `β
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , norm_cast ] theorem const_apply ( x : β ) ( i : ℕ ) : ( const x : ℕ → β ) i = x := rfl
#align cau_seq.const_apply CauSeq.const_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_inj [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `y] [":" `β] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.typeAscription
           "("
           (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
           ":"
           [(Term.app `CauSeq [`β `abv])]
           ")")
          "="
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
         "↔"
         («term_=_» `x "=" `y))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.app
            `congr_arg
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f]
               [(Term.typeSpec ":" (Term.app `CauSeq [`β `abv]))]
               "=>"
               (Term.app
                (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")")
                [(num "0")])))
             `h])))
         ","
         (Term.app `congr_arg [(Term.hole "_")])]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.app
           `congr_arg
           [(Term.fun
             "fun"
             (Term.basicFun
              [`f]
              [(Term.typeSpec ":" (Term.app `CauSeq [`β `abv]))]
              "=>"
              (Term.app
               (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")")
               [(num "0")])))
            `h])))
        ","
        (Term.app `congr_arg [(Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_arg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.app
         `congr_arg
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f]
            [(Term.typeSpec ":" (Term.app `CauSeq [`β `abv]))]
            "=>"
            (Term.app
             (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")")
             [(num "0")])))
          `h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          [(Term.typeSpec ":" (Term.app `CauSeq [`β `abv]))]
          "=>"
          (Term.app
           (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")")
           [(num "0")])))
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        [(Term.typeSpec ":" (Term.app `CauSeq [`β `abv]))]
        "=>"
        (Term.app
         (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")")
         [(num "0")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")") [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℕ "ℕ") "→" `β)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `β
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CauSeq [`β `abv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CauSeq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`f]
       [(Term.typeSpec ":" (Term.app `CauSeq [`β `abv]))]
       "=>"
       (Term.app
        (Term.typeAscription "(" `f ":" [(Term.arrow (termℕ "ℕ") "→" `β)] ")")
        [(num "0")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
         ":"
         [(Term.app `CauSeq [`β `abv])]
         ")")
        "="
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
       "↔"
       («term_=_» `x "=" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
        ":"
        [(Term.app `CauSeq [`β `abv])]
        ")")
       "="
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  const_inj
  { x y : β } : ( const x : CauSeq β abv ) = const y ↔ x = y
  := ⟨ fun h => congr_arg fun f : CauSeq β abv => ( f : ℕ → β ) 0 h , congr_arg _ ⟩
#align cau_seq.const_inj CauSeq.const_inj

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `Zero [(Term.app `CauSeq [`β `abv])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "0")])]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "0")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Zero CauSeq β abv := ⟨ const 0 ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `One [(Term.app `CauSeq [`β `abv])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "1")])]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "1")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : One CauSeq β abv := ⟨ const 1 ⟩

instance : Inhabited (CauSeq β abv) :=
  ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : CauSeq β abv) = 0 :=
  rfl
#align cau_seq.coe_zero CauSeq.coe_zero

@[simp, norm_cast]
theorem coe_one : ⇑(1 : CauSeq β abv) = 1 :=
  rfl
#align cau_seq.coe_one CauSeq.coe_one

@[simp, norm_cast]
theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
  rfl
#align cau_seq.zero_apply CauSeq.zero_apply

@[simp, norm_cast]
theorem one_apply (i) : (1 : CauSeq β abv) i = 1 :=
  rfl
#align cau_seq.one_apply CauSeq.one_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_zero [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "0")])
         "="
         (num "0"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "0")]) "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem const_zero : const 0 = 0 := rfl
#align cau_seq.const_zero CauSeq.const_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_one [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "1")])
         "="
         (num "1"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "1")]) "=" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem const_one : const 1 = 1 := rfl
#align cau_seq.const_one CauSeq.const_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_+_» `x "+" `y)])
         "="
         («term_+_»
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
          "+"
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_+_» `x "+" `y)])
       "="
       («term_+_»
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
        "+"
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
       "+"
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem const_add ( x y : β ) : const x + y = const x + const y := rfl
#align cau_seq.const_add CauSeq.const_add

instance : Mul (CauSeq β abv) :=
  ⟨fun f g =>
    ⟨f * g, fun ε ε0 =>
      let ⟨F, F0, hF⟩ := f.bounded' 0
      let ⟨G, G0, hG⟩ := g.bounded' 0
      let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
      let ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0)
      ⟨i, fun j ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp, norm_cast]
theorem coe_mul (f g : CauSeq β abv) : ⇑(f * g) = f * g :=
  rfl
#align cau_seq.coe_mul CauSeq.coe_mul

@[simp, norm_cast]
theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i :=
  rfl
#align cau_seq.mul_apply CauSeq.mul_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_*_» `x "*" `y)])
         "="
         («term_*_»
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
          "*"
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_*_» `x "*" `y)])
       "="
       («term_*_»
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
        "*"
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
       "*"
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem const_mul ( x y : β ) : const x * y = const x * const y := rfl
#align cau_seq.const_mul CauSeq.const_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `Neg [(Term.app `CauSeq [`β `abv])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (Term.app
            `ofEq
            [(«term_*_»
              (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" (num "1"))])
              "*"
              `f)
             (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term-_» "-" (Term.app `f [`x]))))
             (Term.fun
              "fun"
              (Term.basicFun
               [`i]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
          (Term.app
           `ofEq
           [(«term_*_»
             (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" (num "1"))])
             "*"
             `f)
            (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term-_» "-" (Term.app `f [`x]))))
            (Term.fun
             "fun"
             (Term.basicFun
              [`i]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (Term.app
         `ofEq
         [(«term_*_»
           (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" (num "1"))])
           "*"
           `f)
          (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term-_» "-" (Term.app `f [`x]))))
          (Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ofEq
       [(«term_*_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" (num "1"))])
         "*"
         `f)
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term-_» "-" (Term.app `f [`x]))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term-_» "-" (Term.app `f [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term-_» "-" (Term.app `f [`x]))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" (num "1"))])
       "*"
       `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Neg CauSeq β abv := ⟨ fun f => ofEq const - 1 * f fun x => - f x fun i => by simp ⟩

@[simp, norm_cast]
theorem coe_neg (f : CauSeq β abv) : ⇑(-f) = -f :=
  rfl
#align cau_seq.coe_neg CauSeq.coe_neg

@[simp, norm_cast]
theorem neg_apply (f : CauSeq β abv) (i) : (-f) i = -f i :=
  rfl
#align cau_seq.neg_apply CauSeq.neg_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_neg [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" `x)])
         "="
         («term-_» "-" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term-_» "-" `x)])
       "="
       («term-_» "-" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem const_neg ( x : β ) : const - x = - const x := rfl
#align cau_seq.const_neg CauSeq.const_neg

instance : Sub (CauSeq β abv) :=
  ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩

@[simp, norm_cast]
theorem coe_sub (f g : CauSeq β abv) : ⇑(f - g) = f - g :=
  rfl
#align cau_seq.coe_sub CauSeq.coe_sub

@[simp, norm_cast]
theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
  rfl
#align cau_seq.sub_apply CauSeq.sub_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_sub [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_-_» `x "-" `y)])
         "="
         («term_-_»
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
          "-"
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_-_» `x "-" `y)])
       "="
       («term_-_»
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
        "-"
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
       "-"
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem const_sub ( x y : β ) : const x - y = const x - const y := rfl
#align cau_seq.const_sub CauSeq.const_sub

section HasSmul

variable [HasSmul G β] [IsScalarTower G β β]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `HasSmul [`G (Term.app `CauSeq [`β `abv])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a `f]
           []
           "=>"
           (Term.app
            (Term.app
             `ofEq
             [(«term_*_»
               (Term.app
                (CauSeq.Data.Real.CauSeq.termconst "const")
                [(Algebra.Group.Defs.«term_•_» `a " • " (num "1"))])
               "*"
               `f)
              (Algebra.Group.Defs.«term_•_» `a " • " `f)])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`i]
               []
               "=>"
               (Term.app `smul_one_mul [(Term.hole "_") (Term.hole "_")])))])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `f]
          []
          "=>"
          (Term.app
           (Term.app
            `ofEq
            [(«term_*_»
              (Term.app
               (CauSeq.Data.Real.CauSeq.termconst "const")
               [(Algebra.Group.Defs.«term_•_» `a " • " (num "1"))])
              "*"
              `f)
             (Algebra.Group.Defs.«term_•_» `a " • " `f)])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`i]
              []
              "=>"
              (Term.app `smul_one_mul [(Term.hole "_") (Term.hole "_")])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `f]
        []
        "=>"
        (Term.app
         (Term.app
          `ofEq
          [(«term_*_»
            (Term.app
             (CauSeq.Data.Real.CauSeq.termconst "const")
             [(Algebra.Group.Defs.«term_•_» `a " • " (num "1"))])
            "*"
            `f)
           (Algebra.Group.Defs.«term_•_» `a " • " `f)])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Term.app `smul_one_mul [(Term.hole "_") (Term.hole "_")])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app
        `ofEq
        [(«term_*_»
          (Term.app
           (CauSeq.Data.Real.CauSeq.termconst "const")
           [(Algebra.Group.Defs.«term_•_» `a " • " (num "1"))])
          "*"
          `f)
         (Algebra.Group.Defs.«term_•_» `a " • " `f)])
       [(Term.fun
         "fun"
         (Term.basicFun [`i] [] "=>" (Term.app `smul_one_mul [(Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`i] [] "=>" (Term.app `smul_one_mul [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_one_mul [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_one_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       `ofEq
       [(«term_*_»
         (Term.app
          (CauSeq.Data.Real.CauSeq.termconst "const")
          [(Algebra.Group.Defs.«term_•_» `a " • " (num "1"))])
         "*"
         `f)
        (Algebra.Group.Defs.«term_•_» `a " • " `f)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `a " • " `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `a " • " `f)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_»
       (Term.app
        (CauSeq.Data.Real.CauSeq.termconst "const")
        [(Algebra.Group.Defs.«term_•_» `a " • " (num "1"))])
       "*"
       `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       (CauSeq.Data.Real.CauSeq.termconst "const")
       [(Algebra.Group.Defs.«term_•_» `a " • " (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `a " • " (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `a " • " (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : HasSmul G CauSeq β abv
  := ⟨ fun a f => ofEq const a • 1 * f a • f fun i => smul_one_mul _ _ ⟩

@[simp, norm_cast]
theorem coe_smul (a : G) (f : CauSeq β abv) : ⇑(a • f) = a • f :=
  rfl
#align cau_seq.coe_smul CauSeq.coe_smul

@[simp, norm_cast]
theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i :=
  rfl
#align cau_seq.smul_apply CauSeq.smul_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_smul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `G] [] ")")
        (Term.explicitBinder "(" [`x] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CauSeq.Data.Real.CauSeq.termconst "const")
          [(Algebra.Group.Defs.«term_•_» `a " • " `x)])
         "="
         (Algebra.Group.Defs.«term_•_»
          `a
          " • "
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (CauSeq.Data.Real.CauSeq.termconst "const")
        [(Algebra.Group.Defs.«term_•_» `a " • " `x)])
       "="
       (Algebra.Group.Defs.«term_•_»
        `a
        " • "
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `a
       " • "
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem const_smul ( a : G ) ( x : β ) : const a • x = a • const x := rfl
#align cau_seq.const_smul CauSeq.const_smul

instance : IsScalarTower G (CauSeq β abv) (CauSeq β abv) :=
  ⟨fun a f g => Subtype.ext <| smul_assoc a (⇑f) ⇑g⟩

end HasSmul

instance : AddGroup (CauSeq β abv) :=
  Function.Injective.addGroup _ Subtype.coe_injective rfl coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec ":" (Term.app `AddGroupWithOne [(Term.app `CauSeq [`β `abv])])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`CauSeq.addGroup] "with"]
        [(Term.structInstField (Term.structInstLVal `one []) ":=" (num "1"))
         []
         (Term.structInstField
          (Term.structInstLVal `natCast [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`n]))))
         []
         (Term.structInstField
          (Term.structInstLVal `nat_cast_zero [])
          ":="
          (Term.app `congr_arg [(CauSeq.Data.Real.CauSeq.termconst "const") `Nat.cast_zero]))
         []
         (Term.structInstField
          (Term.structInstLVal `nat_cast_succ [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            (Term.app
             `congr_arg
             [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Nat.cast_succ [`n])]))))
         []
         (Term.structInstField
          (Term.structInstLVal `intCast [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`n]))))
         []
         (Term.structInstField
          (Term.structInstLVal `int_cast_of_nat [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            (Term.app
             `congr_arg
             [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Int.cast_of_nat [`n])]))))
         []
         (Term.structInstField
          (Term.structInstLVal `int_cast_neg_succ_of_nat [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            (Term.app
             `congr_arg
             [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Int.cast_negSucc [`n])]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`CauSeq.addGroup] "with"]
       [(Term.structInstField (Term.structInstLVal `one []) ":=" (num "1"))
        []
        (Term.structInstField
         (Term.structInstLVal `natCast [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun [`n] [] "=>" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`n]))))
        []
        (Term.structInstField
         (Term.structInstLVal `nat_cast_zero [])
         ":="
         (Term.app `congr_arg [(CauSeq.Data.Real.CauSeq.termconst "const") `Nat.cast_zero]))
        []
        (Term.structInstField
         (Term.structInstLVal `nat_cast_succ [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.app
            `congr_arg
            [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Nat.cast_succ [`n])]))))
        []
        (Term.structInstField
         (Term.structInstLVal `intCast [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun [`n] [] "=>" (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`n]))))
        []
        (Term.structInstField
         (Term.structInstLVal `int_cast_of_nat [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.app
            `congr_arg
            [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Int.cast_of_nat [`n])]))))
        []
        (Term.structInstField
         (Term.structInstLVal `int_cast_neg_succ_of_nat [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.app
            `congr_arg
            [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Int.cast_negSucc [`n])]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.app
         `congr_arg
         [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Int.cast_negSucc [`n])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(CauSeq.Data.Real.CauSeq.termconst "const") (Term.app `Int.cast_negSucc [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.cast_negSucc [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.cast_negSucc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Int.cast_negSucc [`n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : AddGroupWithOne CauSeq β abv
  :=
    {
      CauSeq.addGroup with
      one := 1
        natCast := fun n => const n
        nat_cast_zero := congr_arg const Nat.cast_zero
        nat_cast_succ := fun n => congr_arg const Nat.cast_succ n
        intCast := fun n => const n
        int_cast_of_nat := fun n => congr_arg const Int.cast_of_nat n
        int_cast_neg_succ_of_nat := fun n => congr_arg const Int.cast_negSucc n
      }

instance : Pow (CauSeq β abv) ℕ :=
  ⟨fun f n =>
    (ofEq (npowRec n f) fun i => f i ^ n) <| by induction n <;> simp [*, npowRec, pow_succ]⟩

@[simp, norm_cast]
theorem coe_pow (f : CauSeq β abv) (n : ℕ) : ⇑(f ^ n) = f ^ n :=
  rfl
#align cau_seq.coe_pow CauSeq.coe_pow

@[simp, norm_cast]
theorem pow_apply (f : CauSeq β abv) (n i : ℕ) : (f ^ n) i = f i ^ n :=
  rfl
#align cau_seq.pow_apply CauSeq.pow_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_pow [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `β] [] ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_^_» `x "^" `n)])
         "="
         («term_^_» (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]) "^" `n))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [(«term_^_» `x "^" `n)])
       "="
       («term_^_» (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]) "^" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x]) "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem const_pow ( x : β ) ( n : ℕ ) : const x ^ n = const x ^ n := rfl
#align cau_seq.const_pow CauSeq.const_pow

instance : Ring (CauSeq β abv) :=
  Function.Injective.ring _ Subtype.coe_injective rfl rfl coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_smul _ _) (fun _ _ => coe_smul _ _) coe_pow (fun _ => rfl) fun _ => rfl

instance {β : Type _} [CommRing β] {abv : β → α} [IsAbsoluteValue abv] : CommRing (CauSeq β abv) :=
  { CauSeq.ring with mul_comm := by intros <;> apply ext <;> simp [mul_left_comm, mul_comm] }

/-- `lim_zero f` holds when `f` approaches 0. -/
def LimZero {abv : β → α} (f : CauSeq β abv) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j) < ε
#align cau_seq.lim_zero CauSeq.LimZero

theorem add_lim_zero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f + g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ <| half_pos ε0) (hg _ <| half_pos ε0)).imp fun i H j ij =>
      by
      let ⟨H₁, H₂⟩ := H _ ij
      simpa [add_halves ε] using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add H₁ H₂)
#align cau_seq.add_lim_zero CauSeq.add_lim_zero

theorem mul_lim_zero_right (f : CauSeq β abv) {g} (hg : LimZero g) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨F, F0, hF⟩ := f.bounded' 0
    (hg _ <| div_pos ε0 F0).imp fun i H j ij => by
      have := mul_lt_mul' (le_of_lt <| hF j) (H _ ij) (abv_nonneg abv _) F0 <;>
        rwa [mul_comm F, div_mul_cancel _ (ne_of_gt F0), ← abv_mul abv] at this
#align cau_seq.mul_lim_zero_right CauSeq.mul_lim_zero_right

theorem mul_lim_zero_left {f} (g : CauSeq β abv) (hg : LimZero f) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨G, G0, hG⟩ := g.bounded' 0
    (hg _ <| div_pos ε0 G0).imp fun i H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _) <;>
        rwa [div_mul_cancel _ (ne_of_gt G0), ← abv_mul abv] at this
#align cau_seq.mul_lim_zero_left CauSeq.mul_lim_zero_left

theorem neg_lim_zero {f : CauSeq β abv} (hf : LimZero f) : LimZero (-f) := by
  rw [← neg_one_mul] <;> exact mul_lim_zero_right _ hf
#align cau_seq.neg_lim_zero CauSeq.neg_lim_zero

theorem sub_lim_zero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f - g) := by
  simpa only [sub_eq_add_neg] using add_lim_zero hf (neg_lim_zero hg)
#align cau_seq.sub_lim_zero CauSeq.sub_lim_zero

theorem lim_zero_sub_rev {f g : CauSeq β abv} (hfg : LimZero (f - g)) : LimZero (g - f) := by
  simpa using neg_lim_zero hfg
#align cau_seq.lim_zero_sub_rev CauSeq.lim_zero_sub_rev

theorem zero_lim_zero : LimZero (0 : CauSeq β abv)
  | ε, ε0 => ⟨0, fun j ij => by simpa [abv_zero abv] using ε0⟩
#align cau_seq.zero_lim_zero CauSeq.zero_lim_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_lim_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `β] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app `LimZero [(Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])])
         "↔"
         («term_=_» `x "=" (num "0")))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`H]
           []
           "=>"
           («term_<|_»
            (Term.proj (Term.app `abv_eq_zero [`abv]) "." (fieldIdx "1"))
            "<|"
            (Term.app
             (Term.app
              `eq_of_le_of_forall_le_of_dense
              [(Term.app `abv_nonneg [`abv (Term.hole "_")])])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`ε `ε0]
                []
                "=>"
                (Term.let
                 "let"
                 (Term.letDecl
                  (Term.letPatDecl
                   (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
                   []
                   []
                   ":="
                   (Term.app `H [(Term.hole "_") `ε0])))
                 []
                 («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl])))))]))))
         ","
         (Term.fun
          "fun"
          (Term.basicFun [`e] [] "=>" (Term.subst (Term.proj `e "." `symm) "▸" [`zero_lim_zero])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`H]
          []
          "=>"
          («term_<|_»
           (Term.proj (Term.app `abv_eq_zero [`abv]) "." (fieldIdx "1"))
           "<|"
           (Term.app
            (Term.app
             `eq_of_le_of_forall_le_of_dense
             [(Term.app `abv_nonneg [`abv (Term.hole "_")])])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`ε `ε0]
               []
               "=>"
               (Term.let
                "let"
                (Term.letDecl
                 (Term.letPatDecl
                  (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
                  []
                  []
                  ":="
                  (Term.app `H [(Term.hole "_") `ε0])))
                []
                («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl])))))]))))
        ","
        (Term.fun
         "fun"
         (Term.basicFun [`e] [] "=>" (Term.subst (Term.proj `e "." `symm) "▸" [`zero_lim_zero])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`e] [] "=>" (Term.subst (Term.proj `e "." `symm) "▸" [`zero_lim_zero])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst (Term.proj `e "." `symm) "▸" [`zero_lim_zero])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_lim_zero
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj `e "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`H]
        []
        "=>"
        («term_<|_»
         (Term.proj (Term.app `abv_eq_zero [`abv]) "." (fieldIdx "1"))
         "<|"
         (Term.app
          (Term.app `eq_of_le_of_forall_le_of_dense [(Term.app `abv_nonneg [`abv (Term.hole "_")])])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`ε `ε0]
             []
             "=>"
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
                []
                []
                ":="
                (Term.app `H [(Term.hole "_") `ε0])))
              []
              («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl])))))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj (Term.app `abv_eq_zero [`abv]) "." (fieldIdx "1"))
       "<|"
       (Term.app
        (Term.app `eq_of_le_of_forall_le_of_dense [(Term.app `abv_nonneg [`abv (Term.hole "_")])])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`ε `ε0]
           []
           "=>"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
              []
              []
              ":="
              (Term.app `H [(Term.hole "_") `ε0])))
            []
            («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `eq_of_le_of_forall_le_of_dense [(Term.app `abv_nonneg [`abv (Term.hole "_")])])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`ε `ε0]
          []
          "=>"
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
             []
             []
             ":="
             (Term.app `H [(Term.hole "_") `ε0])))
           []
           («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`ε `ε0]
        []
        "=>"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
           []
           []
           ":="
           (Term.app `H [(Term.hole "_") `ε0])))
         []
         («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
         []
         []
         ":="
         (Term.app `H [(Term.hole "_") `ε0])))
       []
       («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `le_of_lt "<|" (Term.app `hi [(Term.hole "_") `le_rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hi [(Term.hole "_") `le_rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [(Term.hole "_") `ε0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," `hi] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `eq_of_le_of_forall_le_of_dense [(Term.app `abv_nonneg [`abv (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abv_nonneg [`abv (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `abv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abv_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `abv_nonneg [`abv (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_of_le_of_forall_le_of_dense
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `eq_of_le_of_forall_le_of_dense
      [(Term.paren "(" (Term.app `abv_nonneg [`abv (Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.app `abv_eq_zero [`abv]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `abv_eq_zero [`abv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abv_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `abv_eq_zero [`abv]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Term.app `LimZero [(Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])])
       "↔"
       («term_=_» `x "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `LimZero [(Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  const_lim_zero
  { x : β } : LimZero const x ↔ x = 0
  :=
    ⟨
      fun
          H
            =>
            abv_eq_zero abv . 1
              <|
              eq_of_le_of_forall_le_of_dense abv_nonneg abv _
                fun ε ε0 => let ⟨ i , hi ⟩ := H _ ε0 le_of_lt <| hi _ le_rfl
        ,
        fun e => e . symm ▸ zero_lim_zero
      ⟩
#align cau_seq.const_lim_zero CauSeq.const_lim_zero

instance equiv : Setoid (CauSeq β abv) :=
  ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_lim_zero], fun f g h => by simpa using neg_lim_zero h,
      fun f g h fg gh => by simpa [sub_eq_add_neg, add_assoc] using add_lim_zero fg gh⟩⟩
#align cau_seq.equiv CauSeq.equiv

theorem add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 + g1 ≈ f2 + g2 := by simpa only [← add_sub_add_comm] using add_lim_zero hf hg
#align cau_seq.add_equiv_add CauSeq.add_equiv_add

theorem neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : -f ≈ -g := by
  simpa only [neg_sub'] using neg_lim_zero hf
#align cau_seq.neg_equiv_neg CauSeq.neg_equiv_neg

theorem sub_equiv_sub {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 - g1 ≈ f2 - g2 := by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)
#align cau_seq.sub_equiv_sub CauSeq.sub_equiv_sub

theorem equiv_def₃ {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - g j) < ε :=
  (exists_forall_ge_and (h _ <| half_pos ε0) (f.cauchy₃ <| half_pos ε0)).imp fun i H j ij k jk =>
    by
    let ⟨h₁, h₂⟩ := H _ ij
    have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk)) <;>
      rwa [sub_add_sub_cancel', add_halves] at this
#align cau_seq.equiv_def₃ CauSeq.equiv_def₃

theorem lim_zero_congr {f g : CauSeq β abv} (h : f ≈ g) : LimZero f ↔ LimZero g :=
  ⟨fun l => by simpa using add_lim_zero (Setoid.symm h) l, fun l => by simpa using add_lim_zero h l⟩
#align cau_seq.lim_zero_congr CauSeq.lim_zero_congr

theorem abv_pos_of_not_lim_zero {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ abv (f j) :=
  by
  haveI := Classical.propDecidable
  by_contra nk
  refine' hf fun ε ε0 => _
  simp [not_forall] at nk
  cases' f.cauchy₃ (half_pos ε0) with i hi
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine' ⟨j, fun k jk => _⟩
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
  rwa [sub_add_cancel, add_halves] at this
#align cau_seq.abv_pos_of_not_lim_zero CauSeq.abv_pos_of_not_lim_zero

theorem of_near (f : ℕ → β) (g : CauSeq β abv) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - g j) < ε) :
    IsCauSeq abv f
  | ε, ε0 =>
    let ⟨i, hi⟩ := exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      cases' hi _ le_rfl with h₁ h₂; rw [abv_sub abv] at h₁
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij))
      rwa [add_halves, add_halves, add_right_comm, sub_add_sub_cancel, sub_add_sub_cancel] at this⟩
#align cau_seq.of_near CauSeq.of_near

theorem not_lim_zero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f :=
  fun this : LimZero f =>
  have : LimZero (f - 0) := by simpa
  hf this
#align cau_seq.not_lim_zero_of_not_congr_zero CauSeq.not_lim_zero_of_not_congr_zero

theorem mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : g * f ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (g * f) := mul_lim_zero_right _ <| by simpa
  show LimZero (g * f - 0) by simpa
#align cau_seq.mul_equiv_zero CauSeq.mul_equiv_zero

theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (f * g) := mul_lim_zero_left _ <| by simpa
  show LimZero (f * g - 0) by simpa
#align cau_seq.mul_equiv_zero' CauSeq.mul_equiv_zero'

theorem mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 :=
  fun this : LimZero (f * g - 0) =>
  by
  have hlz : LimZero (f * g) := by simpa
  have hf' : ¬LimZero f := by simpa using show ¬lim_zero (f - 0) from hf
  have hg' : ¬LimZero g := by simpa using show ¬lim_zero (g - 0) from hg
  rcases abv_pos_of_not_lim_zero hf' with ⟨a1, ha1, N1, hN1⟩
  rcases abv_pos_of_not_lim_zero hg' with ⟨a2, ha2, N2, hN2⟩
  have : 0 < a1 * a2 := mul_pos ha1 ha2
  cases' hlz _ this with N hN
  let i := max N (max N1 N2)
  have hN' := hN i (le_max_left _ _)
  have hN1' := hN1 i (le_trans (le_max_left _ _) (le_max_right _ _))
  have hN1' := hN2 i (le_trans (le_max_right _ _) (le_max_right _ _))
  apply not_le_of_lt hN'
  change _ ≤ abv (_ * _)
  rw [IsAbsoluteValue.abv_mul abv]
  apply mul_le_mul <;> try assumption
  · apply le_of_lt ha2
  · apply IsAbsoluteValue.abv_nonneg abv
#align cau_seq.mul_not_equiv_zero CauSeq.mul_not_equiv_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_equiv [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `y] [":" `β] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≈_»
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
          "≈"
          (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
         "↔"
         («term_=_» `x "=" `y))))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        («term_↔_» (Term.app `LimZero [(Term.hole "_")]) "↔" (Term.hole "_"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `const_sub)
               ","
               (Tactic.rwRule [] `const_lim_zero)
               ","
               (Tactic.rwRule [] `sub_eq_zero)]
              "]")
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_↔_» (Term.app `LimZero [(Term.hole "_")]) "↔" (Term.hole "_"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `const_sub)
              ","
              (Tactic.rwRule [] `const_lim_zero)
              ","
              (Tactic.rwRule [] `sub_eq_zero)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `const_sub)
         ","
         (Tactic.rwRule [] `const_lim_zero)
         ","
         (Tactic.rwRule [] `sub_eq_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `const_lim_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `const_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_» (Term.app `LimZero [(Term.hole "_")]) "↔" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `LimZero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LimZero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≈_»
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
        "≈"
        (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
       "↔"
       («term_=_» `x "=" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_≈_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`x])
       "≈"
       (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst "const") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst', expected 'CauSeq.Data.Real.CauSeq.termconst._@.Data.Real.CauSeq._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  const_equiv
  { x y : β } : const x ≈ const y ↔ x = y
  := show LimZero _ ↔ _ by rw [ ← const_sub , const_lim_zero , sub_eq_zero ]
#align cau_seq.const_equiv CauSeq.const_equiv

theorem mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 * g1 ≈ f2 * g2 := by
  simpa only [mul_sub, sub_mul, sub_add_sub_cancel] using
    add_lim_zero (mul_lim_zero_left g1 hf) (mul_lim_zero_right f2 hg)
#align cau_seq.mul_equiv_mul CauSeq.mul_equiv_mul

theorem smul_equiv_smul [HasSmul G β] [IsScalarTower G β β] {f1 f2 : CauSeq β abv} (c : G)
    (hf : f1 ≈ f2) : c • f1 ≈ c • f2 := by
  simpa [const_smul, smul_one_mul _ _] using mul_equiv_mul (const_equiv.mpr <| Eq.refl <| c • 1) hf
#align cau_seq.smul_equiv_smul CauSeq.smul_equiv_smul

theorem pow_equiv_pow {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : ℕ) : f1 ^ n ≈ f2 ^ n :=
  by
  induction' n with n ih
  · simp only [pow_zero, Setoid.refl]
  · simpa only [pow_succ] using mul_equiv_mul hf ih
#align cau_seq.pow_equiv_pow CauSeq.pow_equiv_pow

end Ring

section IsDomain

variable [Ring β] [IsDomain β] (abv : β → α) [IsAbsoluteValue abv]

theorem one_not_equiv_zero : ¬const abv 1 ≈ const abv 0 := fun h =>
  have : ∀ ε > 0, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε := h
  have h1 : abv 1 ≤ 0 :=
    le_of_not_gt fun h2 : 0 < abv 1 =>
      (Exists.elim (this _ h2)) fun i hi => lt_irrefl (abv 1) <| by simpa using hi _ le_rfl
  have h2 : 0 ≤ abv 1 := IsAbsoluteValue.abv_nonneg _ _
  have : abv 1 = 0 := le_antisymm h1 h2
  have : (1 : β) = 0 := (IsAbsoluteValue.abv_eq_zero abv).1 this
  absurd this one_ne_zero
#align cau_seq.one_not_equiv_zero CauSeq.one_not_equiv_zero

end IsDomain

section DivisionRing

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | ε, ε0 =>
    let ⟨K, K0, HK⟩ := abv_pos_of_not_lim_zero hf
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun j ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩
#align cau_seq.inv_aux CauSeq.inv_aux

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩
#align cau_seq.inv CauSeq.inv

@[simp, norm_cast]
theorem coe_inv {f : CauSeq β abv} (hf) : ⇑(inv f hf) = f⁻¹ :=
  rfl
#align cau_seq.coe_inv CauSeq.coe_inv

@[simp, norm_cast]
theorem inv_apply {f : CauSeq β abv} (hf i) : inv f hf i = (f i)⁻¹ :=
  rfl
#align cau_seq.inv_apply CauSeq.inv_apply

theorem inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf * f ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_lim_zero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
#align cau_seq.inv_mul_cancel CauSeq.inv_mul_cancel

theorem mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv f hf ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_lim_zero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
#align cau_seq.mul_inv_cancel CauSeq.mul_inv_cancel

theorem const_inv {x : β} (hx : x ≠ 0) :
    const abv x⁻¹ = inv (const abv x) (by rwa [const_lim_zero]) :=
  rfl
#align cau_seq.const_inv CauSeq.const_inv

end DivisionRing

section Abs

-- mathport name: exprconst
local notation "const" => const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def Pos (f : CauSeq α abs) : Prop :=
  ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j
#align cau_seq.pos CauSeq.Pos

theorem not_lim_zero_of_pos {f : CauSeq α abs} : Pos f → ¬LimZero f
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_le h₁ (abs_lt.1 h₂).2
#align cau_seq.not_lim_zero_of_pos CauSeq.not_lim_zero_of_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_pos [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `α] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app `Pos [(Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])])
         "↔"
         («term_<_» (num "0") "<" `x))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`K "," `K0 "," `i "," `h] "⟩")]
           []
           "=>"
           (Term.app `lt_of_lt_of_le [`K0 (Term.app `h [(Term.hole "_") `le_rfl])])))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [`x
             ","
             `h
             ","
             (num "0")
             ","
             (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" `le_rfl))]
            "⟩")))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`K "," `K0 "," `i "," `h] "⟩")]
          []
          "=>"
          (Term.app `lt_of_lt_of_le [`K0 (Term.app `h [(Term.hole "_") `le_rfl])])))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [`x
            ","
            `h
            ","
            (num "0")
            ","
            (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" `le_rfl))]
           "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`x
          ","
          `h
          ","
          (num "0")
          ","
          (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" `le_rfl))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`x
        ","
        `h
        ","
        (num "0")
        ","
        (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" `le_rfl))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" `le_rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`K "," `K0 "," `i "," `h] "⟩")]
        []
        "=>"
        (Term.app `lt_of_lt_of_le [`K0 (Term.app `h [(Term.hole "_") `le_rfl])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_of_lt_of_le [`K0 (Term.app `h [(Term.hole "_") `le_rfl])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [(Term.hole "_") `le_rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `h [(Term.hole "_") `le_rfl])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_lt_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`K "," `K0 "," `i "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Term.app `Pos [(Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])])
       "↔"
       («term_<_» (num "0") "<" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `Pos [(Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst_1 "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst_1', expected 'CauSeq.Data.Real.CauSeq.termconst_1._@.Data.Real.CauSeq._hyg.532'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  const_pos
  { x : α } : Pos const x ↔ 0 < x
  :=
    ⟨
      fun ⟨ K , K0 , i , h ⟩ => lt_of_lt_of_le K0 h _ le_rfl
        ,
        fun h => ⟨ x , h , 0 , fun j _ => le_rfl ⟩
      ⟩
#align cau_seq.const_pos CauSeq.const_pos

theorem add_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f + g)
  | ⟨F, F0, hF⟩, ⟨G, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, add_pos F0 G0, i, fun j ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩
#align cau_seq.add_pos CauSeq.add_pos

theorem pos_add_lim_zero {f g : CauSeq α abs} : Pos f → LimZero g → Pos (f + g)
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      cases' h j ij with h₁ h₂
      have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩
#align cau_seq.pos_add_lim_zero CauSeq.pos_add_lim_zero

protected theorem mul_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f * g)
  | ⟨F, F0, hF⟩, ⟨G, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun j ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩
#align cau_seq.mul_pos CauSeq.mul_pos

theorem trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f) :=
  by
  cases Classical.em (lim_zero f) <;> simp [*]
  rcases abv_pos_of_not_lim_zero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  refine' (le_total 0 (f i)).imp _ _ <;> refine' fun h => ⟨K, K0, i, fun j ij => _⟩ <;>
      have := (hi _ ij).1 <;>
    cases' hi _ le_rfl with h₁ h₂
  · rwa [abs_of_nonneg] at this
    rw [abs_of_nonneg h] at h₁
    exact
      (le_add_iff_nonneg_right _).1
        (le_trans h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_lt (abs_lt.1 <| h₂ _ ij).1)
  · rwa [abs_of_nonpos] at this
    rw [abs_of_nonpos h] at h₁
    rw [← sub_le_sub_iff_right, zero_sub]
    exact le_trans (le_of_lt (abs_lt.1 <| h₂ _ ij).2) h₁
#align cau_seq.trichotomy CauSeq.trichotomy

instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩

instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩

theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h :=
  show Pos (h - f) by
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using pos_add_lim_zero fg (neg_lim_zero gh)
#align cau_seq.lt_of_lt_of_eq CauSeq.lt_of_lt_of_eq

theorem lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h := by
  have := pos_add_lim_zero gh (neg_lim_zero fg) <;>
    rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this
#align cau_seq.lt_of_eq_of_lt CauSeq.lt_of_eq_of_lt

theorem lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h :=
  show Pos (h - f) by simpa [sub_eq_add_neg, add_comm, add_left_comm] using add_pos fg gh
#align cau_seq.lt_trans CauSeq.lt_trans

theorem lt_irrefl {f : CauSeq α abs} : ¬f < f
  | h => not_lim_zero_of_pos h (by simp [zero_lim_zero])
#align cau_seq.lt_irrefl CauSeq.lt_irrefl

theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
  hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)
#align cau_seq.le_of_eq_of_le CauSeq.le_of_eq_of_le

theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
  hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)
#align cau_seq.le_of_le_of_eq CauSeq.le_of_le_of_eq

instance : Preorder (CauSeq α abs) where
  lt := (· < ·)
  le f g := f < g ∨ f ≈ g
  le_refl f := Or.inr (Setoid.refl _)
  le_trans f g h fg :=
    match fg with
    | Or.inl fg, Or.inl gh => Or.inl <| lt_trans fg gh
    | Or.inl fg, Or.inr gh => Or.inl <| lt_of_lt_of_eq fg gh
    | Or.inr fg, Or.inl gh => Or.inl <| lt_of_eq_of_lt fg gh
    | Or.inr fg, Or.inr gh => Or.inr <| Setoid.trans fg gh
  lt_iff_le_not_le f g :=
    ⟨fun h => ⟨Or.inl h, not_or_of_not (mt (lt_trans h) lt_irrefl) (not_lim_zero_of_pos h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_right (mt (fun h => Or.inr (Setoid.symm h)) h₂)⟩

theorem le_antisymm {f g : CauSeq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
  fg.resolve_left (not_lt_of_le gf)
#align cau_seq.le_antisymm CauSeq.le_antisymm

theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f :=
  (trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoid.symm h) fun h => by rwa [neg_sub] at h
#align cau_seq.lt_total CauSeq.lt_total

theorem le_total (f g : CauSeq α abs) : f ≤ g ∨ g ≤ f :=
  (or_assoc.2 (lt_total f g)).imp_right Or.inl
#align cau_seq.le_total CauSeq.le_total

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_lt [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `y] [":" `α] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])
          "<"
          (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y]))
         "↔"
         («term_<_» `x "<" `y))))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        («term_↔_» (Term.app `Pos [(Term.hole "_")]) "↔" (Term.hole "_"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `const_sub)
               ","
               (Tactic.rwRule [] `const_pos)
               ","
               (Tactic.rwRule [] `sub_pos)]
              "]")
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_↔_» (Term.app `Pos [(Term.hole "_")]) "↔" (Term.hole "_"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `const_sub)
              ","
              (Tactic.rwRule [] `const_pos)
              ","
              (Tactic.rwRule [] `sub_pos)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `const_sub)
         ","
         (Tactic.rwRule [] `const_pos)
         ","
         (Tactic.rwRule [] `sub_pos)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `const_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `const_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_» (Term.app `Pos [(Term.hole "_")]) "↔" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `Pos [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])
        "<"
        (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y]))
       "↔"
       («term_<_» `x "<" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `x "<" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_<_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])
       "<"
       (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst_1 "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst_1', expected 'CauSeq.Data.Real.CauSeq.termconst_1._@.Data.Real.CauSeq._hyg.532'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  const_lt
  { x y : α } : const x < const y ↔ x < y
  := show Pos _ ↔ _ by rw [ ← const_sub , const_pos , sub_pos ]
#align cau_seq.const_lt CauSeq.const_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `y] [":" `α] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≤_»
          (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])
          "≤"
          (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y]))
         "↔"
         («term_≤_» `x "≤" `y))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_iff_lt_or_eq)] "]")
             [])
            "<;>"
            (Tactic.exact "exact" (Term.app `or_congr [`const_lt `const_equiv])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_iff_lt_or_eq)] "]")
            [])
           "<;>"
           (Tactic.exact "exact" (Term.app `or_congr [`const_lt `const_equiv])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_iff_lt_or_eq)] "]") [])
       "<;>"
       (Tactic.exact "exact" (Term.app `or_congr [`const_lt `const_equiv])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `or_congr [`const_lt `const_equiv]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `or_congr [`const_lt `const_equiv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `const_equiv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `const_lt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `or_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_iff_lt_or_eq)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_iff_lt_or_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≤_»
        (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])
        "≤"
        (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y]))
       "↔"
       («term_≤_» `x "≤" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» `x "≤" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_≤_»
       (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`x])
       "≤"
       (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst_1 "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst_1', expected 'CauSeq.Data.Real.CauSeq.termconst_1._@.Data.Real.CauSeq._hyg.532'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  const_le
  { x y : α } : const x ≤ const y ↔ x ≤ y
  := by rw [ le_iff_lt_or_eq ] <;> exact or_congr const_lt const_equiv
#align cau_seq.const_le CauSeq.const_le

theorem le_of_exists {f g : CauSeq α abs} (h : ∃ i, ∀ j ≥ i, f j ≤ g j) : f ≤ g :=
  let ⟨i, hi⟩ := h
  (or_assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨K, hK0, j, hKj⟩ := hgf
      not_lt_of_ge (hi (max i j) (le_max_left _ _))
        (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _)))))
#align cau_seq.le_of_exists CauSeq.le_of_exists

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_gt [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.app `CauSeq [`α `abs])] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
         ","
         («term_<_» `f "<" (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a])))))
      (Command.declValSimple
       ":="
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor "⟨" [`K "," `H] "⟩")
          []
          []
          ":="
          (Term.proj `f "." `Bounded)))
        []
        (Term.anonymousCtor
         "⟨"
         [(«term_+_» `K "+" (num "1"))
          ","
          (num "1")
          ","
          `zero_lt_one
          ","
          (num "0")
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [`i (Term.hole "_")]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `sub_apply)
                   ","
                   (Tactic.rwRule [] `const_apply)
                   ","
                   (Tactic.rwRule [] `le_sub_iff_add_le')
                   ","
                   (Tactic.rwRule [] `add_le_add_iff_right)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `le_of_lt
                  [(Term.proj
                    (Term.app
                     (Term.proj `abs_lt "." (fieldIdx "1"))
                     [(Term.app `H [(Term.hole "_")])])
                    "."
                    (fieldIdx "2"))]))])))))]
         "⟩"))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`K "," `H] "⟩")
         []
         []
         ":="
         (Term.proj `f "." `Bounded)))
       []
       (Term.anonymousCtor
        "⟨"
        [(«term_+_» `K "+" (num "1"))
         ","
         (num "1")
         ","
         `zero_lt_one
         ","
         (num "0")
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`i (Term.hole "_")]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `sub_apply)
                  ","
                  (Tactic.rwRule [] `const_apply)
                  ","
                  (Tactic.rwRule [] `le_sub_iff_add_le')
                  ","
                  (Tactic.rwRule [] `add_le_add_iff_right)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `le_of_lt
                 [(Term.proj
                   (Term.app
                    (Term.proj `abs_lt "." (fieldIdx "1"))
                    [(Term.app `H [(Term.hole "_")])])
                   "."
                   (fieldIdx "2"))]))])))))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_+_» `K "+" (num "1"))
        ","
        (num "1")
        ","
        `zero_lt_one
        ","
        (num "0")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`i (Term.hole "_")]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `sub_apply)
                 ","
                 (Tactic.rwRule [] `const_apply)
                 ","
                 (Tactic.rwRule [] `le_sub_iff_add_le')
                 ","
                 (Tactic.rwRule [] `add_le_add_iff_right)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `le_of_lt
                [(Term.proj
                  (Term.app
                   (Term.proj `abs_lt "." (fieldIdx "1"))
                   [(Term.app `H [(Term.hole "_")])])
                  "."
                  (fieldIdx "2"))]))])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i (Term.hole "_")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `sub_apply)
               ","
               (Tactic.rwRule [] `const_apply)
               ","
               (Tactic.rwRule [] `le_sub_iff_add_le')
               ","
               (Tactic.rwRule [] `add_le_add_iff_right)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `le_of_lt
              [(Term.proj
                (Term.app (Term.proj `abs_lt "." (fieldIdx "1")) [(Term.app `H [(Term.hole "_")])])
                "."
                (fieldIdx "2"))]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `sub_apply)
             ","
             (Tactic.rwRule [] `const_apply)
             ","
             (Tactic.rwRule [] `le_sub_iff_add_le')
             ","
             (Tactic.rwRule [] `add_le_add_iff_right)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `le_of_lt
            [(Term.proj
              (Term.app (Term.proj `abs_lt "." (fieldIdx "1")) [(Term.app `H [(Term.hole "_")])])
              "."
              (fieldIdx "2"))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `le_of_lt
        [(Term.proj
          (Term.app (Term.proj `abs_lt "." (fieldIdx "1")) [(Term.app `H [(Term.hole "_")])])
          "."
          (fieldIdx "2"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_lt
       [(Term.proj
         (Term.app (Term.proj `abs_lt "." (fieldIdx "1")) [(Term.app `H [(Term.hole "_")])])
         "."
         (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app (Term.proj `abs_lt "." (fieldIdx "1")) [(Term.app `H [(Term.hole "_")])])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `abs_lt "." (fieldIdx "1")) [(Term.app `H [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `H [(Term.hole "_")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `abs_lt "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `abs_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `abs_lt "." (fieldIdx "1"))
      [(Term.paren "(" (Term.app `H [(Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `sub_apply)
         ","
         (Tactic.rwRule [] `const_apply)
         ","
         (Tactic.rwRule [] `le_sub_iff_add_le')
         ","
         (Tactic.rwRule [] `add_le_add_iff_right)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_le_add_iff_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_sub_iff_add_le'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `const_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_lt_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `K "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `Bounded)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`K "," `H] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
       ","
       («term_<_» `f "<" (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `f "<" (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst_1 "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst_1', expected 'CauSeq.Data.Real.CauSeq.termconst_1._@.Data.Real.CauSeq._hyg.532'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_gt
  ( f : CauSeq α abs ) : ∃ a : α , f < const a
  :=
    let
      ⟨ K , H ⟩ := f . Bounded
      ⟨
        K + 1
          ,
          1
          ,
          zero_lt_one
          ,
          0
          ,
          fun
            i _
              =>
              by
                rw [ sub_apply , const_apply , le_sub_iff_add_le' , add_le_add_iff_right ]
                  exact le_of_lt abs_lt . 1 H _ . 2
        ⟩
#align cau_seq.exists_gt CauSeq.exists_gt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_lt [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.app `CauSeq [`α `abs])] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
         ","
         («term_<_» (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a]) "<" `f))))
      (Command.declValSimple
       ":="
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor "⟨" [`a "," `h] "⟩")
          []
          []
          ":="
          (Term.proj («term-_» "-" `f) "." `exists_gt)))
        []
        (Term.anonymousCtor
         "⟨"
         [(«term-_» "-" `a)
          ","
          (Term.show
           "show"
           (Term.app `Pos [(Term.hole "_")])
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `const_neg)
                  ","
                  (Tactic.rwRule [] `sub_neg_eq_add)
                  ","
                  (Tactic.rwRule [] `add_comm)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_neg_eq_add)]
                 "]")
                [])]))))]
         "⟩"))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`a "," `h] "⟩")
         []
         []
         ":="
         (Term.proj («term-_» "-" `f) "." `exists_gt)))
       []
       (Term.anonymousCtor
        "⟨"
        [(«term-_» "-" `a)
         ","
         (Term.show
          "show"
          (Term.app `Pos [(Term.hole "_")])
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `const_neg)
                 ","
                 (Tactic.rwRule [] `sub_neg_eq_add)
                 ","
                 (Tactic.rwRule [] `add_comm)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_neg_eq_add)]
                "]")
               [])]))))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term-_» "-" `a)
        ","
        (Term.show
         "show"
         (Term.app `Pos [(Term.hole "_")])
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `const_neg)
                ","
                (Tactic.rwRule [] `sub_neg_eq_add)
                ","
                (Tactic.rwRule [] `add_comm)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_neg_eq_add)]
               "]")
              [])]))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app `Pos [(Term.hole "_")])
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `const_neg)
              ","
              (Tactic.rwRule [] `sub_neg_eq_add)
              ","
              (Tactic.rwRule [] `add_comm)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_neg_eq_add)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `const_neg)
         ","
         (Tactic.rwRule [] `sub_neg_eq_add)
         ","
         (Tactic.rwRule [] `add_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_neg_eq_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_neg_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_neg_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `const_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Pos [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj («term-_» "-" `f) "." `exists_gt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term-_» "-" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `f) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
       ","
       («term_<_» (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a]) "<" `f))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a]) "<" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CauSeq.Data.Real.CauSeq.termconst_1 "const") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CauSeq.Data.Real.CauSeq.termconst_1 "const")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CauSeq.Data.Real.CauSeq.termconst_1', expected 'CauSeq.Data.Real.CauSeq.termconst_1._@.Data.Real.CauSeq._hyg.532'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_lt
  ( f : CauSeq α abs ) : ∃ a : α , const a < f
  :=
    let
      ⟨ a , h ⟩ := - f . exists_gt
      ⟨ - a , show Pos _ by rwa [ const_neg , sub_neg_eq_add , add_comm , ← sub_neg_eq_add ] ⟩
#align cau_seq.exists_lt CauSeq.exists_lt

-- so named to match `rat_add_continuous_lemma`
theorem rat_sup_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊔ a₂ - b₁ ⊔ b₂) < ε := fun h₁ h₂ =>
  (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)
#align rat_sup_continuous_lemma rat_sup_continuous_lemma

-- so named to match `rat_add_continuous_lemma`
theorem rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊓ a₂ - b₁ ⊓ b₂) < ε := fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)
#align rat_inf_continuous_lemma rat_inf_continuous_lemma

instance : HasSup (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun ε ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun i H j ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

instance : HasInf (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun ε ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun i H j ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[simp, norm_cast]
theorem coe_sup (f g : CauSeq α abs) : ⇑(f ⊔ g) = f ⊔ g :=
  rfl
#align cau_seq.coe_sup CauSeq.coe_sup

@[simp, norm_cast]
theorem coe_inf (f g : CauSeq α abs) : ⇑(f ⊓ g) = f ⊓ g :=
  rfl
#align cau_seq.coe_inf CauSeq.coe_inf

theorem sup_lim_zero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊔ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun i H j ij =>
      by
      let ⟨H₁, H₂⟩ := H _ ij
      rw [abs_lt] at H₁ H₂⊢
      exact ⟨lt_sup_iff.mpr (Or.inl H₁.1), sup_lt_iff.mpr ⟨H₁.2, H₂.2⟩⟩
#align cau_seq.sup_lim_zero CauSeq.sup_lim_zero

theorem inf_lim_zero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊓ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun i H j ij =>
      by
      let ⟨H₁, H₂⟩ := H _ ij
      rw [abs_lt] at H₁ H₂⊢
      exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (Or.inl H₁.2)⟩
#align cau_seq.inf_lim_zero CauSeq.inf_lim_zero

theorem sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊔ b₁ ≈ a₂ ⊔ b₂ := by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_max_sub_max_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩
#align cau_seq.sup_equiv_sup CauSeq.sup_equiv_sup

theorem inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊓ b₁ ≈ a₂ ⊓ b₂ := by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩
#align cau_seq.inf_equiv_inf CauSeq.inf_equiv_inf

protected theorem sup_lt {a b c : CauSeq α abs} (ha : a < c) (hb : b < c) : a ⊔ b < c :=
  by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  refine' ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => _⟩
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_left _ _ _)
#align cau_seq.sup_lt CauSeq.sup_lt

protected theorem lt_inf {a b c : CauSeq α abs} (hb : a < b) (hc : a < c) : a < b ⊓ c :=
  by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  refine' ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => _⟩
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_right _ _ _)
#align cau_seq.lt_inf CauSeq.lt_inf

@[simp]
protected theorem sup_idem (a : CauSeq α abs) : a ⊔ a = a :=
  Subtype.ext sup_idem
#align cau_seq.sup_idem CauSeq.sup_idem

@[simp]
protected theorem inf_idem (a : CauSeq α abs) : a ⊓ a = a :=
  Subtype.ext inf_idem
#align cau_seq.inf_idem CauSeq.inf_idem

protected theorem sup_comm (a b : CauSeq α abs) : a ⊔ b = b ⊔ a :=
  Subtype.ext sup_comm
#align cau_seq.sup_comm CauSeq.sup_comm

protected theorem inf_comm (a b : CauSeq α abs) : a ⊓ b = b ⊓ a :=
  Subtype.ext inf_comm
#align cau_seq.inf_comm CauSeq.inf_comm

protected theorem sup_eq_right {a b : CauSeq α abs} (h : a ≤ b) : a ⊔ b ≈ b :=
  by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine' ⟨i, fun j hj => _⟩
    dsimp
    erw [← max_sub_sub_right]
    rwa [sub_self, max_eq_right, abs_zero]
    rw [sub_nonpos, ← sub_nonneg]
    exact ε0.le.trans (h _ hj)
  · refine' Setoid.trans (sup_equiv_sup h (Setoid.refl _)) _
    rw [CauSeq.sup_idem]
    exact Setoid.refl _
#align cau_seq.sup_eq_right CauSeq.sup_eq_right

protected theorem inf_eq_right {a b : CauSeq α abs} (h : b ≤ a) : a ⊓ b ≈ b :=
  by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine' ⟨i, fun j hj => _⟩
    dsimp
    erw [← min_sub_sub_right]
    rwa [sub_self, min_eq_right, abs_zero]
    exact ε0.le.trans (h _ hj)
  · refine' Setoid.trans (inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) _
    rw [CauSeq.inf_idem]
    exact Setoid.refl _
#align cau_seq.inf_eq_right CauSeq.inf_eq_right

protected theorem sup_eq_left {a b : CauSeq α abs} (h : b ≤ a) : a ⊔ b ≈ a := by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h
#align cau_seq.sup_eq_left CauSeq.sup_eq_left

protected theorem inf_eq_left {a b : CauSeq α abs} (h : a ≤ b) : a ⊓ b ≈ a := by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h
#align cau_seq.inf_eq_left CauSeq.inf_eq_left

protected theorem le_sup_left {a b : CauSeq α abs} : a ≤ a ⊔ b :=
  le_of_exists ⟨0, fun j hj => le_sup_left⟩
#align cau_seq.le_sup_left CauSeq.le_sup_left

protected theorem inf_le_left {a b : CauSeq α abs} : a ⊓ b ≤ a :=
  le_of_exists ⟨0, fun j hj => inf_le_left⟩
#align cau_seq.inf_le_left CauSeq.inf_le_left

protected theorem le_sup_right {a b : CauSeq α abs} : b ≤ a ⊔ b :=
  le_of_exists ⟨0, fun j hj => le_sup_right⟩
#align cau_seq.le_sup_right CauSeq.le_sup_right

protected theorem inf_le_right {a b : CauSeq α abs} : a ⊓ b ≤ b :=
  le_of_exists ⟨0, fun j hj => inf_le_right⟩
#align cau_seq.inf_le_right CauSeq.inf_le_right

protected theorem sup_le {a b c : CauSeq α abs} (ha : a ≤ c) (hb : b ≤ c) : a ⊔ b ≤ c :=
  by
  cases' ha with ha ha
  · cases' hb with hb hb
    · exact Or.inl (CauSeq.sup_lt ha hb)
    · replace ha := le_of_le_of_eq ha.le (Setoid.symm hb)
      refine' le_of_le_of_eq (Or.inr _) hb
      exact CauSeq.sup_eq_right ha
  · replace hb := le_of_le_of_eq hb (Setoid.symm ha)
    refine' le_of_le_of_eq (Or.inr _) ha
    exact CauSeq.sup_eq_left hb
#align cau_seq.sup_le CauSeq.sup_le

protected theorem le_inf {a b c : CauSeq α abs} (hb : a ≤ b) (hc : a ≤ c) : a ≤ b ⊓ c :=
  by
  cases' hb with hb hb
  · cases' hc with hc hc
    · exact Or.inl (CauSeq.lt_inf hb hc)
    · replace hb := le_of_eq_of_le (Setoid.symm hc) hb.le
      refine' le_of_eq_of_le hc (Or.inr _)
      exact Setoid.symm (CauSeq.inf_eq_right hb)
  · replace hc := le_of_eq_of_le (Setoid.symm hb) hc
    refine' le_of_eq_of_le hb (Or.inr _)
    exact Setoid.symm (CauSeq.inf_eq_left hc)
#align cau_seq.le_inf CauSeq.le_inf

/-! Note that `distrib_lattice (cau_seq α abs)` is not true because there is no `partial_order`. -/


protected theorem sup_inf_distrib_left (a b c : CauSeq α abs) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  Subtype.ext <| funext fun i => max_min_distrib_left
#align cau_seq.sup_inf_distrib_left CauSeq.sup_inf_distrib_left

protected theorem sup_inf_distrib_right (a b c : CauSeq α abs) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
  Subtype.ext <| funext fun i => max_min_distrib_right
#align cau_seq.sup_inf_distrib_right CauSeq.sup_inf_distrib_right

end Abs

end CauSeq

