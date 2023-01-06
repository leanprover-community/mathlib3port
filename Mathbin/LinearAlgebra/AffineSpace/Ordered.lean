/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module linear_algebra.affine_space.ordered
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Invertible
import Mathbin.Algebra.Order.Module
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.LinearAlgebra.AffineSpace.Slope
import Mathbin.Tactic.FieldSimp

/-!
# Ordered modules as affine spaces

In this file we prove some theorems about `slope` and `line_map` in the case when the module `E`
acting on the codomain `PE` of a function is an ordered module over its domain `k`. We also prove
inequalities that can be used to link convexity of a function on an interval to monotonicity of the
slope, see section docstring below for details.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered module interpreted as an affine space.

## Tags

affine space, ordered module, slope
-/


open AffineMap

variable {k E PE : Type _}

/-!
### Monotonicity of `line_map`

In this section we prove that `line_map a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/


section OrderedRing

variable [OrderedRing k] [OrderedAddCommGroup E] [Module k E] [OrderedSmul k E]

variable {a a' b b' : E} {r r' : k}

theorem line_map_mono_left (ha : a ≤ a') (hr : r ≤ 1) : lineMap a b r ≤ lineMap a' b r :=
  by
  simp only [line_map_apply_module]
  exact add_le_add_right (smul_le_smul_of_nonneg ha (sub_nonneg.2 hr)) _
#align line_map_mono_left line_map_mono_left

theorem line_map_strict_mono_left (ha : a < a') (hr : r < 1) : lineMap a b r < lineMap a' b r :=
  by
  simp only [line_map_apply_module]
  exact add_lt_add_right (smul_lt_smul_of_pos ha (sub_pos.2 hr)) _
#align line_map_strict_mono_left line_map_strict_mono_left

theorem line_map_mono_right (hb : b ≤ b') (hr : 0 ≤ r) : lineMap a b r ≤ lineMap a b' r :=
  by
  simp only [line_map_apply_module]
  exact add_le_add_left (smul_le_smul_of_nonneg hb hr) _
#align line_map_mono_right line_map_mono_right

theorem line_map_strict_mono_right (hb : b < b') (hr : 0 < r) : lineMap a b r < lineMap a b' r :=
  by
  simp only [line_map_apply_module]
  exact add_lt_add_left (smul_lt_smul_of_pos hb hr) _
#align line_map_strict_mono_right line_map_strict_mono_right

theorem line_map_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r ≤ lineMap a' b' r :=
  (line_map_mono_left ha h₁).trans (line_map_mono_right hb h₀)
#align line_map_mono_endpoints line_map_mono_endpoints

theorem line_map_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r < lineMap a' b' r :=
  by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (line_map_mono_left ha.le h₁).trans_lt (line_map_strict_mono_right hb h₀)
#align line_map_strict_mono_endpoints line_map_strict_mono_endpoints

theorem line_map_lt_line_map_iff_of_lt (h : r < r') : lineMap a b r < lineMap a b r' ↔ a < b :=
  by
  simp only [line_map_apply_module]
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos (sub_pos.2 h)]
  infer_instance
#align line_map_lt_line_map_iff_of_lt line_map_lt_line_map_iff_of_lt

theorem left_lt_line_map_iff_lt (h : 0 < r) : a < lineMap a b r ↔ a < b :=
  Iff.trans (by rw [line_map_apply_zero]) (line_map_lt_line_map_iff_of_lt h)
#align left_lt_line_map_iff_lt left_lt_line_map_iff_lt

theorem line_map_lt_left_iff_lt (h : 0 < r) : lineMap a b r < a ↔ b < a :=
  @left_lt_line_map_iff_lt k Eᵒᵈ _ _ _ _ _ _ _ h
#align line_map_lt_left_iff_lt line_map_lt_left_iff_lt

theorem line_map_lt_right_iff_lt (h : r < 1) : lineMap a b r < b ↔ a < b :=
  Iff.trans (by rw [line_map_apply_one]) (line_map_lt_line_map_iff_of_lt h)
#align line_map_lt_right_iff_lt line_map_lt_right_iff_lt

theorem right_lt_line_map_iff_lt (h : r < 1) : b < lineMap a b r ↔ b < a :=
  @line_map_lt_right_iff_lt k Eᵒᵈ _ _ _ _ _ _ _ h
#align right_lt_line_map_iff_lt right_lt_line_map_iff_lt

end OrderedRing

section LinearOrderedRing

variable [LinearOrderedRing k] [OrderedAddCommGroup E] [Module k E] [OrderedSmul k E]
  [Invertible (2 : k)] {a a' b b' : E} {r r' : k}

theorem midpoint_le_midpoint (ha : a ≤ a') (hb : b ≤ b') : midpoint k a b ≤ midpoint k a' b' :=
  line_map_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) <| invOf_le_one one_le_two
#align midpoint_le_midpoint midpoint_le_midpoint

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField k] [OrderedAddCommGroup E]

variable [Module k E] [OrderedSmul k E]

section

variable {a b : E} {r r' : k}

theorem line_map_le_line_map_iff_of_lt (h : r < r') : lineMap a b r ≤ lineMap a b r' ↔ a ≤ b :=
  by
  simp only [line_map_apply_module]
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos (sub_pos.2 h)]
  infer_instance
#align line_map_le_line_map_iff_of_lt line_map_le_line_map_iff_of_lt

theorem left_le_line_map_iff_le (h : 0 < r) : a ≤ lineMap a b r ↔ a ≤ b :=
  Iff.trans (by rw [line_map_apply_zero]) (line_map_le_line_map_iff_of_lt h)
#align left_le_line_map_iff_le left_le_line_map_iff_le

@[simp]
theorem left_le_midpoint : a ≤ midpoint k a b ↔ a ≤ b :=
  left_le_line_map_iff_le <| inv_pos.2 zero_lt_two
#align left_le_midpoint left_le_midpoint

theorem line_map_le_left_iff_le (h : 0 < r) : lineMap a b r ≤ a ↔ b ≤ a :=
  @left_le_line_map_iff_le k Eᵒᵈ _ _ _ _ _ _ _ h
#align line_map_le_left_iff_le line_map_le_left_iff_le

@[simp]
theorem midpoint_le_left : midpoint k a b ≤ a ↔ b ≤ a :=
  line_map_le_left_iff_le <| inv_pos.2 zero_lt_two
#align midpoint_le_left midpoint_le_left

theorem line_map_le_right_iff_le (h : r < 1) : lineMap a b r ≤ b ↔ a ≤ b :=
  Iff.trans (by rw [line_map_apply_one]) (line_map_le_line_map_iff_of_lt h)
#align line_map_le_right_iff_le line_map_le_right_iff_le

@[simp]
theorem midpoint_le_right : midpoint k a b ≤ b ↔ a ≤ b :=
  line_map_le_right_iff_le <| inv_lt_one one_lt_two
#align midpoint_le_right midpoint_le_right

theorem right_le_line_map_iff_le (h : r < 1) : b ≤ lineMap a b r ↔ b ≤ a :=
  @line_map_le_right_iff_le k Eᵒᵈ _ _ _ _ _ _ _ h
#align right_le_line_map_iff_le right_le_line_map_iff_le

@[simp]
theorem right_le_midpoint : b ≤ midpoint k a b ↔ b ≤ a :=
  right_le_line_map_iff_le <| inv_lt_one one_lt_two
#align right_le_midpoint right_le_midpoint

end

/-!
### Convexity and slope

Given an interval `[a, b]` and a point `c ∈ (a, b)`, `c = line_map a b r`, there are a few ways to
say that the point `(c, f c)` is above/below the segment `[(a, f a), (b, f b)]`:

* compare `f c` to `line_map (f a) (f b) r`;
* compare `slope f a c` to `slope `f a b`;
* compare `slope f c b` to `slope f a b`;
* compare `slope f a c` to `slope f c b`.

In this section we prove equivalence of these four approaches. In order to make the statements more
readable, we introduce local notation `c = line_map a b r`. Then we prove lemmas like

```
lemma map_le_line_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  f c ≤ line_map (f a) (f b) r ↔ slope f a c ≤ slope f a b :=
```

For each inequality between `f c` and `line_map (f a) (f b) r` we provide 3 lemmas:

* `*_left` relates it to an inequality on `slope f a c` and `slope f a b`;
* `*_right` relates it to an inequality on `slope f a b` and `slope f c b`;
* no-suffix version relates it to an inequality on `slope f a c` and `slope f c b`.

These inequalities can by used in to restate `convex_on` in terms of monotonicity of the slope.
-/


variable {f : k → E} {a b r : k}

-- mathport name: exprc
local notation "c" => lineMap a b r

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly below the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f a b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_le_line_map_iff_slope_le_slope_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" («term_<_» (num "0") "<" («term_*_» `r "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≤_»
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "≤"
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
         "↔"
         («term_≤_»
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "≤"
          (Term.app `slope [`f `a `b])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `line_map_apply)
              ","
              (Tactic.rwRule [] `line_map_apply)
              ","
              (Tactic.rwRule [] `slope)
              ","
              (Tactic.rwRule [] `slope)
              ","
              (Tactic.rwRule [] `vsub_eq_sub)
              ","
              (Tactic.rwRule [] `vsub_eq_sub)
              ","
              (Tactic.rwRule [] `vsub_eq_sub)
              ","
              (Tactic.rwRule [] `vadd_eq_add)
              ","
              (Tactic.rwRule [] `vadd_eq_add)
              ","
              (Tactic.rwRule [] `smul_eq_mul)
              ","
              (Tactic.rwRule [] `add_sub_cancel)
              ","
              (Tactic.rwRule [] `smul_sub)
              ","
              (Tactic.rwRule [] `smul_sub)
              ","
              (Tactic.rwRule [] `smul_sub)
              ","
              (Tactic.rwRule [] `sub_le_iff_le_add)
              ","
              (Tactic.rwRule [] `mul_inv_rev)
              ","
              (Tactic.rwRule [] `mul_smul)
              ","
              (Tactic.rwRule [] `mul_smul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_sub)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_sub)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_add)
              ","
              (Tactic.rwRule [] `smul_smul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_inv_rev)
              ","
              (Tactic.rwRule [] (Term.app `inv_smul_le_iff [`h]))
              ","
              (Tactic.rwRule [] `smul_smul)
              ","
              (Tactic.rwRule
               []
               (Term.app `mul_inv_cancel_right₀ [(Term.app `right_ne_zero_of_mul [`h.ne'])]))
              ","
              (Tactic.rwRule [] `smul_add)
              ","
              (Tactic.rwRule
               []
               (Term.app `smul_inv_smul₀ [(Term.app `left_ne_zero_of_mul [`h.ne'])]))]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `line_map_apply)
             ","
             (Tactic.rwRule [] `line_map_apply)
             ","
             (Tactic.rwRule [] `slope)
             ","
             (Tactic.rwRule [] `slope)
             ","
             (Tactic.rwRule [] `vsub_eq_sub)
             ","
             (Tactic.rwRule [] `vsub_eq_sub)
             ","
             (Tactic.rwRule [] `vsub_eq_sub)
             ","
             (Tactic.rwRule [] `vadd_eq_add)
             ","
             (Tactic.rwRule [] `vadd_eq_add)
             ","
             (Tactic.rwRule [] `smul_eq_mul)
             ","
             (Tactic.rwRule [] `add_sub_cancel)
             ","
             (Tactic.rwRule [] `smul_sub)
             ","
             (Tactic.rwRule [] `smul_sub)
             ","
             (Tactic.rwRule [] `smul_sub)
             ","
             (Tactic.rwRule [] `sub_le_iff_le_add)
             ","
             (Tactic.rwRule [] `mul_inv_rev)
             ","
             (Tactic.rwRule [] `mul_smul)
             ","
             (Tactic.rwRule [] `mul_smul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_sub)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_sub)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_add)
             ","
             (Tactic.rwRule [] `smul_smul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_inv_rev)
             ","
             (Tactic.rwRule [] (Term.app `inv_smul_le_iff [`h]))
             ","
             (Tactic.rwRule [] `smul_smul)
             ","
             (Tactic.rwRule
              []
              (Term.app `mul_inv_cancel_right₀ [(Term.app `right_ne_zero_of_mul [`h.ne'])]))
             ","
             (Tactic.rwRule [] `smul_add)
             ","
             (Tactic.rwRule
              []
              (Term.app `smul_inv_smul₀ [(Term.app `left_ne_zero_of_mul [`h.ne'])]))]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `line_map_apply)
         ","
         (Tactic.rwRule [] `line_map_apply)
         ","
         (Tactic.rwRule [] `slope)
         ","
         (Tactic.rwRule [] `slope)
         ","
         (Tactic.rwRule [] `vsub_eq_sub)
         ","
         (Tactic.rwRule [] `vsub_eq_sub)
         ","
         (Tactic.rwRule [] `vsub_eq_sub)
         ","
         (Tactic.rwRule [] `vadd_eq_add)
         ","
         (Tactic.rwRule [] `vadd_eq_add)
         ","
         (Tactic.rwRule [] `smul_eq_mul)
         ","
         (Tactic.rwRule [] `add_sub_cancel)
         ","
         (Tactic.rwRule [] `smul_sub)
         ","
         (Tactic.rwRule [] `smul_sub)
         ","
         (Tactic.rwRule [] `smul_sub)
         ","
         (Tactic.rwRule [] `sub_le_iff_le_add)
         ","
         (Tactic.rwRule [] `mul_inv_rev)
         ","
         (Tactic.rwRule [] `mul_smul)
         ","
         (Tactic.rwRule [] `mul_smul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_sub)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_sub)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_add)
         ","
         (Tactic.rwRule [] `smul_smul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_inv_rev)
         ","
         (Tactic.rwRule [] (Term.app `inv_smul_le_iff [`h]))
         ","
         (Tactic.rwRule [] `smul_smul)
         ","
         (Tactic.rwRule
          []
          (Term.app `mul_inv_cancel_right₀ [(Term.app `right_ne_zero_of_mul [`h.ne'])]))
         ","
         (Tactic.rwRule [] `smul_add)
         ","
         (Tactic.rwRule [] (Term.app `smul_inv_smul₀ [(Term.app `left_ne_zero_of_mul [`h.ne'])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_inv_smul₀ [(Term.app `left_ne_zero_of_mul [`h.ne'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `left_ne_zero_of_mul [`h.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `left_ne_zero_of_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `left_ne_zero_of_mul [`h.ne'])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_inv_smul₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_inv_cancel_right₀ [(Term.app `right_ne_zero_of_mul [`h.ne'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `right_ne_zero_of_mul [`h.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `right_ne_zero_of_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `right_ne_zero_of_mul [`h.ne'])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_inv_cancel_right₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_smul_le_iff [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_smul_le_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_inv_rev
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_inv_rev
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_le_iff_le_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_sub_cancel
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vadd_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vadd_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vsub_eq_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vsub_eq_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vsub_eq_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slope
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slope
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `line_map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `line_map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≤_»
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "≤"
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
       "↔"
       («term_≤_»
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "≤"
        (Term.app `slope [`f `a `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
       "≤"
       (Term.app `slope [`f `a `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly below the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f a b`. -/
  theorem
    map_le_line_map_iff_slope_le_slope_left
    ( h : 0 < r * b - a ) : f c ≤ lineMap f a f b r ↔ slope f a c ≤ slope f a b
    :=
      by
        rw
            [
              line_map_apply
                ,
                line_map_apply
                ,
                slope
                ,
                slope
                ,
                vsub_eq_sub
                ,
                vsub_eq_sub
                ,
                vsub_eq_sub
                ,
                vadd_eq_add
                ,
                vadd_eq_add
                ,
                smul_eq_mul
                ,
                add_sub_cancel
                ,
                smul_sub
                ,
                smul_sub
                ,
                smul_sub
                ,
                sub_le_iff_le_add
                ,
                mul_inv_rev
                ,
                mul_smul
                ,
                mul_smul
                ,
                ← smul_sub
                ,
                ← smul_sub
                ,
                ← smul_add
                ,
                smul_smul
                ,
                ← mul_inv_rev
                ,
                inv_smul_le_iff h
                ,
                smul_smul
                ,
                mul_inv_cancel_right₀ right_ne_zero_of_mul h.ne'
                ,
                smul_add
                ,
                smul_inv_smul₀ left_ne_zero_of_mul h.ne'
              ]
          infer_instance
#align map_le_line_map_iff_slope_le_slope_left map_le_line_map_iff_slope_le_slope_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly above the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f a c`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `line_map_le_map_iff_slope_le_slope_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" («term_<_» (num "0") "<" («term_*_» `r "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≤_»
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
          "≤"
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
         "↔"
         («term_≤_»
          (Term.app `slope [`f `a `b])
          "≤"
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `map_le_line_map_iff_slope_le_slope_left)
        [`k
         (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `f
         `a
         `b
         `r
         `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `map_le_line_map_iff_slope_le_slope_left)
       [`k
        (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `f
        `a
        `b
        `r
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `map_le_line_map_iff_slope_le_slope_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_le_line_map_iff_slope_le_slope_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≤_»
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
        "≤"
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
       "↔"
       («term_≤_»
        (Term.app `slope [`f `a `b])
        "≤"
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `slope [`f `a `b])
       "≤"
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly above the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f a c`. -/
  theorem
    line_map_le_map_iff_slope_le_slope_left
    ( h : 0 < r * b - a ) : lineMap f a f b r ≤ f c ↔ slope f a b ≤ slope f a c
    := @ map_le_line_map_iff_slope_le_slope_left k E ᵒᵈ _ _ _ _ f a b r h
#align line_map_le_map_iff_slope_le_slope_left line_map_le_map_iff_slope_le_slope_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly below the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f a b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_lt_line_map_iff_slope_lt_slope_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" («term_<_» (num "0") "<" («term_*_» `r "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "<"
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
         "↔"
         («term_<_»
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "<"
          (Term.app `slope [`f `a `b])))))
      (Command.declValSimple
       ":="
       (Term.app
        `lt_iff_lt_of_le_iff_le'
        [(Term.app `line_map_le_map_iff_slope_le_slope_left [`h])
         (Term.app `map_le_line_map_iff_slope_le_slope_left [`h])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_iff_lt_of_le_iff_le'
       [(Term.app `line_map_le_map_iff_slope_le_slope_left [`h])
        (Term.app `map_le_line_map_iff_slope_le_slope_left [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map_le_line_map_iff_slope_le_slope_left [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_le_line_map_iff_slope_le_slope_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `map_le_line_map_iff_slope_le_slope_left [`h])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `line_map_le_map_iff_slope_le_slope_left [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `line_map_le_map_iff_slope_le_slope_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `line_map_le_map_iff_slope_le_slope_left [`h])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_iff_lt_of_le_iff_le'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "<"
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
       "↔"
       («term_<_»
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "<"
        (Term.app `slope [`f `a `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
       "<"
       (Term.app `slope [`f `a `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly below the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f a b`. -/
  theorem
    map_lt_line_map_iff_slope_lt_slope_left
    ( h : 0 < r * b - a ) : f c < lineMap f a f b r ↔ slope f a c < slope f a b
    :=
      lt_iff_lt_of_le_iff_le'
        line_map_le_map_iff_slope_le_slope_left h map_le_line_map_iff_slope_le_slope_left h
#align map_lt_line_map_iff_slope_lt_slope_left map_lt_line_map_iff_slope_lt_slope_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly above the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f a c`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `line_map_lt_map_iff_slope_lt_slope_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" («term_<_» (num "0") "<" («term_*_» `r "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
          "<"
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
         "↔"
         («term_<_»
          (Term.app `slope [`f `a `b])
          "<"
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope_left)
        [`k
         (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `f
         `a
         `b
         `r
         `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope_left)
       [`k
        (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `f
        `a
        `b
        `r
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_lt_line_map_iff_slope_lt_slope_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
        "<"
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
       "↔"
       («term_<_»
        (Term.app `slope [`f `a `b])
        "<"
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `slope [`f `a `b])
       "<"
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly above the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f a c`. -/
  theorem
    line_map_lt_map_iff_slope_lt_slope_left
    ( h : 0 < r * b - a ) : lineMap f a f b r < f c ↔ slope f a b < slope f a c
    := @ map_lt_line_map_iff_slope_lt_slope_left k E ᵒᵈ _ _ _ _ f a b r h
#align line_map_lt_map_iff_slope_lt_slope_left line_map_lt_map_iff_slope_lt_slope_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly below the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f c b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_le_line_map_iff_slope_le_slope_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (num "0")
           "<"
           («term_*_» («term_-_» (num "1") "-" `r) "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≤_»
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "≤"
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
         "↔"
         («term_≤_»
          (Term.app `slope [`f `a `b])
          "≤"
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `line_map_apply_one_sub)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `line_map_apply_one_sub [(Term.hole "_") (Term.hole "_") `r]))]
             "]")
            [])
           []
           (Tactic.revert "revert" [`h])
           ";"
           (Tactic.generalize
            "generalize"
            [(Tactic.generalizeArg [] («term_-_» (num "1") "-" `r) "=" `r')]
            [])
           ";"
           (Tactic.clear "clear" [`r])
           ";"
           (Tactic.intro "intro" [`h])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `line_map_apply)
              ","
              (Tactic.rwRule [] `slope)
              ","
              (Tactic.rwRule [] `vsub_eq_sub)
              ","
              (Tactic.rwRule [] `vadd_eq_add)
              ","
              (Tactic.rwRule [] `smul_eq_mul)]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `sub_add_eq_sub_sub_swap)
              ","
              (Tactic.rwRule [] `sub_self)
              ","
              (Tactic.rwRule [] `zero_sub)
              ","
              (Tactic.rwRule [] `neg_mul_eq_mul_neg)
              ","
              (Tactic.rwRule [] `neg_sub)
              ","
              (Tactic.rwRule [] (Term.app `le_inv_smul_iff [`h]))
              ","
              (Tactic.rwRule [] `smul_smul)
              ","
              (Tactic.rwRule [] `mul_inv_cancel_right₀)
              ","
              (Tactic.rwRule [] `le_sub_comm)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `neg_sub [(Term.app `f [`b])]))
              ","
              (Tactic.rwRule [] `smul_neg)
              ","
              (Tactic.rwRule [] `neg_add_eq_sub)]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.app `right_ne_zero_of_mul [`h.ne']))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticInfer_instance "infer_instance")])])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `line_map_apply_one_sub)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `line_map_apply_one_sub [(Term.hole "_") (Term.hole "_") `r]))]
            "]")
           [])
          []
          (Tactic.revert "revert" [`h])
          ";"
          (Tactic.generalize
           "generalize"
           [(Tactic.generalizeArg [] («term_-_» (num "1") "-" `r) "=" `r')]
           [])
          ";"
          (Tactic.clear "clear" [`r])
          ";"
          (Tactic.intro "intro" [`h])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `line_map_apply)
             ","
             (Tactic.rwRule [] `slope)
             ","
             (Tactic.rwRule [] `vsub_eq_sub)
             ","
             (Tactic.rwRule [] `vadd_eq_add)
             ","
             (Tactic.rwRule [] `smul_eq_mul)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `sub_add_eq_sub_sub_swap)
             ","
             (Tactic.rwRule [] `sub_self)
             ","
             (Tactic.rwRule [] `zero_sub)
             ","
             (Tactic.rwRule [] `neg_mul_eq_mul_neg)
             ","
             (Tactic.rwRule [] `neg_sub)
             ","
             (Tactic.rwRule [] (Term.app `le_inv_smul_iff [`h]))
             ","
             (Tactic.rwRule [] `smul_smul)
             ","
             (Tactic.rwRule [] `mul_inv_cancel_right₀)
             ","
             (Tactic.rwRule [] `le_sub_comm)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `neg_sub [(Term.app `f [`b])]))
             ","
             (Tactic.rwRule [] `smul_neg)
             ","
             (Tactic.rwRule [] `neg_add_eq_sub)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `right_ne_zero_of_mul [`h.ne']))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticInfer_instance "infer_instance")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticInfer_instance "infer_instance")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `right_ne_zero_of_mul [`h.ne']))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `right_ne_zero_of_mul [`h.ne']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `right_ne_zero_of_mul [`h.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `right_ne_zero_of_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `sub_add_eq_sub_sub_swap)
         ","
         (Tactic.rwRule [] `sub_self)
         ","
         (Tactic.rwRule [] `zero_sub)
         ","
         (Tactic.rwRule [] `neg_mul_eq_mul_neg)
         ","
         (Tactic.rwRule [] `neg_sub)
         ","
         (Tactic.rwRule [] (Term.app `le_inv_smul_iff [`h]))
         ","
         (Tactic.rwRule [] `smul_smul)
         ","
         (Tactic.rwRule [] `mul_inv_cancel_right₀)
         ","
         (Tactic.rwRule [] `le_sub_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `neg_sub [(Term.app `f [`b])]))
         ","
         (Tactic.rwRule [] `smul_neg)
         ","
         (Tactic.rwRule [] `neg_add_eq_sub)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_add_eq_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `neg_sub [(Term.app `f [`b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`b]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `neg_sub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_sub_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_inv_cancel_right₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_inv_smul_iff [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_inv_smul_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_mul_eq_mul_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_add_eq_sub_sub_swap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `line_map_apply)
         ","
         (Tactic.rwRule [] `slope)
         ","
         (Tactic.rwRule [] `vsub_eq_sub)
         ","
         (Tactic.rwRule [] `vadd_eq_add)
         ","
         (Tactic.rwRule [] `smul_eq_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vadd_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vsub_eq_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slope
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `line_map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.clear "clear" [`r])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.generalize
       "generalize"
       [(Tactic.generalizeArg [] («term_-_» (num "1") "-" `r) "=" `r')]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.revert "revert" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `line_map_apply_one_sub)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `line_map_apply_one_sub [(Term.hole "_") (Term.hole "_") `r]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `line_map_apply_one_sub [(Term.hole "_") (Term.hole "_") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `line_map_apply_one_sub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `line_map_apply_one_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≤_»
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "≤"
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
       "↔"
       («term_≤_»
        (Term.app `slope [`f `a `b])
        "≤"
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `slope [`f `a `b])
       "≤"
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly below the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f c b`. -/
  theorem
    map_le_line_map_iff_slope_le_slope_right
    ( h : 0 < 1 - r * b - a ) : f c ≤ lineMap f a f b r ↔ slope f a b ≤ slope f c b
    :=
      by
        rw [ ← line_map_apply_one_sub , ← line_map_apply_one_sub _ _ r ]
          revert h
          ;
          generalize 1 - r = r'
          ;
          clear r
          ;
          intro h
          simp_rw [ line_map_apply , slope , vsub_eq_sub , vadd_eq_add , smul_eq_mul ]
          rw
            [
              sub_add_eq_sub_sub_swap
                ,
                sub_self
                ,
                zero_sub
                ,
                neg_mul_eq_mul_neg
                ,
                neg_sub
                ,
                le_inv_smul_iff h
                ,
                smul_smul
                ,
                mul_inv_cancel_right₀
                ,
                le_sub_comm
                ,
                ← neg_sub f b
                ,
                smul_neg
                ,
                neg_add_eq_sub
              ]
          · exact right_ne_zero_of_mul h.ne'
          · infer_instance
#align map_le_line_map_iff_slope_le_slope_right map_le_line_map_iff_slope_le_slope_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly above the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `line_map_le_map_iff_slope_le_slope_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (num "0")
           "<"
           («term_*_» («term_-_» (num "1") "-" `r) "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≤_»
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
          "≤"
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
         "↔"
         («term_≤_»
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
          "≤"
          (Term.app `slope [`f `a `b])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `map_le_line_map_iff_slope_le_slope_right)
        [`k
         (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `f
         `a
         `b
         `r
         `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `map_le_line_map_iff_slope_le_slope_right)
       [`k
        (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `f
        `a
        `b
        `r
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `map_le_line_map_iff_slope_le_slope_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_le_line_map_iff_slope_le_slope_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≤_»
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
        "≤"
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
       "↔"
       («term_≤_»
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
        "≤"
        (Term.app `slope [`f `a `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
       "≤"
       (Term.app `slope [`f `a `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly above the
    segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a b`. -/
  theorem
    line_map_le_map_iff_slope_le_slope_right
    ( h : 0 < 1 - r * b - a ) : lineMap f a f b r ≤ f c ↔ slope f c b ≤ slope f a b
    := @ map_le_line_map_iff_slope_le_slope_right k E ᵒᵈ _ _ _ _ f a b r h
#align line_map_le_map_iff_slope_le_slope_right line_map_le_map_iff_slope_le_slope_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly below the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_lt_line_map_iff_slope_lt_slope_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (num "0")
           "<"
           («term_*_» («term_-_» (num "1") "-" `r) "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "<"
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
         "↔"
         («term_<_»
          (Term.app `slope [`f `a `b])
          "<"
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))))
      (Command.declValSimple
       ":="
       (Term.app
        `lt_iff_lt_of_le_iff_le'
        [(Term.app `line_map_le_map_iff_slope_le_slope_right [`h])
         (Term.app `map_le_line_map_iff_slope_le_slope_right [`h])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_iff_lt_of_le_iff_le'
       [(Term.app `line_map_le_map_iff_slope_le_slope_right [`h])
        (Term.app `map_le_line_map_iff_slope_le_slope_right [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map_le_line_map_iff_slope_le_slope_right [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_le_line_map_iff_slope_le_slope_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `map_le_line_map_iff_slope_le_slope_right [`h])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `line_map_le_map_iff_slope_le_slope_right [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `line_map_le_map_iff_slope_le_slope_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `line_map_le_map_iff_slope_le_slope_right [`h])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_iff_lt_of_le_iff_le'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "<"
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
       "↔"
       («term_<_»
        (Term.app `slope [`f `a `b])
        "<"
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `slope [`f `a `b])
       "<"
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly below the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`. -/
  theorem
    map_lt_line_map_iff_slope_lt_slope_right
    ( h : 0 < 1 - r * b - a ) : f c < lineMap f a f b r ↔ slope f a b < slope f c b
    :=
      lt_iff_lt_of_le_iff_le'
        line_map_le_map_iff_slope_le_slope_right h map_le_line_map_iff_slope_le_slope_right h
#align map_lt_line_map_iff_slope_lt_slope_right map_lt_line_map_iff_slope_lt_slope_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly above the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `line_map_lt_map_iff_slope_lt_slope_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (num "0")
           "<"
           («term_*_» («term_-_» (num "1") "-" `r) "*" («term_-_» `b "-" `a)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
          "<"
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
         "↔"
         («term_<_»
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
          "<"
          (Term.app `slope [`f `a `b])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope_right)
        [`k
         (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `f
         `a
         `b
         `r
         `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope_right)
       [`k
        (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `f
        `a
        `b
        `r
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_lt_line_map_iff_slope_lt_slope_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
        "<"
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
       "↔"
       («term_<_»
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
        "<"
        (Term.app `slope [`f `a `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
       "<"
       (Term.app `slope [`f `a `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly above the
    segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a b`. -/
  theorem
    line_map_lt_map_iff_slope_lt_slope_right
    ( h : 0 < 1 - r * b - a ) : lineMap f a f b r < f c ↔ slope f c b < slope f a b
    := @ map_lt_line_map_iff_slope_lt_slope_right k E ᵒᵈ _ _ _ _ f a b r h
#align line_map_lt_map_iff_slope_lt_slope_right line_map_lt_map_iff_slope_lt_slope_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly below the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f c b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_le_line_map_iff_slope_le_slope [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hab] [":" («term_<_» `a "<" `b)] [] ")")
        (Term.explicitBinder "(" [`h₀] [":" («term_<_» (num "0") "<" `r)] [] ")")
        (Term.explicitBinder "(" [`h₁] [":" («term_<_» `r "<" (num "1"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≤_»
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "≤"
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
         "↔"
         («term_≤_»
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "≤"
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `map_le_line_map_iff_slope_le_slope_left
                [(Term.app
                  `mul_pos
                  [`h₀ (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab])])]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `line_map_slope_line_map_slope_line_map [`f `a `b `r]))
              ","
              (Tactic.rwRule [] (Term.app `right_le_line_map_iff_le [`h₁]))]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `map_le_line_map_iff_slope_le_slope_left
               [(Term.app
                 `mul_pos
                 [`h₀ (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab])])]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `line_map_slope_line_map_slope_line_map [`f `a `b `r]))
             ","
             (Tactic.rwRule [] (Term.app `right_le_line_map_iff_le [`h₁]))]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `map_le_line_map_iff_slope_le_slope_left
           [(Term.app `mul_pos [`h₀ (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab])])]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `line_map_slope_line_map_slope_line_map [`f `a `b `r]))
         ","
         (Tactic.rwRule [] (Term.app `right_le_line_map_iff_le [`h₁]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `right_le_line_map_iff_le [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `right_le_line_map_iff_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `line_map_slope_line_map_slope_line_map [`f `a `b `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `line_map_slope_line_map_slope_line_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `map_le_line_map_iff_slope_le_slope_left
       [(Term.app `mul_pos [`h₀ (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_pos [`h₀ (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `sub_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sub_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_pos
      [`h₀ (Term.paren "(" (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [`hab]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_le_line_map_iff_slope_le_slope_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≤_»
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "≤"
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
       "↔"
       («term_≤_»
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "≤"
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
       "≤"
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly below the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f c b`. -/
  theorem
    map_le_line_map_iff_slope_le_slope
    ( hab : a < b ) ( h₀ : 0 < r ) ( h₁ : r < 1 )
      : f c ≤ lineMap f a f b r ↔ slope f a c ≤ slope f c b
    :=
      by
        rw
            [
              map_le_line_map_iff_slope_le_slope_left mul_pos h₀ sub_pos . 2 hab
                ,
                ← line_map_slope_line_map_slope_line_map f a b r
                ,
                right_le_line_map_iff_le h₁
              ]
          infer_instance
          infer_instance
#align map_le_line_map_iff_slope_le_slope map_le_line_map_iff_slope_le_slope

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly above the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a c`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `line_map_le_map_iff_slope_le_slope [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hab] [":" («term_<_» `a "<" `b)] [] ")")
        (Term.explicitBinder "(" [`h₀] [":" («term_<_» (num "0") "<" `r)] [] ")")
        (Term.explicitBinder "(" [`h₁] [":" («term_<_» `r "<" (num "1"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_≤_»
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
          "≤"
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
         "↔"
         («term_≤_»
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
          "≤"
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `map_le_line_map_iff_slope_le_slope)
        [`k
         (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `hab
         `h₀
         `h₁])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `map_le_line_map_iff_slope_le_slope)
       [`k
        (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `hab
        `h₀
        `h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `map_le_line_map_iff_slope_le_slope)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_le_line_map_iff_slope_le_slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_≤_»
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
        "≤"
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
       "↔"
       («term_≤_»
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
        "≤"
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
       "≤"
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly above the
    segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a c`. -/
  theorem
    line_map_le_map_iff_slope_le_slope
    ( hab : a < b ) ( h₀ : 0 < r ) ( h₁ : r < 1 )
      : lineMap f a f b r ≤ f c ↔ slope f c b ≤ slope f a c
    := @ map_le_line_map_iff_slope_le_slope k E ᵒᵈ _ _ _ _ _ _ _ _ hab h₀ h₁
#align line_map_le_map_iff_slope_le_slope line_map_le_map_iff_slope_le_slope

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly below the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f c b`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_lt_line_map_iff_slope_lt_slope [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hab] [":" («term_<_» `a "<" `b)] [] ")")
        (Term.explicitBinder "(" [`h₀] [":" («term_<_» (num "0") "<" `r)] [] ")")
        (Term.explicitBinder "(" [`h₁] [":" («term_<_» `r "<" (num "1"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "<"
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
         "↔"
         («term_<_»
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
          "<"
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))))
      (Command.declValSimple
       ":="
       (Term.app
        `lt_iff_lt_of_le_iff_le'
        [(Term.app `line_map_le_map_iff_slope_le_slope [`hab `h₀ `h₁])
         (Term.app `map_le_line_map_iff_slope_le_slope [`hab `h₀ `h₁])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_iff_lt_of_le_iff_le'
       [(Term.app `line_map_le_map_iff_slope_le_slope [`hab `h₀ `h₁])
        (Term.app `map_le_line_map_iff_slope_le_slope [`hab `h₀ `h₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map_le_line_map_iff_slope_le_slope [`hab `h₀ `h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_le_line_map_iff_slope_le_slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `map_le_line_map_iff_slope_le_slope [`hab `h₀ `h₁])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `line_map_le_map_iff_slope_le_slope [`hab `h₀ `h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `line_map_le_map_iff_slope_le_slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `line_map_le_map_iff_slope_le_slope [`hab `h₀ `h₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_iff_lt_of_le_iff_le'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "<"
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r]))
       "↔"
       («term_<_»
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
        "<"
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
       "<"
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly below the
    segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f c b`. -/
  theorem
    map_lt_line_map_iff_slope_lt_slope
    ( hab : a < b ) ( h₀ : 0 < r ) ( h₁ : r < 1 )
      : f c < lineMap f a f b r ↔ slope f a c < slope f c b
    :=
      lt_iff_lt_of_le_iff_le'
        line_map_le_map_iff_slope_le_slope hab h₀ h₁ map_le_line_map_iff_slope_le_slope hab h₀ h₁
#align map_lt_line_map_iff_slope_lt_slope map_lt_line_map_iff_slope_lt_slope

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly above the\nsegment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a c`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `line_map_lt_map_iff_slope_lt_slope [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hab] [":" («term_<_» `a "<" `b)] [] ")")
        (Term.explicitBinder "(" [`h₀] [":" («term_<_» (num "0") "<" `r)] [] ")")
        (Term.explicitBinder "(" [`h₁] [":" («term_<_» `r "<" (num "1"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
          "<"
          (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
         "↔"
         («term_<_»
          (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
          "<"
          (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope)
        [`k
         (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         `hab
         `h₀
         `h₁])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope)
       [`k
        (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `hab
        `h₀
        `h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_ᵒᵈ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Order.Basic.«term_ᵒᵈ» `E "ᵒᵈ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `map_lt_line_map_iff_slope_lt_slope)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_lt_line_map_iff_slope_lt_slope
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.app `lineMap [(Term.app `f [`a]) (Term.app `f [`b]) `r])
        "<"
        (Term.app `f [(LinearAlgebra.AffineSpace.Ordered.termc "c")]))
       "↔"
       («term_<_»
        (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
        "<"
        (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `slope [`f (LinearAlgebra.AffineSpace.Ordered.termc "c") `b])
       "<"
       (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slope [`f `a (LinearAlgebra.AffineSpace.Ordered.termc "c")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LinearAlgebra.AffineSpace.Ordered.termc "c")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LinearAlgebra.AffineSpace.Ordered.termc', expected 'LinearAlgebra.AffineSpace.Ordered.termc._@.LinearAlgebra.AffineSpace.Ordered._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly above the
    segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a c`. -/
  theorem
    line_map_lt_map_iff_slope_lt_slope
    ( hab : a < b ) ( h₀ : 0 < r ) ( h₁ : r < 1 )
      : lineMap f a f b r < f c ↔ slope f c b < slope f a c
    := @ map_lt_line_map_iff_slope_lt_slope k E ᵒᵈ _ _ _ _ _ _ _ _ hab h₀ h₁
#align line_map_lt_map_iff_slope_lt_slope line_map_lt_map_iff_slope_lt_slope

end LinearOrderedField

