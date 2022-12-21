/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module tactic.zify
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Data.Int.CharZero
import Mathbin.Tactic.NormCast

/-!
# A tactic to shift `ℕ` goals to `ℤ`

It is often easier to work in `ℤ`, where subtraction is well behaved, than in `ℕ` where it isn't.
`zify` is a tactic that casts goals and hypotheses about natural numbers to ones about integers.
It makes use of `push_cast`, part of the `norm_cast` family, to simplify these goals.

## Implementation notes

`zify` is extensible, using the attribute `@[zify]` to label lemmas used for moving propositions
from `ℕ` to `ℤ`.
`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.

`zify` is very nearly just `simp only with zify push_cast`. There are a few minor differences:
* `zify` lemmas are used in the opposite order of the standard simp form.
  E.g. we will rewrite with `int.coe_nat_le_coe_nat_iff` from right to left.
* `zify` should fail if no `zify` lemma applies (i.e. it was unable to shift any proposition to ℤ).
  However, once this succeeds, it does not necessarily need to rewrite with any `push_cast` rules.
-/


-- used by clients
-- used by clients
open Tactic

namespace Zify

/-- The `zify` attribute is used by the `zify` tactic. It applies to lemmas that shift propositions
between `nat` and `int`.

`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.
-/
@[user_attribute]
unsafe def zify_attr :
    user_attribute simp_lemmas Unit where 
  Name := `zify
  descr := "Used to tag lemmas for use in the `zify` tactic"
  cache_cfg :=
    { mk_cache := fun ns =>
        mapM
            (fun n => do
              let c ← mk_const n
              return (c, tt))
            ns >>=
          simp_lemmas.mk.append_with_symm
      dependencies := [] }
#align zify.zify_attr zify.zify_attr

/-- Given an expression `e`, `lift_to_z e` looks for subterms of `e` that are propositions "about"
natural numbers and change them to propositions about integers.

Returns an expression `e'` and a proof that `e = e'`.

Includes `ge_iff_le` and `gt_iff_lt` in the simp set. These can't be tagged with `zify` as we
want to use them in the "forward", not "backward", direction.
-/
unsafe def lift_to_z (e : expr) : tactic (expr × expr) := do
  let sl ← zify_attr.get_cache
  let sl ← sl.add_simp `ge_iff_le
  let sl ← sl.add_simp `gt_iff_lt
  let (e', prf, _) ← simplify sl [] e
  return (e', prf)
#align zify.lift_to_z zify.lift_to_z

attribute [zify] Int.ofNat_le Int.ofNat_lt Int.ofNat_inj

end Zify

@[zify]
theorem Int.coe_nat_ne_coe_nat_iff (a b : ℕ) : (a : ℤ) ≠ b ↔ a ≠ b := by simp
#align int.coe_nat_ne_coe_nat_iff Int.coe_nat_ne_coe_nat_iff

/-- `zify extra_lems e` is used to shift propositions in `e` from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

The list of extra lemmas is used in the `push_cast` step.

Returns an expression `e'` and a proof that `e = e'`.-/
unsafe def tactic.zify (extra_lems : List simp_arg_type) : expr → tactic (expr × expr) := fun z =>
  do
  let (z1, p1) ← zify.lift_to_z z <|> fail "failed to find an applicable zify lemma"
  let (z2, p2) ← norm_cast.derive_push_cast extra_lems z1
  Prod.mk z2 <$> mk_eq_trans p1 p2
#align tactic.zify tactic.zify

/-- A variant of `tactic.zify` that takes `h`, a proof of a proposition about natural numbers,
and returns a proof of the zified version of that propositon.
-/
unsafe def tactic.zify_proof (extra_lems : List simp_arg_type) (h : expr) : tactic expr := do
  let (_, pf) ← infer_type h >>= tactic.zify extra_lems
  mk_eq_mp pf h
#align tactic.zify_proof tactic.zify_proof

section

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

```lean
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b :=
begin
  zify,
  zify at h,
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
end
```

`zify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : false :=
begin
  zify [hab] at h,
  /- h : ↑a - ↑b < ↑c -/
end
```

`zify` makes use of the `@[zify]` attribute to move propositions,
and the `push_cast` tactic to simplify the `ℤ`-valued expressions.

`zify` is in some sense dual to the `lift` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
unsafe def tactic.interactive.zify (sl : parse simp_arg_list) (l : parse location) : tactic Unit :=
  do
  let locs ← l.get_locals
  replace_at (tactic.zify sl) locs l >>= guardb
#align tactic.interactive.zify tactic.interactive.zify

end

add_tactic_doc
  { Name := "zify"
    category := DocCategory.attr
    declNames := [`zify.zify_attr]
    tags := ["coercions", "transport"] }

add_tactic_doc
  { Name := "zify"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.zify]
    tags := ["coercions", "transport"] }

