import Mathbin.Algebra.Ring.Basic

/-!
# Fields and division rings

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `field_theory` folder.

## Main definitions

* `division_ring`: introduces the notion of a division ring as a `ring` such that `0 ≠ 1` and
  `a * a⁻¹ = 1` for `a ≠ 0`
* `field`: a division ring which is also a commutative ring.
* `is_field`: a predicate on a ring that it is a field, i.e. that the multiplication is commutative,
  that it has more than one element and that all non-zero elements have a multiplicative inverse.
  In contrast to `field`, which contains the data of a function associating to an element of the
  field its multiplicative inverse, this predicate only assumes the existence and can therefore more
  easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `group_with_zero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `group_with_zero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/


open Set

universe u

variable {K : Type u}

/--  A `division_ring` is a `ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor Ringₓ DivInvMonoidₓ Nontrivial]
class DivisionRing (K : Type u) extends Ringₓ K, DivInvMonoidₓ K, Nontrivial K where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → (a*a⁻¹) = 1
  inv_zero : (0 : K)⁻¹ = 0

section DivisionRing

variable [DivisionRing K] {a b : K}

/--  Every division ring is a `group_with_zero`. -/
instance (priority := 100) DivisionRing.toGroupWithZero : GroupWithZeroₓ K :=
  { ‹DivisionRing K›, (inferInstance : Semiringₓ K) with }

attribute [field_simps] inv_eq_one_div

attribute [local simp] division_def mul_commₓ mul_assocₓ mul_left_commₓ mul_inv_cancel inv_mul_cancel

theorem one_div_neg_one_eq_neg_one : (1 : K) / -1 = -1 :=
  have : ((-1)*-1) = (1 : K) := by
    rw [neg_mul_neg, one_mulₓ]
  Eq.symm (eq_one_div_of_mul_eq_one this)

theorem one_div_neg_eq_neg_one_div (a : K) : 1 / -a = -(1 / a) :=
  calc 1 / -a = 1 / (-1)*a := by
    rw [neg_eq_neg_one_mul]
    _ = (1 / a)*1 / -1 := by
    rw [one_div_mul_one_div_rev]
    _ = (1 / a)*-1 := by
    rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by
    rw [mul_neg_eq_neg_mul_symm, mul_oneₓ]
    

theorem div_neg_eq_neg_div (a b : K) : b / -a = -(b / a) :=
  calc b / -a = b*1 / -a := by
    rw [← inv_eq_one_div, division_def]
    _ = b*-(1 / a) := by
    rw [one_div_neg_eq_neg_one_div]
    _ = -b*1 / a := by
    rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by
    rw [mul_one_div]
    

theorem neg_div (a b : K) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps]
theorem neg_div' (a b : K) : -(b / a) = -b / a := by
  simp [neg_div]

theorem neg_div_neg_eq (a b : K) : -a / -b = a / b := by
  rw [div_neg_eq_neg_div, neg_div, neg_negₓ]

@[field_simps]
theorem div_add_div_same (a b c : K) : ((a / c)+b / c) = (a+b) / c := by
  simpa only [div_eq_mul_inv] using (right_distrib a b (c⁻¹)).symm

theorem same_add_div {a b : K} (h : b ≠ 0) : (b+a) / b = 1+a / b := by
  simpa only [← @div_self _ _ b h] using (div_add_div_same b a b).symm

theorem one_add_div {a b : K} (h : b ≠ 0) : (1+a / b) = (b+a) / b :=
  (same_add_div h).symm

theorem div_add_same {a b : K} (h : b ≠ 0) : (a+b) / b = (a / b)+1 := by
  simpa only [← @div_self _ _ b h] using (div_add_div_same a b b).symm

theorem div_add_one {a b : K} (h : b ≠ 0) : ((a / b)+1) = (a+b) / b :=
  (div_add_same h).symm

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  (same_sub_div h).symm

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  (div_sub_same h).symm

theorem neg_inv : -a⁻¹ = (-a)⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

theorem add_div (a b c : K) : (a+b) / c = (a / c)+b / c :=
  (div_add_div_same _ _ _).symm

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm

theorem div_neg (a : K) : a / -b = -(a / b) := by
  rw [← div_neg_eq_neg_div]

theorem inv_neg : (-a)⁻¹ = -a⁻¹ := by
  rw [neg_inv]

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    (((1 / a)*a+b)*1 / b) = (1 / a)+1 / b := by
  rw [left_distrib (1 / a), one_div_mul_cancel ha, right_distrib, one_mulₓ, mul_assocₓ, mul_one_div_cancel hb, mul_oneₓ,
    add_commₓ]

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    (((1 / a)*b - a)*1 / b) = 1 / a - 1 / b := by
  rw [mul_sub_left_distrib (1 / a), one_div_mul_cancel ha, mul_sub_right_distrib, one_mulₓ, mul_assocₓ,
    mul_one_div_cancel hb, mul_oneₓ]

theorem add_div_eq_mul_add_div (a b : K) {c : K} (hc : c ≠ 0) : (a+b / c) = ((a*c)+b) / c :=
  (eq_div_iff_mul_eq hc).2 $ by
    rw [right_distrib, div_mul_cancel _ hc]

instance (priority := 100) DivisionRing.is_domain : IsDomain K :=
  { ‹DivisionRing K›,
    (by
      infer_instance : NoZeroDivisors K) with }

end DivisionRing

/--  A `field` is a `comm_ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor CommRingₓ DivInvMonoidₓ Nontrivial]
class Field (K : Type u) extends CommRingₓ K, DivInvMonoidₓ K, Nontrivial K where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → (a*a⁻¹) = 1
  inv_zero : (0 : K)⁻¹ = 0

section Field

variable [Field K]

instance (priority := 100) Field.toDivisionRing : DivisionRing K :=
  { show Field K by
      infer_instance with }

/--  Every field is a `comm_group_with_zero`. -/
instance (priority := 100) Field.toCommGroupWithZero : CommGroupWithZero K :=
  { (_ : GroupWithZeroₓ K), ‹Field K› with }

attribute [local simp] mul_assocₓ mul_commₓ mul_left_commₓ

theorem div_add_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) : ((a / b)+c / d) = ((a*d)+b*c) / b*d :=
  by
  rw [← mul_div_mul_right _ b hd, ← mul_div_mul_left c d hb, div_add_div_same]

theorem one_div_add_one_div {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : ((1 / a)+1 / b) = (a+b) / a*b := by
  rw [div_add_div _ _ ha hb, one_mulₓ, mul_oneₓ, add_commₓ]

@[field_simps]
theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) : a / b - c / d = ((a*d) - b*c) / b*d :=
  by
  simp only [sub_eq_add_neg]
  rw [neg_eq_neg_one_mul, ← mul_div_assoc, div_add_div _ _ hb hd, ← mul_assocₓ, mul_commₓ b, mul_assocₓ, ←
    neg_eq_neg_one_mul]

theorem inv_add_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : (a⁻¹+b⁻¹) = (a+b) / a*b := by
  rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

theorem inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / a*b := by
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mulₓ, mul_oneₓ]

@[field_simps]
theorem add_div' (a b c : K) (hc : c ≠ 0) : (b+a / c) = ((b*c)+a) / c := by
  simpa using div_add_div b a one_ne_zero hc

@[field_simps]
theorem sub_div' (a b c : K) (hc : c ≠ 0) : b - a / c = ((b*c) - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc

@[field_simps]
theorem div_add' (a b c : K) (hc : c ≠ 0) : ((a / c)+b) = (a+b*c) / c := by
  rwa [add_commₓ, add_div', add_commₓ]

@[field_simps]
theorem div_sub' (a b c : K) (hc : c ≠ 0) : a / c - b = (a - c*b) / c := by
  simpa using div_sub_div a b hc one_ne_zero

instance (priority := 100) Field.is_domain : IsDomain K :=
  { DivisionRing.is_domain with }

end Field

section IsField

/--  A predicate to express that a ring is a field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a field. -/
structure IsField (R : Type u) [Ringₓ R] : Prop where
  exists_pair_ne : ∃ x y : R, x ≠ y
  mul_comm : ∀ x y : R, (x*y) = y*x
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, (a*b) = 1

/--  Transferring from field to is_field -/
theorem Field.to_is_field (R : Type u) [Field R] : IsField R :=
  { ‹Field R› with mul_inv_cancel := fun a ha => ⟨a⁻¹, Field.mul_inv_cancel ha⟩ }

open_locale Classical

/--  Transferring from is_field to field -/
noncomputable def IsField.toField (R : Type u) [Ringₓ R] (h : IsField R) : Field R :=
  { ‹Ringₓ R›, h with inv := fun a => if ha : a = 0 then 0 else Classical.some (IsField.mul_inv_cancel h ha),
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a ha => by
      convert Classical.some_spec (IsField.mul_inv_cancel h ha)
      exact dif_neg ha }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " For each field, and for each nonzero element of said field, there is a unique inverse.\nSince `is_field` doesn't remember the data of an `inv` function and as such,\na lemma that there is a unique inverse could be useful.\n-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `uniq_inv_of_is_field [])
  (Command.declSig
   [(Term.explicitBinder "(" [`R] [":" (Term.type "Type" [`u])] [] ")")
    (Term.instBinder "[" [] (Term.app `Ringₓ [`R]) "]")
    (Term.explicitBinder "(" [`hf] [":" (Term.app `IsField [`R])] [] ")")]
   (Term.typeSpec
    ":"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `R)])]
     ","
     (Term.arrow
      («term_≠_» `x "≠" (numLit "0"))
      "→"
      (Init.Logic.«term∃!_,_»
       "∃!"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `R]))
       ", "
       («term_=_» (Init.Logic.«term_*_» `x "*" `y) "=" (numLit "1")))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.intro "intro" [`x `hx]) [])
       (group (Tactic.apply "apply" `exists_unique_of_exists_of_unique) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `hf.mul_inv_cancel [`hx])) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`y `z `hxy `hxz]) [])
            (group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_=_» `y "=" (Init.Logic.«term_*_» `y "*" (Init.Logic.«term_*_» `x "*" `z)))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxz) "," (Tactic.rwRule [] `mul_oneₓ)] "]")
                      [])
                     [])]))))
               (calcStep
                («term_=_» (Term.hole "_") "=" (Init.Logic.«term_*_» (Init.Logic.«term_*_» `x "*" `y) "*" `z))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule ["←"] `mul_assocₓ) "," (Tactic.rwRule [] (Term.app `hf.mul_comm [`y `x]))]
                       "]")
                      [])
                     [])]))))
               (calcStep
                («term_=_» (Term.hole "_") "=" `z)
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy) "," (Tactic.rwRule [] `one_mulₓ)] "]")
                      [])
                     [])]))))])
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`x `hx]) [])
      (group (Tactic.apply "apply" `exists_unique_of_exists_of_unique) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `hf.mul_inv_cancel [`hx])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`y `z `hxy `hxz]) [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_=_» `y "=" (Init.Logic.«term_*_» `y "*" (Init.Logic.«term_*_» `x "*" `z)))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxz) "," (Tactic.rwRule [] `mul_oneₓ)] "]")
                     [])
                    [])]))))
              (calcStep
               («term_=_» (Term.hole "_") "=" (Init.Logic.«term_*_» (Init.Logic.«term_*_» `x "*" `y) "*" `z))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] `mul_assocₓ) "," (Tactic.rwRule [] (Term.app `hf.mul_comm [`y `x]))]
                      "]")
                     [])
                    [])]))))
              (calcStep
               («term_=_» (Term.hole "_") "=" `z)
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy) "," (Tactic.rwRule [] `one_mulₓ)] "]")
                     [])
                    [])]))))])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`y `z `hxy `hxz]) [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_» `y "=" (Init.Logic.«term_*_» `y "*" (Init.Logic.«term_*_» `x "*" `z)))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxz) "," (Tactic.rwRule [] `mul_oneₓ)] "]")
                [])
               [])]))))
         (calcStep
          («term_=_» (Term.hole "_") "=" (Init.Logic.«term_*_» (Init.Logic.«term_*_» `x "*" `y) "*" `z))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `mul_assocₓ) "," (Tactic.rwRule [] (Term.app `hf.mul_comm [`y `x]))]
                 "]")
                [])
               [])]))))
         (calcStep
          («term_=_» (Term.hole "_") "=" `z)
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy) "," (Tactic.rwRule [] `one_mulₓ)] "]")
                [])
               [])]))))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_» `y "=" (Init.Logic.«term_*_» `y "*" (Init.Logic.«term_*_» `x "*" `z)))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxz) "," (Tactic.rwRule [] `mul_oneₓ)] "]")
           [])
          [])]))))
    (calcStep
     («term_=_» (Term.hole "_") "=" (Init.Logic.«term_*_» (Init.Logic.«term_*_» `x "*" `y) "*" `z))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `mul_assocₓ) "," (Tactic.rwRule [] (Term.app `hf.mul_comm [`y `x]))]
            "]")
           [])
          [])]))))
    (calcStep
     («term_=_» (Term.hole "_") "=" `z)
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy) "," (Tactic.rwRule [] `one_mulₓ)] "]")
           [])
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy) "," (Tactic.rwRule [] `one_mulₓ)] "]") [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy) "," (Tactic.rwRule [] `one_mulₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_mulₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hxy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" `z)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `mul_assocₓ) "," (Tactic.rwRule [] (Term.app `hf.mul_comm [`y `x]))]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `mul_assocₓ) "," (Tactic.rwRule [] (Term.app `hf.mul_comm [`y `x]))] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf.mul_comm [`y `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf.mul_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Init.Logic.«term_*_» (Init.Logic.«term_*_» `x "*" `y) "*" `z))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_*_» (Init.Logic.«term_*_» `x "*" `y) "*" `z)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Init.Logic.«term_*_» `x "*" `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_*_» `x "*" `y) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxz) "," (Tactic.rwRule [] `mul_oneₓ)] "]") [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxz) "," (Tactic.rwRule [] `mul_oneₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_oneₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hxz
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `y "=" (Init.Logic.«term_*_» `y "*" (Init.Logic.«term_*_» `x "*" `z)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_*_» `y "*" (Init.Logic.«term_*_» `x "*" `z))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_*_» `x "*" `z)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`y `z `hxy `hxz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hxz
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hxy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `hf.mul_inv_cancel [`hx])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `hf.mul_inv_cancel [`hx]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf.mul_inv_cancel [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf.mul_inv_cancel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `exists_unique_of_exists_of_unique)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exists_unique_of_exists_of_unique
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `R)])]
   ","
   (Term.arrow
    («term_≠_» `x "≠" (numLit "0"))
    "→"
    (Init.Logic.«term∃!_,_»
     "∃!"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `R]))
     ", "
     («term_=_» (Init.Logic.«term_*_» `x "*" `y) "=" (numLit "1")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   («term_≠_» `x "≠" (numLit "0"))
   "→"
   (Init.Logic.«term∃!_,_»
    "∃!"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `R]))
    ", "
    («term_=_» (Init.Logic.«term_*_» `x "*" `y) "=" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term∃!_,_»
   "∃!"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [":" `R]))
   ", "
   («term_=_» (Init.Logic.«term_*_» `x "*" `y) "=" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term∃!_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Init.Logic.«term_*_» `x "*" `y) "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Logic.«term_*_» `x "*" `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_*_» `x "*" `y) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For each field, and for each nonzero element of said field, there is a unique inverse.
    Since `is_field` doesn't remember the data of an `inv` function and as such,
    a lemma that there is a unique inverse could be useful.
    -/
  theorem
    uniq_inv_of_is_field
    ( R : Type u ) [ Ringₓ R ] ( hf : IsField R ) : ∀ x : R , x ≠ 0 → ∃! y : R , x * y = 1
    :=
      by
        intro x hx
          apply exists_unique_of_exists_of_unique
          · exact hf.mul_inv_cancel hx
          ·
            intro y z hxy hxz
              calc
                y = y * x * z := by rw [ hxz , mul_oneₓ ]
                  _ = x * y * z := by rw [ ← mul_assocₓ , hf.mul_comm y x ]
                  _ = z := by rw [ hxy , one_mulₓ ]

end IsField

namespace RingHom

section

variable {R : Type _} [Semiringₓ R] [DivisionRing K] (f : R →+* K)

@[simp]
theorem map_units_inv (u : Units R) : f (↑u⁻¹) = f (↑u)⁻¹ :=
  (f : R →* K).map_units_inv u

end

section

variable {R K' : Type _} [DivisionRing K] [Semiringₓ R] [Nontrivial R] [DivisionRing K'] (f : K →+* R) (g : K →+* K')
  {x y : K}

theorem map_ne_zero : f x ≠ 0 ↔ x ≠ 0 :=
  f.to_monoid_with_zero_hom.map_ne_zero

@[simp]
theorem map_eq_zero : f x = 0 ↔ x = 0 :=
  f.to_monoid_with_zero_hom.map_eq_zero

variable (x y)

theorem map_inv : g (x⁻¹) = g x⁻¹ :=
  g.to_monoid_with_zero_hom.map_inv x

theorem map_div : g (x / y) = g x / g y :=
  g.to_monoid_with_zero_hom.map_div x y

protected theorem injective : Function.Injective f :=
  f.injective_iff.2 $ fun x => f.map_eq_zero.1

end

end RingHom

section NoncomputableDefs

variable {R : Type _} [Nontrivial R]

/--  Constructs a `division_ring` structure on a `ring` consisting only of units and 0. -/
noncomputable def divisionRingOfIsUnitOrEqZero [hR : Ringₓ R] (h : ∀ a : R, IsUnit a ∨ a = 0) : DivisionRing R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }

/--  Constructs a `field` structure on a `comm_ring` consisting only of units and 0. -/
noncomputable def fieldOfIsUnitOrEqZero [hR : CommRingₓ R] (h : ∀ a : R, IsUnit a ∨ a = 0) : Field R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }

end NoncomputableDefs

/--  Pullback a `division_ring` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.divisionRing [DivisionRing K] {K'} [HasZero K'] [Mul K'] [Add K'] [Neg K'] [Sub K']
    [HasOne K'] [HasInv K'] [Div K'] (f : K' → K) (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x+y) = f x+f y) (mul : ∀ x y, f (x*y) = f x*f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
    DivisionRing K' :=
  { hf.group_with_zero f zero one mul inv div, hf.ring f zero one add mul neg sub with }

/--  Pullback a `field` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.field [Field K] {K'} [HasZero K'] [Mul K'] [Add K'] [Neg K'] [Sub K'] [HasOne K']
    [HasInv K'] [Div K'] (f : K' → K) (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x+y) = f x+f y) (mul : ∀ x y, f (x*y) = f x*f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) : Field K' :=
  { hf.comm_group_with_zero f zero one mul inv div, hf.comm_ring f zero one add mul neg sub with }

