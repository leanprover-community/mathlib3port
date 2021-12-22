import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Data.Real.Basic
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Nonneg

/-!
# Nonnegative real numbers

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `ordered_comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `canonically_linear_ordered_add_monoid ℝ≥0`;
  - `archimedean ℝ≥0`;
  - `conditionally_complete_linear_order_bot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`. See `algebra/order/nonneg`.

* `real.to_nnreal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(real.to_nnreal x) = x` when `0 ≤ x` and
  `↑(real.to_nnreal x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.
-/


open_locale Classical BigOperators

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler ordered_semiring
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler comm_monoid_with_zero
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler semilattice_inf
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler densely_ordered
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler order_bot
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler canonically_linear_ordered_add_monoid
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler linear_ordered_comm_group_with_zero
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler archimedean
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler linear_ordered_semiring
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler ordered_comm_semiring
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler canonically_ordered_comm_semiring
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler has_sub
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler has_ordered_sub
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler has_div
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler inhabited
/--  Nonnegative real numbers. -/
def Nnreal :=
  { r : ℝ // 0 ≤ r }deriving [anonymous], [anonymous], [anonymous], [anonymous], [anonymous], [anonymous], [anonymous],
  [anonymous], [anonymous], [anonymous], [anonymous], [anonymous], [anonymous], [anonymous], [anonymous]

localized [Nnreal] notation " ℝ≥0 " => Nnreal

namespace Nnreal

instance : Coe ℝ≥0 ℝ :=
  ⟨Subtype.val⟩

@[simp]
theorem val_eq_coe (n : ℝ≥0 ) : n.val = n :=
  rfl

-- failed to format: format: uncaught backtrack exception
instance : CanLift ℝ ℝ≥0 where coe := coeₓ cond r := 0 ≤ r prf x hx := ⟨ ⟨ x , hx ⟩ , rfl ⟩

protected theorem Eq {n m : ℝ≥0 } : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.eq

protected theorem eq_iff {n m : ℝ≥0 } : (n : ℝ) = (m : ℝ) ↔ n = m :=
  Iff.intro Nnreal.eq (congr_argₓ coeₓ)

theorem ne_iff {x y : ℝ≥0 } : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_iff_not_of_iff $ Nnreal.eq_iff

/--  Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
noncomputable def _root_.real.to_nnreal (r : ℝ) : ℝ≥0 :=
  ⟨max r 0, le_max_rightₓ _ _⟩

theorem _root_.real.coe_to_nnreal (r : ℝ) (hr : 0 ≤ r) : (Real.toNnreal r : ℝ) = r :=
  max_eq_leftₓ hr

theorem _root_.real.le_coe_to_nnreal (r : ℝ) : r ≤ Real.toNnreal r :=
  le_max_leftₓ r 0

theorem coe_nonneg (r : ℝ≥0 ) : (0 : ℝ) ≤ r :=
  r.2

@[norm_cast]
theorem coe_mk (a : ℝ) ha : ((⟨a, ha⟩ : ℝ≥0 ) : ℝ) = a :=
  rfl

example : HasZero ℝ≥0 := by
  infer_instance

example : HasOne ℝ≥0 := by
  infer_instance

example : Add ℝ≥0 := by
  infer_instance

noncomputable example : Sub ℝ≥0 := by
  infer_instance

example : Mul ℝ≥0 := by
  infer_instance

noncomputable example : HasInv ℝ≥0 := by
  infer_instance

noncomputable example : Div ℝ≥0 := by
  infer_instance

noncomputable example : LE ℝ≥0 := by
  infer_instance

example : HasBot ℝ≥0 := by
  infer_instance

example : Inhabited ℝ≥0 := by
  infer_instance

example : Nontrivial ℝ≥0 := by
  infer_instance

protected theorem coe_injective : Function.Injective (coeₓ : ℝ≥0 → ℝ) :=
  Subtype.coe_injective

@[simp, norm_cast]
protected theorem coe_eq {r₁ r₂ : ℝ≥0 } : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
  Nnreal.coe_injective.eq_iff

protected theorem coe_zero : ((0 : ℝ≥0 ) : ℝ) = 0 :=
  rfl

protected theorem coe_one : ((1 : ℝ≥0 ) : ℝ) = 1 :=
  rfl

protected theorem coe_add (r₁ r₂ : ℝ≥0 ) : ((r₁+r₂ : ℝ≥0 ) : ℝ) = r₁+r₂ :=
  rfl

protected theorem coe_mul (r₁ r₂ : ℝ≥0 ) : ((r₁*r₂ : ℝ≥0 ) : ℝ) = r₁*r₂ :=
  rfl

protected theorem coe_inv (r : ℝ≥0 ) : ((r⁻¹ : ℝ≥0 ) : ℝ) = r⁻¹ :=
  rfl

protected theorem coe_div (r₁ r₂ : ℝ≥0 ) : ((r₁ / r₂ : ℝ≥0 ) : ℝ) = r₁ / r₂ :=
  rfl

@[simp, norm_cast]
protected theorem coe_bit0 (r : ℝ≥0 ) : ((bit0 r : ℝ≥0 ) : ℝ) = bit0 r :=
  rfl

@[simp, norm_cast]
protected theorem coe_bit1 (r : ℝ≥0 ) : ((bit1 r : ℝ≥0 ) : ℝ) = bit1 r :=
  rfl

@[simp, norm_cast]
protected theorem coe_sub {r₁ r₂ : ℝ≥0 } (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0 ) : ℝ) = r₁ - r₂ :=
  max_eq_leftₓ $
    le_sub.2 $ by
      simp [show (r₂ : ℝ) ≤ r₁ from h]

@[simp, norm_cast]
protected theorem coe_eq_zero (r : ℝ≥0 ) : ↑r = (0 : ℝ) ↔ r = 0 := by
  rw [← Nnreal.coe_zero, Nnreal.coe_eq]

@[simp, norm_cast]
protected theorem coe_eq_one (r : ℝ≥0 ) : ↑r = (1 : ℝ) ↔ r = 1 := by
  rw [← Nnreal.coe_one, Nnreal.coe_eq]

theorem coe_ne_zero {r : ℝ≥0 } : (r : ℝ) ≠ 0 ↔ r ≠ 0 := by
  norm_cast

example : CommSemiringₓ ℝ≥0 := by
  infer_instance

/--  Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def to_real_hom : ℝ≥0 →+* ℝ :=
  ⟨coeₓ, Nnreal.coe_one, Nnreal.coe_mul, Nnreal.coe_zero, Nnreal.coe_add⟩

@[simp]
theorem coe_to_real_hom : ⇑to_real_hom = coeₓ :=
  rfl

section Actions

/--  A `mul_action` over `ℝ` restricts to a `mul_action` over `ℝ≥0`. -/
instance {M : Type _} [MulAction ℝ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M to_real_hom.toMonoidHom

theorem smul_def {M : Type _} [MulAction ℝ M] (c : ℝ≥0 ) (x : M) : c • x = (c : ℝ) • x :=
  rfl

-- failed to format: format: uncaught backtrack exception
instance
  { M N : Type _ } [ MulAction ℝ M ] [ MulAction ℝ N ] [ HasScalar M N ] [ IsScalarTower ℝ M N ] : IsScalarTower ℝ≥0 M N
  where smul_assoc r := ( smul_assoc ( r : ℝ ) : _ )

-- failed to format: format: uncaught backtrack exception
instance
  smul_comm_class_left
  { M N : Type _ } [ MulAction ℝ N ] [ HasScalar M N ] [ SmulCommClass ℝ M N ] : SmulCommClass ℝ≥0 M N
  where smul_comm r := ( smul_comm ( r : ℝ ) : _ )

-- failed to format: format: uncaught backtrack exception
instance
  smul_comm_class_right
  { M N : Type _ } [ MulAction ℝ N ] [ HasScalar M N ] [ SmulCommClass M ℝ N ] : SmulCommClass M ℝ≥0 N
  where smul_comm m r := ( smul_comm m ( r : ℝ ) : _ )

/--  A `distrib_mul_action` over `ℝ` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
instance {M : Type _} [AddMonoidₓ M] [DistribMulAction ℝ M] : DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M to_real_hom.toMonoidHom

/--  A `module` over `ℝ` restricts to a `module` over `ℝ≥0`. -/
instance {M : Type _} [AddCommMonoidₓ M] [Module ℝ M] : Module ℝ≥0 M :=
  Module.compHom M to_real_hom

-- failed to format: format: uncaught backtrack exception
/-- An `algebra` over `ℝ` restricts to an `algebra` over `ℝ≥0`. -/
  instance
    { A : Type _ } [ Semiringₓ A ] [ Algebra ℝ A ] : Algebra ℝ≥0 A
    where
      smul := · • ·
        commutes' r x := by simp [ Algebra.commutes ]
        smul_def' r x := by simp [ ← Algebra.smul_def ( r : ℝ ) x , smul_def ]
        toRingHom := ( algebraMap ℝ A ) . comp ( to_real_hom : ℝ≥0 →+* ℝ )

example : Algebra ℝ≥0 ℝ := by
  infer_instance

example : DistribMulAction (Units ℝ≥0 ) ℝ := by
  infer_instance

end Actions

example : MonoidWithZeroₓ ℝ≥0 := by
  infer_instance

example : CommMonoidWithZero ℝ≥0 := by
  infer_instance

noncomputable example : CommGroupWithZero ℝ≥0 := by
  infer_instance

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0 ) (a : α) :
    ((s.indicator f a : ℝ≥0 ) : ℝ) = s.indicator (fun x => f x) a :=
  (to_real_hom : ℝ≥0 →+ ℝ).map_indicator _ _ _

@[simp, norm_cast]
theorem coe_pow (r : ℝ≥0 ) (n : ℕ) : ((r ^ n : ℝ≥0 ) : ℝ) = r ^ n :=
  to_real_hom.map_pow r n

@[simp, norm_cast]
theorem coe_zpow (r : ℝ≥0 ) (n : ℤ) : ((r ^ n : ℝ≥0 ) : ℝ) = r ^ n := by
  cases n <;> simp

@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0 ) : ((l.sum : ℝ≥0 ) : ℝ) = (l.map coeₓ).Sum :=
  to_real_hom.map_list_sum l

@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0 ) : ((l.prod : ℝ≥0 ) : ℝ) = (l.map coeₓ).Prod :=
  to_real_hom.map_list_prod l

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0 ) : ((s.sum : ℝ≥0 ) : ℝ) = (s.map coeₓ).Sum :=
  to_real_hom.map_multiset_sum s

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0 ) : ((s.prod : ℝ≥0 ) : ℝ) = (s.map coeₓ).Prod :=
  to_real_hom.map_multiset_prod s

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.normCast "norm_cast" []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `coe_sum [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [] "}")
    (Term.implicitBinder "{" [`s] [":" (Term.app `Finset [`α])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 "))] "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Init.Coe.«term↑_»
      "↑"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
       " in "
       `s
       ", "
       (Term.app `f [`a])))
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))))
  (Command.declValSimple ":=" (Term.app (Term.proj `to_real_hom "." `map_sum) [(Term.hole "_") (Term.hole "_")]) [])
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
  (Term.app (Term.proj `to_real_hom "." `map_sum) [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `to_real_hom "." `map_sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `to_real_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Init.Coe.«term↑_»
    "↑"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
     " in "
     `s
     ", "
     (Term.app `f [`a])))
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    " in "
    `s
    ", "
    (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   " in "
   `s
   ", "
   (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
@[ norm_cast ]
  theorem
    coe_sum
    { α } { s : Finset α } { f : α → ℝ≥0 } : ↑ ∑ a in s , f a = ∑ a in s , ( f a : ℝ )
    := to_real_hom . map_sum _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `_root_.real.to_nnreal_sum_of_nonneg [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [] "}")
    (Term.implicitBinder "{" [`s] [":" (Term.app `Finset [`α])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" (Data.Real.Basic.termℝ "ℝ"))] "}")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`a] [])]
       ","
       (Term.arrow (Init.Core.«term_∈_» `a " ∈ " `s) "→" («term_≤_» (numLit "0") "≤" (Term.app `f [`a]))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Real.toNnreal
      [(Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
        " in "
        `s
        ", "
        (Term.app `f [`a]))])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.app `Real.toNnreal [(Term.app `f [`a])])))))
  (Command.declValSimple
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
          [(Tactic.rwRule ["←"] `Nnreal.coe_eq)
           ","
           (Tactic.rwRule [] `Nnreal.coe_sum)
           ","
           (Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.sum_nonneg [`hf])]))]
          "]")
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `Finset.sum_congr
          [`rfl
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x `hxs] [])]
             "=>"
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
                    [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
                    "]")
                   [])
                  [])])))))]))
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
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `Nnreal.coe_eq)
          ","
          (Tactic.rwRule [] `Nnreal.coe_sum)
          ","
          (Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.sum_nonneg [`hf])]))]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `Finset.sum_congr
         [`rfl
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `hxs] [])]
            "=>"
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
                   [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
                   "]")
                  [])
                 [])])))))]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `Finset.sum_congr
    [`rfl
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`x `hxs] [])]
       "=>"
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
              [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
              "]")
             [])
            [])])))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.sum_congr
   [`rfl
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x `hxs] [])]
      "=>"
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
             [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
             "]")
            [])
           [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x `hxs] [])]
    "=>"
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
           [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
           "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
         [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
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
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf [`x `hxs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hxs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hf [`x `hxs]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.coe_to_nnreal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `Nnreal.coe_eq)
     ","
     (Tactic.rwRule [] `Nnreal.coe_sum)
     ","
     (Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.sum_nonneg [`hf])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.sum_nonneg [`hf])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sum_nonneg [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.sum_nonneg [`hf]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.coe_to_nnreal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `Real.toNnreal
    [(Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.app `f [`a]))])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    " in "
    `s
    ", "
    (Term.app `Real.toNnreal [(Term.app `f [`a])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   " in "
   `s
   ", "
   (Term.app `Real.toNnreal [(Term.app `f [`a])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Real.toNnreal [(Term.app `f [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`a]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.toNnreal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
theorem
  _root_.real.to_nnreal_sum_of_nonneg
  { α } { s : Finset α } { f : α → ℝ } ( hf : ∀ a , a ∈ s → 0 ≤ f a )
    : Real.toNnreal ∑ a in s , f a = ∑ a in s , Real.toNnreal f a
  :=
    by
      rw [ ← Nnreal.coe_eq , Nnreal.coe_sum , Real.coe_to_nnreal _ Finset.sum_nonneg hf ]
        exact Finset.sum_congr rfl fun x hxs => by rw [ Real.coe_to_nnreal _ hf x hxs ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.normCast "norm_cast" []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `coe_prod [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [] "}")
    (Term.implicitBinder "{" [`s] [":" (Term.app `Finset [`α])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 "))] "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Init.Coe.«term↑_»
      "↑"
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
       " in "
       `s
       ", "
       (Term.app `f [`a])))
     "="
     (Algebra.BigOperators.Basic.«term∏_in_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))))
  (Command.declValSimple ":=" (Term.app (Term.proj `to_real_hom "." `map_prod) [(Term.hole "_") (Term.hole "_")]) [])
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
  (Term.app (Term.proj `to_real_hom "." `map_prod) [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `to_real_hom "." `map_prod)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `to_real_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Init.Coe.«term↑_»
    "↑"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
     " in "
     `s
     ", "
     (Term.app `f [`a])))
   "="
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    " in "
    `s
    ", "
    (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   " in "
   `s
   ", "
   (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
@[ norm_cast ]
  theorem
    coe_prod
    { α } { s : Finset α } { f : α → ℝ≥0 } : ↑ ∏ a in s , f a = ∏ a in s , ( f a : ℝ )
    := to_real_hom . map_prod _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `_root_.real.to_nnreal_prod_of_nonneg [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [] "}")
    (Term.implicitBinder "{" [`s] [":" (Term.app `Finset [`α])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" (Data.Real.Basic.termℝ "ℝ"))] "}")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`a] [])]
       ","
       (Term.arrow (Init.Core.«term_∈_» `a " ∈ " `s) "→" («term_≤_» (numLit "0") "≤" (Term.app `f [`a]))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Real.toNnreal
      [(Algebra.BigOperators.Basic.«term∏_in_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
        " in "
        `s
        ", "
        (Term.app `f [`a]))])
     "="
     (Algebra.BigOperators.Basic.«term∏_in_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.app `Real.toNnreal [(Term.app `f [`a])])))))
  (Command.declValSimple
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
          [(Tactic.rwRule ["←"] `Nnreal.coe_eq)
           ","
           (Tactic.rwRule [] `Nnreal.coe_prod)
           ","
           (Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.prod_nonneg [`hf])]))]
          "]")
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `Finset.prod_congr
          [`rfl
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x `hxs] [])]
             "=>"
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
                    [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
                    "]")
                   [])
                  [])])))))]))
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
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `Nnreal.coe_eq)
          ","
          (Tactic.rwRule [] `Nnreal.coe_prod)
          ","
          (Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.prod_nonneg [`hf])]))]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `Finset.prod_congr
         [`rfl
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `hxs] [])]
            "=>"
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
                   [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
                   "]")
                  [])
                 [])])))))]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `Finset.prod_congr
    [`rfl
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`x `hxs] [])]
       "=>"
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
              [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
              "]")
             [])
            [])])))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.prod_congr
   [`rfl
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x `hxs] [])]
      "=>"
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
             [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
             "]")
            [])
           [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x `hxs] [])]
    "=>"
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
           [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
           "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
         [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
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
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `hf [`x `hxs])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf [`x `hxs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hxs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hf [`x `hxs]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.coe_to_nnreal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.prod_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `Nnreal.coe_eq)
     ","
     (Tactic.rwRule [] `Nnreal.coe_prod)
     ","
     (Tactic.rwRule [] (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.prod_nonneg [`hf])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Real.coe_to_nnreal [(Term.hole "_") (Term.app `Finset.prod_nonneg [`hf])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.prod_nonneg [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.prod_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.prod_nonneg [`hf]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.coe_to_nnreal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_prod
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `Real.toNnreal
    [(Algebra.BigOperators.Basic.«term∏_in_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
      " in "
      `s
      ", "
      (Term.app `f [`a]))])
   "="
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    " in "
    `s
    ", "
    (Term.app `Real.toNnreal [(Term.app `f [`a])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   " in "
   `s
   ", "
   (Term.app `Real.toNnreal [(Term.app `f [`a])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Real.toNnreal [(Term.app `f [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`a]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.toNnreal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
theorem
  _root_.real.to_nnreal_prod_of_nonneg
  { α } { s : Finset α } { f : α → ℝ } ( hf : ∀ a , a ∈ s → 0 ≤ f a )
    : Real.toNnreal ∏ a in s , f a = ∏ a in s , Real.toNnreal f a
  :=
    by
      rw [ ← Nnreal.coe_eq , Nnreal.coe_prod , Real.coe_to_nnreal _ Finset.prod_nonneg hf ]
        exact Finset.prod_congr rfl fun x hxs => by rw [ Real.coe_to_nnreal _ hf x hxs ]

theorem nsmul_coe (r : ℝ≥0 ) (n : ℕ) : ↑(n • r) = n • (r : ℝ) := by
  norm_cast

@[simp, norm_cast]
protected theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0 ) : ℝ) = n :=
  to_real_hom.map_nat_cast n

noncomputable example : LinearOrderₓ ℝ≥0 := by
  infer_instance

@[simp, norm_cast]
protected theorem coe_le_coe {r₁ r₂ : ℝ≥0 } : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ :=
  Iff.rfl

@[simp, norm_cast]
protected theorem coe_lt_coe {r₁ r₂ : ℝ≥0 } : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ :=
  Iff.rfl

@[simp, norm_cast]
protected theorem coe_pos {r : ℝ≥0 } : (0 : ℝ) < r ↔ 0 < r :=
  Iff.rfl

protected theorem coe_mono : Monotone (coeₓ : ℝ≥0 → ℝ) := fun _ _ => Nnreal.coe_le_coe.2

protected theorem _root_.real.to_nnreal_mono : Monotone Real.toNnreal := fun x y h => max_le_max h (le_reflₓ 0)

@[simp]
theorem _root_.real.to_nnreal_coe {r : ℝ≥0 } : Real.toNnreal r = r :=
  Nnreal.eq $ max_eq_leftₓ r.2

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0 ) n :=
  Nnreal.eq (Nnreal.coe_nat_cast n).symm

@[simp]
theorem to_nnreal_coe_nat (n : ℕ) : Real.toNnreal n = n :=
  Nnreal.eq $ by
    simp [Real.coe_to_nnreal]

/--  `real.to_nnreal` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
noncomputable def gi : GaloisInsertion Real.toNnreal coeₓ :=
  GaloisInsertion.monotoneIntro Nnreal.coe_mono Real.to_nnreal_mono Real.le_coe_to_nnreal fun _ => Real.to_nnreal_coe

example : OrderBot ℝ≥0 := by
  infer_instance

example : PartialOrderₓ ℝ≥0 := by
  infer_instance

noncomputable example : CanonicallyLinearOrderedAddMonoid ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedAddCommMonoid ℝ≥0 := by
  infer_instance

noncomputable example : DistribLattice ℝ≥0 := by
  infer_instance

noncomputable example : SemilatticeInf ℝ≥0 := by
  infer_instance

noncomputable example : SemilatticeSup ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedSemiring ℝ≥0 := by
  infer_instance

example : OrderedCommSemiring ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedCommMonoid ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedCommMonoidWithZero ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedCommGroupWithZero ℝ≥0 := by
  infer_instance

example : CanonicallyOrderedCommSemiring ℝ≥0 := by
  infer_instance

example : DenselyOrdered ℝ≥0 := by
  infer_instance

example : NoTopOrder ℝ≥0 := by
  infer_instance

theorem bdd_above_coe {s : Set ℝ≥0 } : BddAbove ((coeₓ : ℝ≥0 → ℝ) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNnreal b, fun ⟨y, hy⟩ hys => show y ≤ max b 0 from le_max_of_le_left $ hb $ Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩

theorem bdd_below_coe (s : Set ℝ≥0 ) : BddBelow ((coeₓ : ℝ≥0 → ℝ) '' s) :=
  ⟨0, fun r ⟨q, _, Eq⟩ => Eq ▸ q.2⟩

noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  Nonneg.conditionallyCompleteLinearOrderBot Real.Sup_empty.le

theorem coe_Sup (s : Set ℝ≥0 ) : (↑Sup s : ℝ) = Sup ((coeₓ : ℝ≥0 → ℝ) '' s) :=
  Eq.symm $ @subset_Sup_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0 )⟩ s $ Real.Sup_nonneg _ $ fun y ⟨x, _, hy⟩ => hy ▸ x.2

theorem coe_Inf (s : Set ℝ≥0 ) : (↑Inf s : ℝ) = Inf ((coeₓ : ℝ≥0 → ℝ) '' s) :=
  Eq.symm $ @subset_Inf_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0 )⟩ s $ Real.Inf_nonneg _ $ fun y ⟨x, _, hy⟩ => hy ▸ x.2

example : Archimedean ℝ≥0 := by
  infer_instance

instance covariant_add : CovariantClass ℝ≥0 ℝ≥0 (·+·) (· ≤ ·) :=
  OrderedAddCommMonoid.to_covariant_class_left ℝ≥0

instance contravariant_add : ContravariantClass ℝ≥0 ℝ≥0 (·+·) (· < ·) :=
  OrderedCancelAddCommMonoid.to_contravariant_class_left ℝ≥0

instance covariant_mul : CovariantClass ℝ≥0 ℝ≥0 (·*·) (· ≤ ·) :=
  OrderedCommMonoid.to_covariant_class_left ℝ≥0

theorem le_of_forall_pos_le_add {a b : ℝ≥0 } (h : ∀ ε, 0 < ε → a ≤ b+ε) : a ≤ b :=
  le_of_forall_le_of_dense $ fun x hxb => by
    rcases le_iff_exists_add.1 (le_of_ltₓ hxb) with ⟨ε, rfl⟩
    exact h _ ((lt_add_iff_pos_right b).1 hxb)

theorem le_of_add_le_left {a b c : ℝ≥0 } (h : (a+b) ≤ c) : a ≤ c := by
  refine' le_transₓ _ h
  exact (le_add_iff_nonneg_right _).mpr zero_le'

theorem le_of_add_le_right {a b c : ℝ≥0 } (h : (a+b) ≤ c) : b ≤ c := by
  refine' le_transₓ _ h
  exact (le_add_iff_nonneg_left _).mpr zero_le'

theorem lt_iff_exists_rat_btwn (a b : ℝ≥0 ) : a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNnreal q ∧ Real.toNnreal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_transₓ a.2 $ le_of_ltₓ haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_to_nnreal _ this, nnreal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨q, _, haq, hqb⟩ => lt_transₓ haq hqb

theorem bot_eq_zero : (⊥ : ℝ≥0 ) = 0 :=
  rfl

theorem mul_sup (a b c : ℝ≥0 ) : (a*b⊔c) = (a*b)⊔a*c := by
  cases' le_totalₓ b c with h h
  ·
    simp [sup_eq_max, max_eq_rightₓ h, max_eq_rightₓ (mul_le_mul_of_nonneg_left h (zero_le a))]
  ·
    simp [sup_eq_max, max_eq_leftₓ h, max_eq_leftₓ (mul_le_mul_of_nonneg_left h (zero_le a))]

theorem mul_finset_sup {α} {f : α → ℝ≥0 } {s : Finset α} (r : ℝ≥0 ) : (r*s.sup f) = s.sup fun a => r*f a := by
  refine' s.induction_on _ _
  ·
    simp [bot_eq_zero]
  ·
    intro a s has ih
    simp [has, ih, mul_sup]

theorem finset_sup_div {α} {f : α → ℝ≥0 } {s : Finset α} (r : ℝ≥0 ) : s.sup f / r = s.sup fun a => f a / r := by
  simp only [div_eq_inv_mul, mul_finset_sup]

@[simp, norm_cast]
theorem coe_max (x y : ℝ≥0 ) : ((max x y : ℝ≥0 ) : ℝ) = max (x : ℝ) (y : ℝ) :=
  Nnreal.coe_mono.map_max

@[simp, norm_cast]
theorem coe_min (x y : ℝ≥0 ) : ((min x y : ℝ≥0 ) : ℝ) = min (x : ℝ) (y : ℝ) :=
  Nnreal.coe_mono.map_min

@[simp]
theorem zero_le_coe {q : ℝ≥0 } : 0 ≤ (q : ℝ) :=
  q.2

end Nnreal

namespace Real

section ToNnreal

@[simp]
theorem to_nnreal_zero : Real.toNnreal 0 = 0 := by
  simp [Real.toNnreal] <;> rfl

@[simp]
theorem to_nnreal_one : Real.toNnreal 1 = 1 := by
  simp [Real.toNnreal, max_eq_leftₓ (zero_le_one : (0 : ℝ) ≤ 1)] <;> rfl

@[simp]
theorem to_nnreal_pos {r : ℝ} : 0 < Real.toNnreal r ↔ 0 < r := by
  simp [Real.toNnreal, nnreal.coe_lt_coe.symm, lt_irreflₓ]

@[simp]
theorem to_nnreal_eq_zero {r : ℝ} : Real.toNnreal r = 0 ↔ r ≤ 0 := by
  simpa [-to_nnreal_pos] using not_iff_not.2 (@to_nnreal_pos r)

theorem to_nnreal_of_nonpos {r : ℝ} : r ≤ 0 → Real.toNnreal r = 0 :=
  to_nnreal_eq_zero.2

@[simp]
theorem coe_to_nnreal' (r : ℝ) : (Real.toNnreal r : ℝ) = max r 0 :=
  rfl

@[simp]
theorem to_nnreal_le_to_nnreal_iff {r p : ℝ} (hp : 0 ≤ p) : Real.toNnreal r ≤ Real.toNnreal p ↔ r ≤ p := by
  simp [nnreal.coe_le_coe.symm, Real.toNnreal, hp]

@[simp]
theorem to_nnreal_lt_to_nnreal_iff' {r p : ℝ} : Real.toNnreal r < Real.toNnreal p ↔ r < p ∧ 0 < p := by
  simp [nnreal.coe_lt_coe.symm, Real.toNnreal, lt_irreflₓ]

theorem to_nnreal_lt_to_nnreal_iff {r p : ℝ} (h : 0 < p) : Real.toNnreal r < Real.toNnreal p ↔ r < p :=
  to_nnreal_lt_to_nnreal_iff'.trans (and_iff_left h)

theorem to_nnreal_lt_to_nnreal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) : Real.toNnreal r < Real.toNnreal p ↔ r < p :=
  to_nnreal_lt_to_nnreal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_ltₓ hr h⟩⟩

@[simp]
theorem to_nnreal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) : Real.toNnreal (r+p) = Real.toNnreal r+Real.toNnreal p :=
  Nnreal.eq $ by
    simp [Real.toNnreal, hr, hp, add_nonneg]

theorem to_nnreal_add_to_nnreal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    (Real.toNnreal r+Real.toNnreal p) = Real.toNnreal (r+p) :=
  (Real.to_nnreal_add hr hp).symm

theorem to_nnreal_le_to_nnreal {r p : ℝ} (h : r ≤ p) : Real.toNnreal r ≤ Real.toNnreal p :=
  Real.to_nnreal_mono h

theorem to_nnreal_add_le {r p : ℝ} : Real.toNnreal (r+p) ≤ Real.toNnreal r+Real.toNnreal p :=
  Nnreal.coe_le_coe.1 $ max_leₓ (add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _)) Nnreal.zero_le_coe

theorem to_nnreal_le_iff_le_coe {r : ℝ} {p : ℝ≥0 } : Real.toNnreal r ≤ p ↔ r ≤ ↑p :=
  Nnreal.gi.gc r p

theorem le_to_nnreal_iff_coe_le {r : ℝ≥0 } {p : ℝ} (hp : 0 ≤ p) : r ≤ Real.toNnreal p ↔ ↑r ≤ p := by
  rw [← Nnreal.coe_le_coe, Real.coe_to_nnreal p hp]

theorem le_to_nnreal_iff_coe_le' {r : ℝ≥0 } {p : ℝ} (hr : 0 < r) : r ≤ Real.toNnreal p ↔ ↑r ≤ p :=
  (le_or_ltₓ 0 p).elim le_to_nnreal_iff_coe_le $ fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_le, to_nnreal_eq_zero.2 hp.le, hr.not_le]

theorem to_nnreal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0 } (ha : 0 ≤ r) : Real.toNnreal r < p ↔ r < ↑p := by
  rw [← Nnreal.coe_lt_coe, Real.coe_to_nnreal r ha]

theorem lt_to_nnreal_iff_coe_lt {r : ℝ≥0 } {p : ℝ} : r < Real.toNnreal p ↔ ↑r < p := by
  cases le_totalₓ 0 p
  ·
    rw [← Nnreal.coe_lt_coe, Real.coe_to_nnreal p h]
  ·
    rw [to_nnreal_eq_zero.2 h]
    constructor
    ·
      intro
      have := not_lt_of_le (zero_le r)
      contradiction
    ·
      intro rp
      have : ¬p ≤ 0 := not_le_of_lt (lt_of_le_of_ltₓ (Nnreal.coe_nonneg _) rp)
      contradiction

@[simp]
theorem to_nnreal_bit0 {r : ℝ} (hr : 0 ≤ r) : Real.toNnreal (bit0 r) = bit0 (Real.toNnreal r) :=
  Real.to_nnreal_add hr hr

@[simp]
theorem to_nnreal_bit1 {r : ℝ} (hr : 0 ≤ r) : Real.toNnreal (bit1 r) = bit1 (Real.toNnreal r) :=
  (Real.to_nnreal_add
        (by
          simp [hr])
        zero_le_one).trans
    (by
      simp [to_nnreal_one, bit1, hr])

end ToNnreal

end Real

open Real

namespace Nnreal

section Mul

theorem mul_eq_mul_left {a b c : ℝ≥0 } (h : a ≠ 0) : ((a*b) = a*c) ↔ b = c := by
  rw [← Nnreal.eq_iff, ← Nnreal.eq_iff, Nnreal.coe_mul, Nnreal.coe_mul]
  constructor
  ·
    exact mul_left_cancel₀ (mt (@Nnreal.eq_iff a 0).1 h)
  ·
    intro h
    rw [h]

theorem _root_.real.to_nnreal_mul {p q : ℝ} (hp : 0 ≤ p) : Real.toNnreal (p*q) = Real.toNnreal p*Real.toNnreal q := by
  cases' le_totalₓ 0 q with hq hq
  ·
    apply Nnreal.eq
    simp [Real.toNnreal, hp, hq, max_eq_leftₓ, mul_nonneg]
  ·
    have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnreal_eq_zero.2 hq, to_nnreal_eq_zero.2 hpq, mul_zero]

end Mul

section Pow

theorem pow_antitone_exp {a : ℝ≥0 } (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) : a ^ n ≤ a ^ m :=
  pow_le_pow_of_le_one (zero_le a) a1 mn

theorem exists_pow_lt_of_lt_one {a b : ℝ≥0 } (ha : 0 < a) (hb : b < 1) : ∃ n : ℕ, b ^ n < a := by
  simpa only [← coe_pow, Nnreal.coe_lt_coe] using exists_pow_lt_of_lt_one (Nnreal.coe_pos.2 ha) (Nnreal.coe_lt_coe.2 hb)

theorem exists_mem_Ico_zpow {x : ℝ≥0 } {y : ℝ≥0 } (hx : x ≠ 0) (hy : 1 < y) : ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ n+1) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n ≤ x ∧ (x : ℝ) < y ^ n+1 :=
    exists_mem_Ico_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← Nnreal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩

theorem exists_mem_Ioc_zpow {x : ℝ≥0 } {y : ℝ≥0 } (hx : x ≠ 0) (hy : 1 < y) : ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ n+1) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n < x ∧ (x : ℝ) ≤ y ^ n+1 :=
    exists_mem_Ioc_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← Nnreal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩

end Pow

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas
about `has_ordered_sub` in the file `algebra.order.sub`. See also `mul_tsub` and `tsub_mul`. -/


theorem sub_def {r p : ℝ≥0 } : r - p = Real.toNnreal (r - p) :=
  rfl

theorem coe_sub_def {r p : ℝ≥0 } : ↑(r - p) = max (r - p : ℝ) 0 :=
  rfl

noncomputable example : HasOrderedSub ℝ≥0 := by
  infer_instance

theorem sub_div (a b c : ℝ≥0 ) : (a - b) / c = a / c - b / c := by
  simp only [div_eq_mul_inv, tsub_mul]

end Sub

section Inv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_div [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 "))] [] ")")
    (Term.explicitBinder "(" [`b] [":" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     («term_/_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i]))
      "/"
      `b)
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      («term_/_» (Term.app `f [`i]) "/" `b)))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv) "," (Tactic.simpLemma [] [] `Finset.sum_mul)] "]"]
         [])
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
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv) "," (Tactic.simpLemma [] [] `Finset.sum_mul)] "]"]
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
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv) "," (Tactic.simpLemma [] [] `Finset.sum_mul)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `div_eq_mul_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   («term_/_»
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i]))
    "/"
    `b)
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    («term_/_» (Term.app `f [`i]) "/" `b)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   («term_/_» (Term.app `f [`i]) "/" `b))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (Term.app `f [`i]) "/" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
theorem
  sum_div
  { ι } ( s : Finset ι ) ( f : ι → ℝ≥0 ) ( b : ℝ≥0 ) : ∑ i in s , f i / b = ∑ i in s , f i / b
  := by simp only [ div_eq_mul_inv , Finset.sum_mul ]

@[simp]
theorem inv_pos {r : ℝ≥0 } : 0 < r⁻¹ ↔ 0 < r := by
  simp [pos_iff_ne_zero]

theorem div_pos {r p : ℝ≥0 } (hr : 0 < r) (hp : 0 < p) : 0 < r / p := by
  simpa only [div_eq_mul_inv] using mul_pos hr (inv_pos.2 hp)

protected theorem mul_inv {r p : ℝ≥0 } : (r*p)⁻¹ = p⁻¹*r⁻¹ :=
  Nnreal.eq $ mul_inv_rev₀ _ _

theorem div_self_le (r : ℝ≥0 ) : r / r ≤ 1 :=
  if h : r = 0 then by
    simp [h]
  else by
    rw [div_self h]

@[simp]
theorem inv_le {r p : ℝ≥0 } (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r*p := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]

theorem inv_le_of_le_mul {r p : ℝ≥0 } (h : 1 ≤ r*p) : r⁻¹ ≤ p := by
  by_cases' r = 0 <;> simp [inv_le]

@[simp]
theorem le_inv_iff_mul_le {r p : ℝ≥0 } (h : p ≠ 0) : r ≤ p⁻¹ ↔ (r*p) ≤ 1 := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_commₓ]

@[simp]
theorem lt_inv_iff_mul_lt {r p : ℝ≥0 } (h : p ≠ 0) : r < p⁻¹ ↔ (r*p) < 1 := by
  rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_commₓ]

theorem mul_le_iff_le_inv {a b r : ℝ≥0 } (hr : r ≠ 0) : (r*a) ≤ b ↔ a ≤ r⁻¹*b :=
  have : 0 < r := lt_of_le_of_neₓ (zero_le r) hr.symm
  by
  rw [← @mul_le_mul_left _ _ a _ r this, ← mul_assocₓ, mul_inv_cancel hr, one_mulₓ]

theorem le_div_iff_mul_le {a b r : ℝ≥0 } (hr : r ≠ 0) : a ≤ b / r ↔ (a*r) ≤ b := by
  rw [div_eq_inv_mul, ← mul_le_iff_le_inv hr, mul_commₓ]

theorem div_le_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b*r :=
  @div_le_iff ℝ _ a r b $ pos_iff_ne_zero.2 hr

theorem div_le_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r*b :=
  @div_le_iff' ℝ _ a r b $ pos_iff_ne_zero.2 hr

theorem div_le_of_le_mul {a b c : ℝ≥0 } (h : a ≤ b*c) : a / c ≤ b :=
  if h0 : c = 0 then by
    simp [h0]
  else (div_le_iff h0).2 h

theorem div_le_of_le_mul' {a b c : ℝ≥0 } (h : a ≤ b*c) : a / b ≤ c :=
  div_le_of_le_mul $ mul_commₓ b c ▸ h

theorem le_div_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a ≤ b / r ↔ (a*r) ≤ b :=
  @le_div_iff ℝ _ a b r $ pos_iff_ne_zero.2 hr

theorem le_div_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a ≤ b / r ↔ (r*a) ≤ b :=
  @le_div_iff' ℝ _ a b r $ pos_iff_ne_zero.2 hr

theorem div_lt_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r < b ↔ a < b*r :=
  lt_iff_lt_of_le_iff_le (le_div_iff hr)

theorem div_lt_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r < b ↔ a < r*b :=
  lt_iff_lt_of_le_iff_le (le_div_iff' hr)

theorem lt_div_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a < b / r ↔ (a*r) < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hr)

theorem lt_div_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a < b / r ↔ (r*a) < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff' hr)

theorem mul_lt_of_lt_div {a b r : ℝ≥0 } (h : a < b / r) : (a*r) < b := by
  refine' (lt_div_iff $ fun hr => False.elim _).1 h
  subst r
  simpa using h

theorem div_le_div_left_of_le {a b c : ℝ≥0 } (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) : a / b ≤ a / c := by
  by_cases' a0 : a = 0
  ·
    rw [a0, zero_div, zero_div]
  ·
    cases' a with a ha
    replace a0 : 0 < a := lt_of_le_of_neₓ ha (ne_of_ltₓ (zero_lt_iff.mpr a0))
    exact (div_le_div_left a0 b0 c0).mpr cb

theorem div_le_div_left {a b c : ℝ≥0 } (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) : a / b ≤ a / c ↔ c ≤ b := by
  rw [Nnreal.div_le_iff b0.ne.symm, div_mul_eq_mul_div, Nnreal.le_div_iff_mul_le c0.ne.symm, mul_le_mul_left a0]

theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0 } (h : ∀, ∀ a < 1, ∀, (a*x) ≤ y) : x ≤ y :=
  le_of_forall_ge_of_dense $ fun a ha =>
    have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_ltₓ (zero_le _) ha)
    have hx' : x⁻¹ ≠ 0 := by
      rwa [· ≠ ·, inv_eq_zero]
    have : (a*x⁻¹) < 1 := by
      rwa [← lt_inv_iff_mul_lt hx', inv_inv₀]
    have : ((a*x⁻¹)*x) ≤ y := h _ this
    by
    rwa [mul_assocₓ, inv_mul_cancel hx, mul_oneₓ] at this

theorem div_add_div_same (a b c : ℝ≥0 ) : ((a / c)+b / c) = (a+b) / c :=
  Eq.symm $ right_distrib a b (c⁻¹)

theorem half_pos {a : ℝ≥0 } (h : 0 < a) : 0 < a / 2 :=
  div_pos h zero_lt_two

theorem add_halves (a : ℝ≥0 ) : ((a / 2)+a / 2) = a :=
  Nnreal.eq (add_halves a)

theorem half_lt_self {a : ℝ≥0 } (h : a ≠ 0) : a / 2 < a := by
  rw [← Nnreal.coe_lt_coe, Nnreal.coe_div] <;> exact half_lt_self (bot_lt_iff_ne_bot.2 h)

theorem two_inv_lt_one : (2⁻¹ : ℝ≥0 ) < 1 := by
  simpa using half_lt_self zero_ne_one.symm

theorem div_lt_one_of_lt {a b : ℝ≥0 } (h : a < b) : a / b < 1 := by
  rwa [div_lt_iff, one_mulₓ]
  exact ne_of_gtₓ (lt_of_le_of_ltₓ (zero_le _) h)

@[field_simps]
theorem div_add_div (a : ℝ≥0 ) {b : ℝ≥0 } (c : ℝ≥0 ) {d : ℝ≥0 } (hb : b ≠ 0) (hd : d ≠ 0) :
    ((a / b)+c / d) = ((a*d)+b*c) / b*d := by
  rw [← Nnreal.eq_iff]
  simp only [Nnreal.coe_add, Nnreal.coe_div, Nnreal.coe_mul]
  exact div_add_div _ _ (coe_ne_zero.2 hb) (coe_ne_zero.2 hd)

@[field_simps]
theorem add_div' (a b c : ℝ≥0 ) (hc : c ≠ 0) : (b+a / c) = ((b*c)+a) / c := by
  simpa using div_add_div b a one_ne_zero hc

@[field_simps]
theorem div_add' (a b c : ℝ≥0 ) (hc : c ≠ 0) : ((a / c)+b) = (a+b*c) / c := by
  rwa [add_commₓ, add_div', add_commₓ]

theorem _root_.real.to_nnreal_inv {x : ℝ} : Real.toNnreal (x⁻¹) = Real.toNnreal x⁻¹ := by
  by_cases' hx : 0 ≤ x
  ·
    nth_rw 0[← Real.coe_to_nnreal x hx]
    rw [← Nnreal.coe_inv, Real.to_nnreal_coe]
  ·
    have hx' := le_of_not_geₓ hx
    rw [to_nnreal_eq_zero.mpr hx', inv_zero, to_nnreal_eq_zero.mpr (inv_nonpos.mpr hx')]

theorem _root_.real.to_nnreal_div {x y : ℝ} (hx : 0 ≤ x) : Real.toNnreal (x / y) = Real.toNnreal x / Real.toNnreal y :=
  by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.to_nnreal_inv, ← Real.to_nnreal_mul hx]

theorem _root_.real.to_nnreal_div' {x y : ℝ} (hy : 0 ≤ y) : Real.toNnreal (x / y) = Real.toNnreal x / Real.toNnreal y :=
  by
  rw [div_eq_inv_mul, div_eq_inv_mul, Real.to_nnreal_mul (inv_nonneg.2 hy), Real.to_nnreal_inv]

theorem inv_lt_one_iff {x : ℝ≥0 } (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x := by
  rwa [← one_div, div_lt_iff hx, one_mulₓ]

theorem inv_lt_one {x : ℝ≥0 } (hx : 1 < x) : x⁻¹ < 1 :=
  (inv_lt_one_iff (zero_lt_one.trans hx).ne').2 hx

theorem zpow_pos {x : ℝ≥0 } (hx : x ≠ 0) (n : ℤ) : 0 < x ^ n := by
  cases n
  ·
    exact pow_pos hx.bot_lt _
  ·
    simp [pow_pos hx.bot_lt _]

end Inv

@[simp]
theorem abs_eq (x : ℝ≥0 ) : |(x : ℝ)| = x :=
  abs_of_nonneg x.property

end Nnreal

namespace Real

/--  The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot]
noncomputable def nnabs : MonoidWithZeroHom ℝ ℝ≥0 :=
  { toFun := fun x => ⟨|x|, abs_nonneg x⟩,
    map_zero' := by
      ext
      simp ,
    map_one' := by
      ext
      simp ,
    map_mul' := fun x y => by
      ext
      simp [abs_mul] }

@[norm_cast, simp]
theorem coe_nnabs (x : ℝ) : (nnabs x : ℝ) = |x| :=
  rfl

@[simp]
theorem nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = to_nnreal x := by
  ext
  simp [coe_to_nnreal x h, abs_of_nonneg h]

theorem coe_to_nnreal_le (x : ℝ) : (to_nnreal x : ℝ) ≤ |x| :=
  max_leₓ (le_abs_self _) (abs_nonneg _)

theorem cast_nat_abs_eq_nnabs_cast (n : ℤ) : (n.nat_abs : ℝ≥0 ) = nnabs n := by
  ext
  rw [Nnreal.coe_nat_cast, Int.cast_nat_abs, Real.coe_nnabs]

end Real

