import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Typeclasses for measurability of operations

In this file we define classes `has_measurable_mul` etc and prove dot-style lemmas
(`measurable.mul`, `ae_measurable.mul` etc). For binary operations we define two typeclasses:

- `has_measurable_mul` says that both left and right multiplication are measurable;
- `has_measurable_mul₂` says that `λ p : α × α, p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_mul₂`
etc require `α` to have a second countable topology.

We define separate classes for `has_measurable_div`/`has_measurable_sub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `has_continuous_mul` to `has_measurable_mul` see file
`measure_theory.borel_space`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operations) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## Todo

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `has_measurable_pow` to `has_measurable_smul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `measurable_smul`.)
-/


universe u v

open_locale BigOperators Pointwise

open MeasureTheory

/-!
### Binary operations: `(+)`, `(*)`, `(-)`, `(/)`
-/


/--  We say that a type `has_measurable_add` if `((+) c)` and `(+ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (+)` see `has_measurable_add₂`. -/
class HasMeasurableAdd (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable ((·+·) c)
  measurable_add_const : ∀ c : M, Measurable (·+c)

/--  We say that a type `has_measurable_add` if `uncurry (+)` is a measurable functions.
For a typeclass assuming measurability of `((+) c)` and `(+ c)` see `has_measurable_add`. -/
class HasMeasurableAdd₂ (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1+p.2

export HasMeasurableAdd₂ (measurable_add)

export HasMeasurableAdd (measurable_const_add measurable_add_const)

/--  We say that a type `has_measurable_mul` if `((*) c)` and `(* c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `has_measurable_mul₂`. -/
@[to_additive]
class HasMeasurableMul (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable ((·*·) c)
  measurable_mul_const : ∀ c : M, Measurable (·*c)

/--  We say that a type `has_measurable_mul` if `uncurry (*)` is a measurable functions.
For a typeclass assuming measurability of `((*) c)` and `(* c)` see `has_measurable_mul`. -/
@[to_additive HasMeasurableAdd₂]
class HasMeasurableMul₂ (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1*p.2

export HasMeasurableMul₂ (measurable_mul)

export HasMeasurableMul (measurable_const_mul measurable_mul_const)

section Mul

variable {M α : Type _} [MeasurableSpace M] [Mul M] [MeasurableSpace α]

@[to_additive, measurability]
theorem Measurable.const_mul [HasMeasurableMul M] {f : α → M} (hf : Measurable f) (c : M) : Measurable fun x => c*f x :=
  (measurable_const_mul c).comp hf

@[to_additive, measurability]
theorem AeMeasurable.const_mul [HasMeasurableMul M] {f : α → M} {μ : Measureₓ α} (hf : AeMeasurable f μ) (c : M) :
    AeMeasurable (fun x => c*f x) μ :=
  (HasMeasurableMul.measurable_const_mul c).comp_ae_measurable hf

@[to_additive, measurability]
theorem Measurable.mul_const [HasMeasurableMul M] {f : α → M} (hf : Measurable f) (c : M) : Measurable fun x => f x*c :=
  (measurable_mul_const c).comp hf

@[to_additive, measurability]
theorem AeMeasurable.mul_const [HasMeasurableMul M] {f : α → M} {μ : Measureₓ α} (hf : AeMeasurable f μ) (c : M) :
    AeMeasurable (fun x => f x*c) μ :=
  (measurable_mul_const c).comp_ae_measurable hf

@[to_additive, measurability]
theorem Measurable.mul' [HasMeasurableMul₂ M] {f g : α → M} (hf : Measurable f) (hg : Measurable g) :
    Measurable (f*g) :=
  measurable_mul.comp (hf.prod_mk hg)

@[to_additive, measurability]
theorem Measurable.mul [HasMeasurableMul₂ M] {f g : α → M} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a*g a :=
  measurable_mul.comp (hf.prod_mk hg)

@[to_additive, measurability]
theorem AeMeasurable.mul' [HasMeasurableMul₂ M] {μ : Measureₓ α} {f g : α → M} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g μ) : AeMeasurable (f*g) μ :=
  measurable_mul.comp_ae_measurable (hf.prod_mk hg)

@[to_additive, measurability]
theorem AeMeasurable.mul [HasMeasurableMul₂ M] {μ : Measureₓ α} {f g : α → M} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g μ) : AeMeasurable (fun a => f a*g a) μ :=
  measurable_mul.comp_ae_measurable (hf.prod_mk hg)

@[to_additive]
instance (priority := 100) HasMeasurableMul₂.to_has_measurable_mul [HasMeasurableMul₂ M] : HasMeasurableMul M :=
  ⟨fun c => measurable_const.mul measurable_id, fun c => measurable_id.mul measurable_const⟩

attribute [measurability]
  Measurable.add' Measurable.add AeMeasurable.add AeMeasurable.add' Measurable.const_add AeMeasurable.const_add Measurable.add_const AeMeasurable.add_const

end Mul

/--  This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class HasMeasurablePow (β γ : Type _) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2

export HasMeasurablePow (measurable_pow)

instance HasMeasurableMul.hasMeasurablePow (M : Type _) [Monoidₓ M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurablePow M ℕ :=
  ⟨by
    have : MeasurableSingletonClass ℕ := ⟨fun _ => trivialₓ⟩
    refine' measurable_from_prod_encodable fun n => _
    induction' n with n ih
    ·
      simp [pow_zeroₓ, measurable_one]
    ·
      simp only [pow_succₓ]
      exact measurable_id.mul ih⟩

section Pow

variable {β γ α : Type _} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [HasMeasurablePow β γ] [MeasurableSpace α]

@[measurability]
theorem Measurable.pow {f : α → β} {g : α → γ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prod_mk hg)

@[measurability]
theorem AeMeasurable.pow {μ : Measureₓ α} {f : α → β} {g : α → γ} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_ae_measurable (hf.prod_mk hg)

@[measurability]
theorem Measurable.pow_const {f : α → β} (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const

@[measurability]
theorem AeMeasurable.pow_const {μ : Measureₓ α} {f : α → β} (hf : AeMeasurable f μ) (c : γ) :
    AeMeasurable (fun x => f x ^ c) μ :=
  hf.pow ae_measurable_const

@[measurability]
theorem Measurable.const_pow {f : α → γ} (hf : Measurable f) (c : β) : Measurable fun x => c ^ f x :=
  measurable_const.pow hf

@[measurability]
theorem AeMeasurable.const_pow {μ : Measureₓ α} {f : α → γ} (hf : AeMeasurable f μ) (c : β) :
    AeMeasurable (fun x => c ^ f x) μ :=
  ae_measurable_const.pow hf

end Pow

/--  We say that a type `has_measurable_sub` if `(λ x, c - x)` and `(λ x, x - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `has_measurable_sub₂`. -/
class HasMeasurableSub (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : ∀ c : G, Measurable fun x => c - x
  measurable_sub_const : ∀ c : G, Measurable fun x => x - c

/--  We say that a type `has_measurable_sub` if `uncurry (-)` is a measurable functions.
For a typeclass assuming measurability of `((-) c)` and `(- c)` see `has_measurable_sub`. -/
class HasMeasurableSub₂ (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2

export HasMeasurableSub₂ (measurable_sub)

/--  We say that a type `has_measurable_div` if `((/) c)` and `(/ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (/)` see `has_measurable_div₂`. -/
@[to_additive]
class HasMeasurableDiv (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_const_div : ∀ c : G₀, Measurable ((· / ·) c)
  measurable_div_const : ∀ c : G₀, Measurable (· / c)

/--  We say that a type `has_measurable_div` if `uncurry (/)` is a measurable functions.
For a typeclass assuming measurability of `((/) c)` and `(/ c)` see `has_measurable_div`. -/
@[to_additive HasMeasurableSub₂]
class HasMeasurableDiv₂ (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2

export HasMeasurableDiv₂ (measurable_div)

section Div

variable {G α : Type _} [MeasurableSpace G] [Div G] [MeasurableSpace α]

@[to_additive, measurability]
theorem Measurable.const_div [HasMeasurableDiv G] {f : α → G} (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (HasMeasurableDiv.measurable_const_div c).comp hf

@[to_additive, measurability]
theorem AeMeasurable.const_div [HasMeasurableDiv G] {f : α → G} {μ : Measureₓ α} (hf : AeMeasurable f μ) (c : G) :
    AeMeasurable (fun x => c / f x) μ :=
  (HasMeasurableDiv.measurable_const_div c).comp_ae_measurable hf

@[to_additive, measurability]
theorem Measurable.div_const [HasMeasurableDiv G] {f : α → G} (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (HasMeasurableDiv.measurable_div_const c).comp hf

@[to_additive, measurability]
theorem AeMeasurable.div_const [HasMeasurableDiv G] {f : α → G} {μ : Measureₓ α} (hf : AeMeasurable f μ) (c : G) :
    AeMeasurable (fun x => f x / c) μ :=
  (HasMeasurableDiv.measurable_div_const c).comp_ae_measurable hf

@[to_additive, measurability]
theorem Measurable.div' [HasMeasurableDiv₂ G] {f g : α → G} (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurable_div.comp (hf.prod_mk hg)

@[to_additive, measurability]
theorem Measurable.div [HasMeasurableDiv₂ G] {f g : α → G} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a / g a :=
  measurable_div.comp (hf.prod_mk hg)

@[to_additive, measurability]
theorem AeMeasurable.div' [HasMeasurableDiv₂ G] {f g : α → G} {μ : Measureₓ α} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g μ) : AeMeasurable (f / g) μ :=
  measurable_div.comp_ae_measurable (hf.prod_mk hg)

@[to_additive, measurability]
theorem AeMeasurable.div [HasMeasurableDiv₂ G] {f g : α → G} {μ : Measureₓ α} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g μ) : AeMeasurable (fun a => f a / g a) μ :=
  measurable_div.comp_ae_measurable (hf.prod_mk hg)

@[to_additive]
instance (priority := 100) HasMeasurableDiv₂.to_has_measurable_div [HasMeasurableDiv₂ G] : HasMeasurableDiv G :=
  ⟨fun c => measurable_const.div measurable_id, fun c => measurable_id.div measurable_const⟩

attribute [measurability]
  Measurable.sub Measurable.sub' AeMeasurable.sub AeMeasurable.sub' Measurable.const_sub AeMeasurable.const_sub Measurable.sub_const AeMeasurable.sub_const

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `measurability []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `measurable_set_eq_fun [])
  (Command.declSig
   [(Term.implicitBinder "{" [`E] [] "}")
    (Term.instBinder "[" [] (Term.app `MeasurableSpace [`E]) "]")
    (Term.instBinder "[" [] (Term.app `AddGroupₓ [`E]) "]")
    (Term.instBinder "[" [] (Term.app `MeasurableSingletonClass [`E]) "]")
    (Term.instBinder "[" [] (Term.app `HasMeasurableSub₂ [`E]) "]")
    (Term.implicitBinder "{" [`f `g] [":" (Term.arrow `α "→" `E)] "}")
    (Term.explicitBinder "(" [`hf] [":" (Term.app `Measurable [`f])] [] ")")
    (Term.explicitBinder "(" [`hg] [":" (Term.app `Measurable [`g])] [] ")")]
   (Term.typeSpec
    ":"
    (Term.app `MeasurableSet [(Set.«term{_|_}» "{" `x "|" («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x])) "}")])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.suffices'
         "suffices"
         [`h_set_eq []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Set.«term{_|_}»
             "{"
             (Mathlib.ExtendedBinder.extBinder `x [":" `α])
             "|"
             («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x]))
             "}")
            "="
            (Set.«term{_|_}»
             "{"
             `x
             "|"
             («term_=_»
              (Term.app («term_-_» `f "-" `g) [`x])
              "="
              (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")"))
             "}")))])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_set_eq)] "]") []) [])
            (group (Tactic.exact "exact" (Term.app (Term.app `hf.sub [`hg]) [`measurable_set_eq])) [])])))
        [])
       (group (Tactic.ext "ext" [] []) [])
       (group
        (Tactic.simpRw
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Set.mem_set_of_eq)
           ","
           (Tactic.rwRule [] `Pi.sub_apply)
           ","
           (Tactic.rwRule [] `sub_eq_zero)]
          "]")
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
       (Tactic.suffices'
        "suffices"
        [`h_set_eq []]
        [(Term.typeSpec
          ":"
          («term_=_»
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder `x [":" `α])
            "|"
            («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x]))
            "}")
           "="
           (Set.«term{_|_}»
            "{"
            `x
            "|"
            («term_=_»
             (Term.app («term_-_» `f "-" `g) [`x])
             "="
             (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")"))
            "}")))])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_set_eq)] "]") []) [])
           (group (Tactic.exact "exact" (Term.app (Term.app `hf.sub [`hg]) [`measurable_set_eq])) [])])))
       [])
      (group (Tactic.ext "ext" [] []) [])
      (group
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Set.mem_set_of_eq)
          ","
          (Tactic.rwRule [] `Pi.sub_apply)
          ","
          (Tactic.rwRule [] `sub_eq_zero)]
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
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Set.mem_set_of_eq) "," (Tactic.rwRule [] `Pi.sub_apply) "," (Tactic.rwRule [] `sub_eq_zero)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Pi.sub_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_set_eq)] "]") []) [])
      (group (Tactic.exact "exact" (Term.app (Term.app `hf.sub [`hg]) [`measurable_set_eq])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app (Term.app `hf.sub [`hg]) [`measurable_set_eq]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.app `hf.sub [`hg]) [`measurable_set_eq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `measurable_set_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `hf.sub [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf.sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hf.sub [`hg]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_set_eq)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_set_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.suffices'
   "suffices"
   [`h_set_eq []]
   [(Term.typeSpec
     ":"
     («term_=_»
      (Set.«term{_|_}»
       "{"
       (Mathlib.ExtendedBinder.extBinder `x [":" `α])
       "|"
       («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x]))
       "}")
      "="
      (Set.«term{_|_}»
       "{"
       `x
       "|"
       («term_=_»
        (Term.app («term_-_» `f "-" `g) [`x])
        "="
        (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")"))
       "}")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.suffices'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder `x [":" `α])
    "|"
    («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x]))
    "}")
   "="
   (Set.«term{_|_}»
    "{"
    `x
    "|"
    («term_=_»
     (Term.app («term_-_» `f "-" `g) [`x])
     "="
     (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")"))
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `x
   "|"
   («term_=_»
    (Term.app («term_-_» `f "-" `g) [`x])
    "="
    (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")"))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app («term_-_» `f "-" `g) [`x])
   "="
   (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app («term_-_» `f "-" `g) [`x])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_-_» `f "-" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 65, (some 66, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `f "-" `g) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
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
@[ measurability ]
  theorem
    measurable_set_eq_fun
    { E }
        [ MeasurableSpace E ]
        [ AddGroupₓ E ]
        [ MeasurableSingletonClass E ]
        [ HasMeasurableSub₂ E ]
        { f g : α → E }
        ( hf : Measurable f )
        ( hg : Measurable g )
      : MeasurableSet { x | f x = g x }
    :=
      by
        suffices h_set_eq : { x : α | f x = g x } = { x | f - g x = ( 0 : E ) }
          · rw [ h_set_eq ] exact hf.sub hg measurable_set_eq
          ext
          simp_rw [ Set.mem_set_of_eq , Pi.sub_apply , sub_eq_zero ]

theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measureₓ α} [MeasurableSpace E] [AddGroupₓ E]
    [MeasurableSingletonClass E] [HasMeasurableSub₂ E] (hm : m ≤ m0) {f g : α → E} (hf : @Measurable _ _ m _ f)
    (hg : @Measurable _ _ m _ g) (hfg : f =ᵐ[μ] g) : f =ᶠ[@measure.ae α m (μ.trim hm)] g := by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurable_set_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurable_set_eq_fun α m E _ _ _ _ _ _ hf hg)

end Div

/--  We say that a type `has_measurable_neg` if `x ↦ -x` is a measurable function. -/
class HasMeasurableNeg (G : Type _) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G → G)

/--  We say that a type `has_measurable_inv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class HasMeasurableInv (G : Type _) [HasInv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (HasInv.inv : G → G)

export HasMeasurableInv (measurable_inv)

export HasMeasurableNeg (measurable_neg)

-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance
    ( priority := 100 )
    has_measurable_div_of_mul_inv
    ( G : Type _ ) [ MeasurableSpace G ] [ DivInvMonoidₓ G ] [ HasMeasurableMul G ] [ HasMeasurableInv G ]
      : HasMeasurableDiv G
    where
      measurable_const_div c := by convert measurable_inv.const_mul c ext1 apply div_eq_mul_inv
        measurable_div_const c := by convert measurable_id.mul_const ( c ⁻¹ ) ext1 apply div_eq_mul_inv

section Inv

variable {G α : Type _} [HasInv G] [MeasurableSpace G] [HasMeasurableInv G] [MeasurableSpace α]

@[to_additive, measurability]
theorem Measurable.inv {f : α → G} (hf : Measurable f) : Measurable fun x => f x⁻¹ :=
  measurable_inv.comp hf

@[to_additive, measurability]
theorem AeMeasurable.inv {f : α → G} {μ : Measureₓ α} (hf : AeMeasurable f μ) : AeMeasurable (fun x => f x⁻¹) μ :=
  measurable_inv.comp_ae_measurable hf

attribute [measurability] Measurable.neg AeMeasurable.neg

@[to_additive]
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet (s⁻¹) :=
  measurable_inv hs

@[simp, to_additive]
theorem measurable_inv_iff {G : Type _} [Groupₓ G] [MeasurableSpace G] [HasMeasurableInv G] {f : α → G} :
    (Measurable fun x => f x⁻¹) ↔ Measurable f :=
  ⟨fun h => by
    simpa only [inv_invₓ] using h.inv, fun h => h.inv⟩

@[simp, to_additive]
theorem ae_measurable_inv_iff {G : Type _} [Groupₓ G] [MeasurableSpace G] [HasMeasurableInv G] {f : α → G}
    {μ : Measureₓ α} : AeMeasurable (fun x => f x⁻¹) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by
    simpa only [inv_invₓ] using h.inv, fun h => h.inv⟩

@[simp]
theorem measurable_inv_iff₀ {G₀ : Type _} [GroupWithZeroₓ G₀] [MeasurableSpace G₀] [HasMeasurableInv G₀] {f : α → G₀} :
    (Measurable fun x => f x⁻¹) ↔ Measurable f :=
  ⟨fun h => by
    simpa only [inv_inv₀] using h.inv, fun h => h.inv⟩

@[simp]
theorem ae_measurable_inv_iff₀ {G₀ : Type _} [GroupWithZeroₓ G₀] [MeasurableSpace G₀] [HasMeasurableInv G₀] {f : α → G₀}
    {μ : Measureₓ α} : AeMeasurable (fun x => f x⁻¹) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by
    simpa only [inv_inv₀] using h.inv, fun h => h.inv⟩

end Inv

private theorem has_measurable_zpow_aux (G : Type u) [DivInvMonoidₓ G] [MeasurableSpace G] [HasMeasurableMul₂ G]
    [HasMeasurableInv G] (k : ℕ) : Measurable fun x : G => x ^ -[1+ k] := by
  simp_rw [zpow_neg_succ_of_nat]
  exact (measurable_id.pow_const (k+1)).inv

instance hasMeasurableZpow (G : Type u) [DivInvMonoidₓ G] [MeasurableSpace G] [HasMeasurableMul₂ G]
    [HasMeasurableInv G] : HasMeasurablePow G ℤ := by
  let this' : MeasurableSingletonClass ℤ := ⟨fun _ => trivialₓ⟩
  constructor
  refine' measurable_from_prod_encodable fun n => _
  dsimp
  apply Int.casesOn n
  ·
    simpa using measurable_id.pow_const
  ·
    exact has_measurable_zpow_aux G

@[to_additive]
instance (priority := 100) has_measurable_div₂_of_mul_inv (G : Type _) [MeasurableSpace G] [DivInvMonoidₓ G]
    [HasMeasurableMul₂ G] [HasMeasurableInv G] : HasMeasurableDiv₂ G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩

/--  We say that the action of `M` on `α` `has_measurable_vadd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd (M α : Type _) [HasVadd M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_const_vadd : ∀ c : M, Measurable ((· +ᵥ ·) c : α → α)
  measurable_vadd_const : ∀ x : α, Measurable fun c : M => c +ᵥ x

/--  We say that the action of `M` on `α` `has_measurable_smul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class HasMeasurableSmul (M α : Type _) [HasScalar M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_const_smul : ∀ c : M, Measurable ((· • ·) c : α → α)
  measurable_smul_const : ∀ x : α, Measurable fun c : M => c • x

/--  We say that the action of `M` on `α` `has_measurable_vadd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd₂ (M α : Type _) [HasVadd M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)

/--  We say that the action of `M` on `α` `has_measurable_smul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive HasMeasurableVadd₂]
class HasMeasurableSmul₂ (M α : Type _) [HasScalar M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α → α)

export HasMeasurableSmul (measurable_const_smul measurable_smul_const)

export HasMeasurableSmul₂ (measurable_smul)

export HasMeasurableVadd (measurable_const_vadd measurable_vadd_const)

export HasMeasurableVadd₂ (measurable_vadd)

@[to_additive]
instance has_measurable_smul_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul M] :
    HasMeasurableSmul M M :=
  ⟨measurable_id.const_mul, measurable_id.mul_const⟩

@[to_additive]
instance has_measurable_smul₂_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurableSmul₂ M M :=
  ⟨measurable_mul⟩

@[to_additive]
instance Submonoid.has_measurable_smul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoidₓ M] [MulAction M α]
    [HasMeasurableSmul M α] (s : Submonoid M) : HasMeasurableSmul s α :=
  ⟨fun c => by
    simpa only using measurable_const_smul (c : M), fun x =>
    (measurable_smul_const x : Measurable fun c : M => c • x).comp measurable_subtype_coe⟩

@[to_additive]
instance Subgroup.has_measurable_smul {G α} [MeasurableSpace G] [MeasurableSpace α] [Groupₓ G] [MulAction G α]
    [HasMeasurableSmul G α] (s : Subgroup G) : HasMeasurableSmul s α :=
  s.to_submonoid.has_measurable_smul

section Smul

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [HasScalar M β] [MeasurableSpace α]

@[measurability, to_additive]
theorem Measurable.smul [HasMeasurableSmul₂ M β] {f : α → M} {g : α → β} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurable_smul.comp (hf.prod_mk hg)

@[measurability, to_additive]
theorem AeMeasurable.smul [HasMeasurableSmul₂ M β] {f : α → M} {g : α → β} {μ : Measureₓ α} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g μ) : AeMeasurable (fun x => f x • g x) μ :=
  HasMeasurableSmul₂.measurable_smul.comp_ae_measurable (hf.prod_mk hg)

@[to_additive]
instance (priority := 100) HasMeasurableSmul₂.to_has_measurable_smul [HasMeasurableSmul₂ M β] : HasMeasurableSmul M β :=
  ⟨fun c => measurable_const.smul measurable_id, fun y => measurable_id.smul measurable_const⟩

variable [HasMeasurableSmul M β] {μ : Measureₓ α}

@[measurability, to_additive]
theorem Measurable.smul_const {f : α → M} (hf : Measurable f) (y : β) : Measurable fun x => f x • y :=
  (HasMeasurableSmul.measurable_smul_const y).comp hf

@[measurability, to_additive]
theorem AeMeasurable.smul_const {f : α → M} (hf : AeMeasurable f μ) (y : β) : AeMeasurable (fun x => f x • y) μ :=
  (HasMeasurableSmul.measurable_smul_const y).comp_ae_measurable hf

@[measurability, to_additive]
theorem Measurable.const_smul' {f : α → β} (hf : Measurable f) (c : M) : Measurable fun x => c • f x :=
  (HasMeasurableSmul.measurable_const_smul c).comp hf

@[measurability, to_additive]
theorem Measurable.const_smul {f : α → β} (hf : Measurable f) (c : M) : Measurable (c • f) :=
  hf.const_smul' c

@[measurability, to_additive]
theorem AeMeasurable.const_smul' {f : α → β} (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => c • f x) μ :=
  (HasMeasurableSmul.measurable_const_smul c).comp_ae_measurable hf

@[measurability, to_additive]
theorem AeMeasurable.const_smul {f : α → β} (hf : AeMeasurable f μ) (c : M) : AeMeasurable (c • f) μ :=
  hf.const_smul' c

end Smul

section MulAction

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [Monoidₓ M] [MulAction M β] [HasMeasurableSmul M β]
  [MeasurableSpace α] {f : α → β} {μ : Measureₓ α}

variable {G : Type _} [Groupₓ G] [MeasurableSpace G] [MulAction G β] [HasMeasurableSmul G β]

@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by
    simpa only [inv_smul_smul] using h.const_smul' (c⁻¹), fun h => h.const_smul c⟩

@[to_additive]
theorem ae_measurable_const_smul_iff (c : G) : AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by
    simpa only [inv_smul_smul] using h.const_smul' (c⁻¹), fun h => h.const_smul c⟩

@[to_additive]
instance : MeasurableSpace (Units M) :=
  MeasurableSpace.comap (coeₓ : Units M → M) ‹_›

-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance
    Units.has_measurable_smul
    : HasMeasurableSmul ( Units M ) β
    where
      measurable_const_smul c := ( measurable_const_smul ( c : M ) : _ )
        measurable_smul_const
          x
          :=
          ( measurable_smul_const x : Measurable fun c : M => c • x ) . comp MeasurableSpace.le_map_comap

@[to_additive]
theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) : (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u

@[to_additive]
theorem IsUnit.ae_measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ ae_measurable_const_smul_iff u

variable {G₀ : Type _} [GroupWithZeroₓ G₀] [MeasurableSpace G₀] [MulAction G₀ β] [HasMeasurableSmul G₀ β]

theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) : (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff

theorem ae_measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) : AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  (IsUnit.mk0 c hc).ae_measurable_const_smul_iff

end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

instance {α : Type _} [h : MeasurableSpace α] : MeasurableSpace (αᵐᵒᵖ) :=
  MeasurableSpace.map op h

theorem measurable_op {α : Type _} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun s => id

theorem measurable_unop {α : Type _} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) := fun s => id

instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul M] : HasMeasurableMul (Mᵐᵒᵖ) :=
  ⟨fun c => measurable_op.comp (measurable_unop.mul_const _), fun c => measurable_op.comp (measurable_unop.const_mul _)⟩

instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] : HasMeasurableMul₂ (Mᵐᵒᵖ) :=
  ⟨measurable_op.comp ((measurable_unop.comp measurable_snd).mul (measurable_unop.comp measurable_fst))⟩

instance has_measurable_smul_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul M] :
    HasMeasurableSmul (Mᵐᵒᵖ) M :=
  ⟨fun c => measurable_mul_const (unop c), fun x => measurable_unop.const_mul x⟩

instance has_measurable_smul₂_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurableSmul₂ (Mᵐᵒᵖ) M :=
  ⟨measurable_snd.mul (measurable_unop.comp measurable_fst)⟩

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoidₓ

variable {M α : Type _} [Monoidₓ M] [MeasurableSpace M] [HasMeasurableMul₂ M] [MeasurableSpace α]

@[to_additive, measurability]
theorem List.measurable_prod' (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, Measurable f) : Measurable l.prod := by
  induction' l with f l ihl
  ·
    exact measurable_one
  rw [List.forall_mem_consₓ] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)

@[to_additive, measurability]
theorem List.ae_measurable_prod' {μ : Measureₓ α} (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeMeasurable f μ) :
    AeMeasurable l.prod μ := by
  induction' l with f l ihl
  ·
    exact ae_measurable_one
  rw [List.forall_mem_consₓ] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)

@[to_additive, measurability]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod' hl

@[to_additive, measurability]
theorem List.ae_measurable_prod {μ : Measureₓ α} (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeMeasurable f μ) :
    AeMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.ae_measurable_prod' hl

end Monoidₓ

section CommMonoidₓ

variable {M ι α : Type _} [CommMonoidₓ M] [MeasurableSpace M] [HasMeasurableMul₂ M] [MeasurableSpace α]

@[to_additive, measurability]
theorem Multiset.measurable_prod' (l : Multiset (α → M)) (hl : ∀, ∀ f ∈ l, ∀, Measurable f) : Measurable l.prod := by
  rcases l with ⟨l⟩
  simpa using
    l.measurable_prod'
      (by
        simpa using hl)

@[to_additive, measurability]
theorem Multiset.ae_measurable_prod' {μ : Measureₓ α} (l : Multiset (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeMeasurable f μ) :
    AeMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using
    l.ae_measurable_prod'
      (by
        simpa using hl)

@[to_additive, measurability]
theorem Multiset.measurable_prod (s : Multiset (α → M)) (hs : ∀, ∀ f ∈ s, ∀, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod' hs

@[to_additive, measurability]
theorem Multiset.ae_measurable_prod {μ : Measureₓ α} (s : Multiset (α → M)) (hs : ∀, ∀ f ∈ s, ∀, AeMeasurable f μ) :
    AeMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.ae_measurable_prod' hs

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.toAdditive "to_additive" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.simple `measurability []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `Finset.measurable_prod' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" (Term.arrow `α "→" `M))] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `i
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," (Term.app `Measurable [(Term.app `f [`i])]))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `Measurable
     [(Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i]))])))
  (Command.declValSimple
   ":="
   (Term.app
    `Finset.prod_induction
    [(Term.hole "_")
     (Term.hole "_")
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `Measurable.mul))
     (Term.app (Term.explicit "@" `measurable_one) [`M (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
     `hf])
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
  (Term.app
   `Finset.prod_induction
   [(Term.hole "_")
    (Term.hole "_")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `Measurable.mul))
    (Term.app (Term.explicit "@" `measurable_one) [`M (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
    `hf])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.explicit "@" `measurable_one) [`M (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `measurable_one)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `measurable_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.explicit "@" `measurable_one) [`M (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `Measurable.mul))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Measurable.mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `Measurable.mul)) []]
 ")")
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
  `Finset.prod_induction
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `Measurable
   [(Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
@[ to_additive , measurability ]
  theorem
    Finset.measurable_prod'
    { f : ι → α → M } ( s : Finset ι ) ( hf : ∀ , ∀ i ∈ s , ∀ , Measurable f i ) : Measurable ∏ i in s , f i
    := Finset.prod_induction _ _ fun _ _ => Measurable.mul @ measurable_one M _ _ _ _ hf

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.toAdditive "to_additive" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.simple `measurability []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `Finset.measurable_prod [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" (Term.arrow `α "→" `M))] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `i
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," (Term.app `Measurable [(Term.app `f [`i])]))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `Measurable
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`a] [])]
        "=>"
        (Algebra.BigOperators.Basic.«term∏_in_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         " in "
         `s
         ", "
         (Term.app `f [`i `a]))))])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simpa
         "simpa"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] ["←"] `Finset.prod_apply)] "]"]
         []
         ["using" (Term.app `s.measurable_prod' [`hf])])
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
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] ["←"] `Finset.prod_apply)] "]"]
        []
        ["using" (Term.app `s.measurable_prod' [`hf])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] ["←"] `Finset.prod_apply)] "]"]
   []
   ["using" (Term.app `s.measurable_prod' [`hf])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s.measurable_prod' [`hf])
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
  `s.measurable_prod'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.prod_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `Measurable
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`a] [])]
      "=>"
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i `a]))))])
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
    [(Term.simpleBinder [`a] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i `a]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i `a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i `a])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
@[ to_additive , measurability ]
  theorem
    Finset.measurable_prod
    { f : ι → α → M } ( s : Finset ι ) ( hf : ∀ , ∀ i ∈ s , ∀ , Measurable f i ) : Measurable fun a => ∏ i in s , f i a
    := by simpa only [ ← Finset.prod_apply ] using s.measurable_prod' hf

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.toAdditive "to_additive" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.simple `measurability []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `Finset.ae_measurable_prod' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`μ] [":" (Term.app `Measureₓ [`α])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" (Term.arrow `α "→" `M))] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `i
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," (Term.app `AeMeasurable [(Term.app `f [`i]) `μ]))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `AeMeasurable
     [(Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i]))
      `μ])))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app `Multiset.ae_measurable_prod' [(Term.hole "_")])
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`g `hg] [])]
      "=>"
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`i "," `hi "," `hg] "⟩")
         []
         []
         ":="
         (Term.app (Term.proj `Multiset.mem_map "." (fieldIdx "1")) [`hg])))
       []
       (Term.subst `hg "▸" [(Term.app `hf [(Term.hole "_") `hi])])))))
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
  («term_$__»
   (Term.app `Multiset.ae_measurable_prod' [(Term.hole "_")])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`g `hg] [])]
     "=>"
     (Term.let
      "let"
      (Term.letDecl
       (Term.letPatDecl
        (Term.anonymousCtor "⟨" [`i "," `hi "," `hg] "⟩")
        []
        []
        ":="
        (Term.app (Term.proj `Multiset.mem_map "." (fieldIdx "1")) [`hg])))
      []
      (Term.subst `hg "▸" [(Term.app `hf [(Term.hole "_") `hi])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`g `hg] [])]
    "=>"
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`i "," `hi "," `hg] "⟩")
       []
       []
       ":="
       (Term.app (Term.proj `Multiset.mem_map "." (fieldIdx "1")) [`hg])))
     []
     (Term.subst `hg "▸" [(Term.app `hf [(Term.hole "_") `hi])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor "⟨" [`i "," `hi "," `hg] "⟩")
     []
     []
     ":="
     (Term.app (Term.proj `Multiset.mem_map "." (fieldIdx "1")) [`hg])))
   []
   (Term.subst `hg "▸" [(Term.app `hf [(Term.hole "_") `hi])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.subst `hg "▸" [(Term.app `hf [(Term.hole "_") `hi])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf [(Term.hole "_") `hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app (Term.proj `Multiset.mem_map "." (fieldIdx "1")) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Multiset.mem_map "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Multiset.mem_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`i "," `hi "," `hg] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `Multiset.ae_measurable_prod' [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Multiset.ae_measurable_prod'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `AeMeasurable
   [(Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i]))
    `μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
@[ to_additive , measurability ]
  theorem
    Finset.ae_measurable_prod'
    { μ : Measureₓ α } { f : ι → α → M } ( s : Finset ι ) ( hf : ∀ , ∀ i ∈ s , ∀ , AeMeasurable f i μ )
      : AeMeasurable ∏ i in s , f i μ
    := Multiset.ae_measurable_prod' _ $ fun g hg => let ⟨ i , hi , hg ⟩ := Multiset.mem_map . 1 hg hg ▸ hf _ hi

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.toAdditive "to_additive" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.simple `measurability []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `Finset.ae_measurable_prod [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" (Term.arrow `α "→" `M))] "}")
    (Term.implicitBinder "{" [`μ] [":" (Term.app `Measureₓ [`α])] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `i
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," (Term.app `AeMeasurable [(Term.app `f [`i]) `μ]))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `AeMeasurable
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`a] [])]
        "=>"
        (Algebra.BigOperators.Basic.«term∏_in_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         " in "
         `s
         ", "
         (Term.app `f [`i `a]))))
      `μ])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simpa
         "simpa"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] ["←"] `Finset.prod_apply)] "]"]
         []
         ["using" (Term.app `s.ae_measurable_prod' [`hf])])
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
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] ["←"] `Finset.prod_apply)] "]"]
        []
        ["using" (Term.app `s.ae_measurable_prod' [`hf])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] ["←"] `Finset.prod_apply)] "]"]
   []
   ["using" (Term.app `s.ae_measurable_prod' [`hf])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s.ae_measurable_prod' [`hf])
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
  `s.ae_measurable_prod'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.prod_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `AeMeasurable
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`a] [])]
      "=>"
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i `a]))))
    `μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i `a]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i `a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i `a])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
@[ to_additive , measurability ]
  theorem
    Finset.ae_measurable_prod
    { f : ι → α → M } { μ : Measureₓ α } ( s : Finset ι ) ( hf : ∀ , ∀ i ∈ s , ∀ , AeMeasurable f i μ )
      : AeMeasurable fun a => ∏ i in s , f i a μ
    := by simpa only [ ← Finset.prod_apply ] using s.ae_measurable_prod' hf

end CommMonoidₓ

attribute [measurability]
  List.measurable_sum' List.ae_measurable_sum' List.measurable_sum List.ae_measurable_sum Multiset.measurable_sum' Multiset.ae_measurable_sum' Multiset.measurable_sum Multiset.ae_measurable_sum Finset.measurable_sum' Finset.ae_measurable_sum' Finset.measurable_sum Finset.ae_measurable_sum

