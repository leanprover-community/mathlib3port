import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.SpecificLimits
import Mathbin.Topology.Sequences

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory of `semi_normed_group_hom` and we specialize to `normed_group_hom` when needed.
-/


noncomputable section

open_locale Nnreal BigOperators

/--  A morphism of seminormed abelian groups is a bounded group homomorphism. -/
structure NormedGroupHom (V W : Type _) [SemiNormedGroup V] [SemiNormedGroup W] where
  toFun : V → W
  map_add' : ∀ v₁ v₂, to_fun (v₁+v₂) = to_fun v₁+to_fun v₂
  bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C*∥v∥

namespace AddMonoidHom

variable {V W : Type _} [SemiNormedGroup V] [SemiNormedGroup W] {f g : NormedGroupHom V W}

/--  Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_group_hom'` for a version that uses `ℝ≥0` for the bound. -/
def mk_normed_group_hom (f : V →+ W) (C : ℝ) (h : ∀ v, ∥f v∥ ≤ C*∥v∥) : NormedGroupHom V W :=
  { f with bound' := ⟨C, h⟩ }

/--  Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_group_hom` for a version that uses `ℝ` for the bound. -/
def mk_normed_group_hom' (f : V →+ W) (C : ℝ≥0 ) (hC : ∀ x, nnnorm (f x) ≤ C*nnnorm x) : NormedGroupHom V W :=
  { f with bound' := ⟨C, hC⟩ }

end AddMonoidHom

theorem exists_pos_bound_of_bound {V W : Type _} [SemiNormedGroup V] [SemiNormedGroup W] {f : V → W} (M : ℝ)
    (h : ∀ x, ∥f x∥ ≤ M*∥x∥) : ∃ N, 0 < N ∧ ∀ x, ∥f x∥ ≤ N*∥x∥ :=
  ⟨max M 1, lt_of_lt_of_leₓ zero_lt_one (le_max_rightₓ _ _), fun x =>
    calc ∥f x∥ ≤ M*∥x∥ := h x
      _ ≤ max M 1*∥x∥ := mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (norm_nonneg _)
      ⟩

namespace NormedGroupHom

variable {V V₁ V₂ V₃ : Type _}

variable [SemiNormedGroup V] [SemiNormedGroup V₁] [SemiNormedGroup V₂] [SemiNormedGroup V₃]

variable {f g : NormedGroupHom V₁ V₂}

instance : CoeFun (NormedGroupHom V₁ V₂) fun _ => V₁ → V₂ :=
  ⟨NormedGroupHom.toFun⟩

initialize_simps_projections NormedGroupHom (toFun → apply)

theorem coe_inj (H : (f : V₁ → V₂) = g) : f = g := by
  cases f <;> cases g <;> congr <;> exact funext H

theorem coe_injective : @Function.Injective (NormedGroupHom V₁ V₂) (V₁ → V₂) coeFn := by
  apply coe_inj

theorem coe_inj_iff : f = g ↔ (f : V₁ → V₂) = g :=
  ⟨congr_argₓ _, coe_inj⟩

@[ext]
theorem ext (H : ∀ x, f x = g x) : f = g :=
  coe_inj $ funext H

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x <;> rfl, ext⟩

variable (f g)

@[simp]
theorem to_fun_eq_coe : f.to_fun = f :=
  rfl

@[simp]
theorem coe_mk f h₁ h₂ h₃ : ⇑(⟨f, h₁, h₂, h₃⟩ : NormedGroupHom V₁ V₂) = f :=
  rfl

@[simp]
theorem coe_mk_normed_group_hom (f : V₁ →+ V₂) C hC : ⇑f.mk_normed_group_hom C hC = f :=
  rfl

@[simp]
theorem coe_mk_normed_group_hom' (f : V₁ →+ V₂) C hC : ⇑f.mk_normed_group_hom' C hC = f :=
  rfl

/--  The group homomorphism underlying a bounded group homomorphism. -/
def to_add_monoid_hom (f : NormedGroupHom V₁ V₂) : V₁ →+ V₂ :=
  AddMonoidHom.mk' f f.map_add'

@[simp]
theorem coe_to_add_monoid_hom : ⇑f.to_add_monoid_hom = f :=
  rfl

theorem to_add_monoid_hom_injective : Function.Injective (@NormedGroupHom.toAddMonoidHom V₁ V₂ _ _) := fun f g h =>
  coe_inj $
    show ⇑f.to_add_monoid_hom = g by
      rw [h]
      rfl

@[simp]
theorem mk_to_add_monoid_hom f h₁ h₂ : (⟨f, h₁, h₂⟩ : NormedGroupHom V₁ V₂).toAddMonoidHom = AddMonoidHom.mk' f h₁ :=
  rfl

@[simp]
theorem map_zero : f 0 = 0 :=
  f.to_add_monoid_hom.map_zero

@[simp]
theorem map_add x y : f (x+y) = f x+f y :=
  f.to_add_monoid_hom.map_add _ _

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
  (Command.declId `map_sum [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`v] [":" (Term.arrow `ι "→" `V₁)] [] ")")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `f
      [(Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        " in "
        `s
        ", "
        (Term.app `v [`i]))])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `f [(Term.app `v [`i])])))))
  (Command.declValSimple ":=" (Term.app `f.to_add_monoid_hom.map_sum [(Term.hole "_") (Term.hole "_")]) [])
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
  (Term.app `f.to_add_monoid_hom.map_sum [(Term.hole "_") (Term.hole "_")])
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
  `f.to_add_monoid_hom.map_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `f
    [(Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `v [`i]))])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Term.app `f [(Term.app `v [`i])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [(Term.app `v [`i])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [(Term.app `v [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `v [`i])
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
  `v
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `v [`i]) []] ")")
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
@[ simp ]
  theorem
    map_sum
    { ι : Type _ } ( v : ι → V₁ ) ( s : Finset ι ) : f ∑ i in s , v i = ∑ i in s , f v i
    := f.to_add_monoid_hom.map_sum _ _

@[simp]
theorem map_sub x y : f (x - y) = f x - f y :=
  f.to_add_monoid_hom.map_sub _ _

@[simp]
theorem map_neg x : f (-x) = -f x :=
  f.to_add_monoid_hom.map_neg _

theorem bound : ∃ C, 0 < C ∧ ∀ x, ∥f x∥ ≤ C*∥x∥ :=
  let ⟨C, hC⟩ := f.bound'
  exists_pos_bound_of_bound _ hC

theorem antilipschitz_of_norm_ge {K : ℝ≥0 } (h : ∀ x, ∥x∥ ≤ K*∥f x∥) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist $ fun x y => by
    simpa only [dist_eq_norm, f.map_sub] using h (x - y)

/--  A normed group hom is surjective on the subgroup `K` with constant `C` if every element
`x` of `K` has a preimage whose norm is bounded above by `C*∥x∥`. This is a more
abstract version of `f` having a right inverse defined on `K` with operator norm
at most `C`. -/
def surjective_on_with (f : NormedGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : ℝ) : Prop :=
  ∀, ∀ h ∈ K, ∀, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥

theorem surjective_on_with.mono {f : NormedGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : ℝ}
    (h : f.surjective_on_with K C) (H : C ≤ C') : f.surjective_on_with K C' := by
  intro k k_in
  rcases h k k_in with ⟨g, rfl, hg⟩
  use g, rfl
  by_cases' Hg : ∥f g∥ = 0
  ·
    simpa [Hg] using hg
  ·
    exact hg.trans ((mul_le_mul_right $ (Ne.symm Hg).le_iff_lt.mp (norm_nonneg _)).mpr H)

theorem surjective_on_with.exists_pos {f : NormedGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
    (h : f.surjective_on_with K C) : ∃ C' > 0, f.surjective_on_with K C' := by
  refine' ⟨|C|+1, _, _⟩
  ·
    linarith [abs_nonneg C]
  ·
    apply h.mono
    linarith [le_abs_self C]

theorem surjective_on_with.surj_on {f : NormedGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
    (h : f.surjective_on_with K C) : Set.SurjOn f Set.Univ K := fun x hx =>
  (h x hx).imp $ fun a ⟨ha, _⟩ => ⟨Set.mem_univ _, ha⟩

/-! ### The operator norm -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The operator norm of a seminormed group homomorphism is the inf of all its bounds. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `op_norm [])
  (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.app `NormedGroupHom [`V₁ `V₂])] [] ")")] [])
  (Command.declValSimple
   ":="
   (Term.app
    `Inf
    [(Set.«term{_|_}»
      "{"
      `c
      "|"
      («term_∧_»
       («term_≤_» (numLit "0") "≤" `c)
       "∧"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`x] [])]
        ","
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
         "≤"
         (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
      "}")])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Inf
   [(Set.«term{_|_}»
     "{"
     `c
     "|"
     («term_∧_»
      («term_≤_» (numLit "0") "≤" `c)
      "∧"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [])]
       ","
       («term_≤_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
        "≤"
        (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
     "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `c
   "|"
   («term_∧_»
    («term_≤_» (numLit "0") "≤" `c)
    "∧"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`x] [])]
     ","
     («term_≤_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_≤_» (numLit "0") "≤" `c)
   "∧"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`x] [])]
    ","
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
     "≤"
     (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [])]
   ","
   («term_≤_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
    "≤"
    (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_≤_» (numLit "0") "≤" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The operator norm of a seminormed group homomorphism is the inf of all its bounds. -/
  def op_norm ( f : NormedGroupHom V₁ V₂ ) := Inf { c | 0 ≤ c ∧ ∀ x , ∥ f x ∥ ≤ c * ∥ x ∥ }

instance has_op_norm : HasNorm (NormedGroupHom V₁ V₂) :=
  ⟨op_norm⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `norm_def [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")
     "="
     (Term.app
      `Inf
      [(Set.«term{_|_}»
        "{"
        `c
        "|"
        («term_∧_»
         («term_≤_» (numLit "0") "≤" `c)
         "∧"
         (Term.forall
          "∀"
          [(Term.simpleBinder [`x] [])]
          ","
          («term_≤_»
           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
        "}")]))))
  (Command.declValSimple ":=" `rfl [])
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
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")
   "="
   (Term.app
    `Inf
    [(Set.«term{_|_}»
      "{"
      `c
      "|"
      («term_∧_»
       («term_≤_» (numLit "0") "≤" `c)
       "∧"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`x] [])]
        ","
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
         "≤"
         (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
      "}")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Inf
   [(Set.«term{_|_}»
     "{"
     `c
     "|"
     («term_∧_»
      («term_≤_» (numLit "0") "≤" `c)
      "∧"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [])]
       ","
       («term_≤_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
        "≤"
        (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
     "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `c
   "|"
   («term_∧_»
    («term_≤_» (numLit "0") "≤" `c)
    "∧"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`x] [])]
     ","
     («term_≤_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_≤_» (numLit "0") "≤" `c)
   "∧"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`x] [])]
    ","
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
     "≤"
     (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [])]
   ","
   («term_≤_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
    "≤"
    (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_≤_» (numLit "0") "≤" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
theorem norm_def : ∥ f ∥ = Inf { c | 0 ≤ c ∧ ∀ x , ∥ f x ∥ ≤ c * ∥ x ∥ } := rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `bounds_nonempty [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.app `NormedGroupHom [`V₁ `V₂])] "}")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
     ","
     (Init.Core.«term_∈_»
      `c
      " ∈ "
      (Set.«term{_|_}»
       "{"
       `c
       "|"
       («term_∧_»
        («term_≤_» (numLit "0") "≤" `c)
        "∧"
        (Term.forall
         "∀"
         [(Term.simpleBinder [`x] [])]
         ","
         («term_≤_»
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
          "≤"
          (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
       "}")))))
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`M "," `hMp "," `hMb] "⟩") [] [] ":=" `f.bound))
    []
    (Term.anonymousCtor "⟨" [`M "," (Term.app `le_of_ltₓ [`hMp]) "," `hMb] "⟩"))
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
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`M "," `hMp "," `hMb] "⟩") [] [] ":=" `f.bound))
   []
   (Term.anonymousCtor "⟨" [`M "," (Term.app `le_of_ltₓ [`hMp]) "," `hMb] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`M "," (Term.app `le_of_ltₓ [`hMp]) "," `hMb] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hMb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_of_ltₓ [`hMp])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hMp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_of_ltₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  `f.bound
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`M "," `hMp "," `hMb] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hMb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hMp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
   ","
   (Init.Core.«term_∈_»
    `c
    " ∈ "
    (Set.«term{_|_}»
     "{"
     `c
     "|"
     («term_∧_»
      («term_≤_» (numLit "0") "≤" `c)
      "∧"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [])]
       ","
       («term_≤_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
        "≤"
        (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
     "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_»
   `c
   " ∈ "
   (Set.«term{_|_}»
    "{"
    `c
    "|"
    («term_∧_»
     («term_≤_» (numLit "0") "≤" `c)
     "∧"
     (Term.forall
      "∀"
      [(Term.simpleBinder [`x] [])]
      ","
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
       "≤"
       (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `c
   "|"
   («term_∧_»
    («term_≤_» (numLit "0") "≤" `c)
    "∧"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`x] [])]
     ","
     («term_≤_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_≤_» (numLit "0") "≤" `c)
   "∧"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`x] [])]
    ","
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
     "≤"
     (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [])]
   ","
   («term_≤_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
    "≤"
    (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_≤_» (numLit "0") "≤" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
  bounds_nonempty
  { f : NormedGroupHom V₁ V₂ } : ∃ c , c ∈ { c | 0 ≤ c ∧ ∀ x , ∥ f x ∥ ≤ c * ∥ x ∥ }
  := let ⟨ M , hMp , hMb ⟩ := f.bound ⟨ M , le_of_ltₓ hMp , hMb ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `bounds_bdd_below [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.app `NormedGroupHom [`V₁ `V₂])] "}")]
   (Term.typeSpec
    ":"
    (Term.app
     `BddBelow
     [(Set.«term{_|_}»
       "{"
       `c
       "|"
       («term_∧_»
        («term_≤_» (numLit "0") "≤" `c)
        "∧"
        (Term.forall
         "∀"
         [(Term.simpleBinder [`x] [])]
         ","
         («term_≤_»
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
          "≤"
          (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
       "}")])))
  (Command.declValSimple
   ":="
   (Term.anonymousCtor
    "⟨"
    [(numLit "0")
     ","
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [(Term.hole "_")] []) (Term.anonymousCtor "⟨" [`hn "," (Term.hole "_")] "⟩")]
       "=>"
       `hn))]
    "⟩")
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
  (Term.anonymousCtor
   "⟨"
   [(numLit "0")
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [(Term.hole "_")] []) (Term.anonymousCtor "⟨" [`hn "," (Term.hole "_")] "⟩")]
      "=>"
      `hn))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [(Term.hole "_")] []) (Term.anonymousCtor "⟨" [`hn "," (Term.hole "_")] "⟩")]
    "=>"
    `hn))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`hn "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `BddBelow
   [(Set.«term{_|_}»
     "{"
     `c
     "|"
     («term_∧_»
      («term_≤_» (numLit "0") "≤" `c)
      "∧"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [])]
       ","
       («term_≤_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
        "≤"
        (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
     "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `c
   "|"
   («term_∧_»
    («term_≤_» (numLit "0") "≤" `c)
    "∧"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`x] [])]
     ","
     («term_≤_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_≤_» (numLit "0") "≤" `c)
   "∧"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`x] [])]
    ","
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
     "≤"
     (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [])]
   ","
   («term_≤_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
    "≤"
    (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `c "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_≤_» (numLit "0") "≤" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
  bounds_bdd_below
  { f : NormedGroupHom V₁ V₂ } : BddBelow { c | 0 ≤ c ∧ ∀ x , ∥ f x ∥ ≤ c * ∥ x ∥ }
  := ⟨ 0 , fun _ ⟨ hn , _ ⟩ => hn ⟩

theorem op_norm_nonneg : 0 ≤ ∥f∥ :=
  le_cInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

/--  The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm (x : V₁) : ∥f x∥ ≤ ∥f∥*∥x∥ := by
  obtain ⟨C, Cpos, hC⟩ := f.bound
  replace hC := hC x
  by_cases' h : ∥x∥ = 0
  ·
    rwa [h, mul_zero] at hC⊢
  have hlt : 0 < ∥x∥ := lt_of_le_of_neₓ (norm_nonneg x) (Ne.symm h)
  exact
    (div_le_iff hlt).mp
      (le_cInf bounds_nonempty fun c ⟨_, hc⟩ =>
        (div_le_iff hlt).mpr $ by
          apply hc)

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥*c :=
  le_transₓ (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

theorem le_of_op_norm_le {c : ℝ} (h : ∥f∥ ≤ c) (x : V₁) : ∥f x∥ ≤ c*∥x∥ :=
  (f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))

/--  continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : LipschitzWith ⟨∥f∥, op_norm_nonneg f⟩ f :=
  LipschitzWith.of_dist_le_mul $ fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    apply le_op_norm

protected theorem UniformContinuous (f : NormedGroupHom V₁ V₂) : UniformContinuous f :=
  f.lipschitz.uniform_continuous

@[continuity]
protected theorem Continuous (f : NormedGroupHom V₁ V₂) : Continuous f :=
  f.uniform_continuous.continuous

theorem ratio_le_op_norm (x : V₁) : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)

/--  If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem op_norm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M*∥x∥) : ∥f∥ ≤ M :=
  cInf_le bounds_bdd_below ⟨hMp, hM⟩

theorem op_norm_eq_of_bounds {M : ℝ} (M_nonneg : 0 ≤ M) (h_above : ∀ x, ∥f x∥ ≤ M*∥x∥)
    (h_below : ∀, ∀ N ≥ 0, ∀, (∀ x, ∥f x∥ ≤ N*∥x∥) → M ≤ N) : ∥f∥ = M :=
  le_antisymmₓ (f.op_norm_le_bound M_nonneg h_above)
    ((le_cInf_iff NormedGroupHom.bounds_bdd_below ⟨M, M_nonneg, h_above⟩).mpr $ fun N ⟨N_nonneg, hN⟩ =>
      h_below N N_nonneg hN)

theorem op_norm_le_of_lipschitz {f : NormedGroupHom V₁ V₂} {K : ℝ≥0 } (hf : LipschitzWith K f) : ∥f∥ ≤ K :=
  f.op_norm_le_bound K.2 $ fun x => by
    simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

/--  If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`mk_normed_group_hom`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem mk_normed_group_hom_norm_le (f : V₁ →+ V₂) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) :
    ∥f.mk_normed_group_hom C h∥ ≤ C :=
  op_norm_le_bound _ hC h

/--  If a bounded group homomorphism map is constructed from a group homomorphism
via the constructor `mk_normed_group_hom`, then its norm is bounded by the bound
given to the constructor or zero if this bound is negative. -/
theorem mk_normed_group_hom_norm_le' (f : V₁ →+ V₂) {C : ℝ} (h : ∀ x, ∥f x∥ ≤ C*∥x∥) :
    ∥f.mk_normed_group_hom C h∥ ≤ max C 0 :=
  op_norm_le_bound _ (le_max_rightₓ _ _) $ fun x =>
    (h x).trans $ mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (norm_nonneg x)

alias mk_normed_group_hom_norm_le ← AddMonoidHom.mk_normed_group_hom_norm_le

alias mk_normed_group_hom_norm_le' ← AddMonoidHom.mk_normed_group_hom_norm_le'

/-! ### Addition of normed group homs -/


/--  Addition of normed group homs. -/
instance : Add (NormedGroupHom V₁ V₂) :=
  ⟨fun f g =>
    (f.to_add_monoid_hom+g.to_add_monoid_hom).mkNormedGroupHom (∥f∥+∥g∥) $ fun v =>
      calc ∥f v+g v∥ ≤ ∥f v∥+∥g v∥ := norm_add_le _ _
        _ ≤ (∥f∥*∥v∥)+∥g∥*∥v∥ := add_le_add (le_op_norm f v) (le_op_norm g v)
        _ = (∥f∥+∥g∥)*∥v∥ := by
        rw [add_mulₓ]
        ⟩

/--  The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f+g∥ ≤ ∥f∥+∥g∥ :=
  mk_normed_group_hom_norm_le _ (add_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

/-- 
Terms containing `@has_add.add (has_coe_to_fun.F ...) pi.has_add`
seem to cause leanchecker to [crash due to an out-of-memory
condition](https://github.com/leanprover-community/lean/issues/543).
As a workaround, we add a type annotation: `(f + g : V₁ → V₂)`
-/
library_note "addition on function coercions"

@[simp]
theorem coe_add (f g : NormedGroupHom V₁ V₂) : (⇑f+g) = (f+g : V₁ → V₂) :=
  rfl

@[simp]
theorem add_apply (f g : NormedGroupHom V₁ V₂) (v : V₁) : (f+g : NormedGroupHom V₁ V₂) v = f v+g v :=
  rfl

/-! ### The zero normed group hom -/


instance : HasZero (NormedGroupHom V₁ V₂) :=
  ⟨(0 : V₁ →+ V₂).mkNormedGroupHom 0
      (by
        simp )⟩

instance : Inhabited (NormedGroupHom V₁ V₂) :=
  ⟨0⟩

/--  The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ∥(0 : NormedGroupHom V₁ V₂)∥ = 0 :=
  le_antisymmₓ
    (cInf_le bounds_bdd_below
      ⟨ge_of_eq rfl, fun _ =>
        le_of_eqₓ
          (by
            rw [zero_mul]
            exact norm_zero)⟩)
    (op_norm_nonneg _)

/--  For normed groups, an operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff {V₁ V₂ : Type _} [NormedGroup V₁] [NormedGroup V₂] {f : NormedGroupHom V₁ V₂} :
    ∥f∥ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ext fun x =>
        norm_le_zero_iff.1
          (calc _ ≤ ∥f∥*∥x∥ := le_op_norm _ _
            _ = _ := by
            rw [hn, zero_mul]
            ))
    fun hf => by
    rw [hf, op_norm_zero]

@[simp]
theorem coe_zero : ⇑(0 : NormedGroupHom V₁ V₂) = (0 : V₁ → V₂) :=
  rfl

@[simp]
theorem zero_apply (v : V₁) : (0 : NormedGroupHom V₁ V₂) v = 0 :=
  rfl

variable {f g}

/-! ### The identity normed group hom -/


variable (V)

/--  The identity as a continuous normed group hom. -/
@[simps]
def id : NormedGroupHom V V :=
  (AddMonoidHom.id V).mkNormedGroupHom 1
    (by
      simp [le_reflₓ])

/--  The norm of the identity is at most `1`. It is in fact `1`, except when the norm of every
element vanishes, where it is `0`. (Since we are working with seminorms this can happen even if the
space is non-trivial.) It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ∥(id V : NormedGroupHom V V)∥ ≤ 1 :=
  op_norm_le_bound _ zero_le_one fun x => by
    simp

/--  If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : V, ∥x∥ ≠ 0) : ∥id V∥ = 1 :=
  le_antisymmₓ (norm_id_le V) $
    let ⟨x, hx⟩ := h
    have := (id V).ratio_le_op_norm x
    by
    rwa [id_apply, div_self hx] at this

/--  If a normed space is non-trivial, then the norm of the identity equals `1`. -/
theorem norm_id {V : Type _} [NormedGroup V] [Nontrivial V] : ∥id V∥ = 1 := by
  refine' norm_id_of_nontrivial_seminorm V _
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact ⟨x, ne_of_gtₓ (norm_pos_iff.2 hx)⟩

theorem coe_id : (NormedGroupHom.id V : V → V) = (_root_.id : V → V) :=
  rfl

/-! ### The negation of a normed group hom -/


/--  Opposite of a normed group hom. -/
instance : Neg (NormedGroupHom V₁ V₂) :=
  ⟨fun f =>
    (-f.to_add_monoid_hom).mkNormedGroupHom ∥f∥ fun v => by
      simp [le_op_norm f v]⟩

@[simp]
theorem coe_neg (f : NormedGroupHom V₁ V₂) : ⇑(-f) = (-f : V₁ → V₂) :=
  rfl

@[simp]
theorem neg_apply (f : NormedGroupHom V₁ V₂) (v : V₁) : (-f : NormedGroupHom V₁ V₂) v = -f v :=
  rfl

theorem op_norm_neg (f : NormedGroupHom V₁ V₂) : ∥-f∥ = ∥f∥ := by
  simp only [norm_def, coe_neg, norm_neg, Pi.neg_apply]

/-! ### Subtraction of normed group homs -/


/--  Subtraction of normed group homs. -/
instance : Sub (NormedGroupHom V₁ V₂) :=
  ⟨fun f g =>
    { f.to_add_monoid_hom - g.to_add_monoid_hom with
      bound' := by
        simp only [AddMonoidHom.sub_apply, AddMonoidHom.to_fun_eq_coe, sub_eq_add_neg]
        exact (f+-g).bound' }⟩

@[simp]
theorem coe_sub (f g : NormedGroupHom V₁ V₂) : ⇑(f - g) = (f - g : V₁ → V₂) :=
  rfl

@[simp]
theorem sub_apply (f g : NormedGroupHom V₁ V₂) (v : V₁) : (f - g : NormedGroupHom V₁ V₂) v = f v - g v :=
  rfl

/-! ### Normed group structure on normed group homs -/


/--  Homs between two given normed groups form a commutative additive group. -/
instance : AddCommGroupₓ (NormedGroupHom V₁ V₂) :=
  coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) fun _ _ => rfl

/--  Normed group homomorphisms themselves form a seminormed group with respect to
    the operator norm. -/
instance to_semi_normed_group : SemiNormedGroup (NormedGroupHom V₁ V₂) :=
  SemiNormedGroup.ofCore _ ⟨op_norm_zero, op_norm_add_le, op_norm_neg⟩

/--  Normed group homomorphisms themselves form a normed group with respect to
    the operator norm. -/
instance to_normed_group {V₁ V₂ : Type _} [NormedGroup V₁] [NormedGroup V₂] : NormedGroup (NormedGroupHom V₁ V₂) :=
  NormedGroup.ofCore _ ⟨fun f => op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

/--  Coercion of a `normed_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn` -/
@[simps]
def coe_fn_add_hom : NormedGroupHom V₁ V₂ →+ V₁ → V₂ :=
  { toFun := coeFn, map_zero' := coe_zero, map_add' := coe_add }

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
  (Command.declId `coe_sum [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" (Term.app `NormedGroupHom [`V₁ `V₂]))] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Init.Coe.«term⇑_»
      "⇑"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i])))
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `f [`i])))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj
     (Term.paren
      "("
      [`coe_fn_add_hom
       [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→+_» (Term.hole "_") " →+ " (Term.arrow `V₁ "→" `V₂)))]]
      ")")
     "."
     `map_sum)
    [`f `s])
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
   (Term.proj
    (Term.paren
     "("
     [`coe_fn_add_hom
      [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→+_» (Term.hole "_") " →+ " (Term.arrow `V₁ "→" `V₂)))]]
     ")")
    "."
    `map_sum)
   [`f `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.paren
    "("
    [`coe_fn_add_hom
     [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→+_» (Term.hole "_") " →+ " (Term.arrow `V₁ "→" `V₂)))]]
    ")")
   "."
   `map_sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [`coe_fn_add_hom
    [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→+_» (Term.hole "_") " →+ " (Term.arrow `V₁ "→" `V₂)))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Hom.«term_→+_» (Term.hole "_") " →+ " (Term.arrow `V₁ "→" `V₂))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Hom.«term_→+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow `V₁ "→" `V₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `V₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `V₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `coe_fn_add_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Init.Coe.«term⇑_»
    "⇑"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i])))
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Term.app `f [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
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
@[ simp ]
  theorem
    coe_sum
    { ι : Type _ } ( s : Finset ι ) ( f : ι → NormedGroupHom V₁ V₂ ) : ⇑ ∑ i in s , f i = ∑ i in s , f i
    := ( coe_fn_add_hom : _ →+ V₁ → V₂ ) . map_sum f s

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_apply [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" (Term.app `NormedGroupHom [`V₁ `V₂]))] [] ")")
    (Term.explicitBinder "(" [`v] [":" `V₁] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i]))
      [`v])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `f [`i `v])))))
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
         ["[" [(Tactic.simpLemma [] [] `coe_sum) "," (Tactic.simpLemma [] [] `Finset.sum_apply)] "]"]
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
        ["[" [(Tactic.simpLemma [] [] `coe_sum) "," (Tactic.simpLemma [] [] `Finset.sum_apply)] "]"]
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
   ["[" [(Tactic.simpLemma [] [] `coe_sum) "," (Tactic.simpLemma [] [] `Finset.sum_apply)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coe_sum
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
   (Term.app
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i]))
    [`v])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Term.app `f [`i `v])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i `v]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `v
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
  sum_apply
  { ι : Type _ } ( s : Finset ι ) ( f : ι → NormedGroupHom V₁ V₂ ) ( v : V₁ ) : ∑ i in s , f i v = ∑ i in s , f i v
  := by simp only [ coe_sum , Finset.sum_apply ]

/-! ### Composition of normed group homs -/


/--  The composition of continuous normed group homs. -/
@[simps]
protected def comp (g : NormedGroupHom V₂ V₃) (f : NormedGroupHom V₁ V₂) : NormedGroupHom V₁ V₃ :=
  (g.to_add_monoid_hom.comp f.to_add_monoid_hom).mkNormedGroupHom (∥g∥*∥f∥) $ fun v =>
    calc ∥g (f v)∥ ≤ ∥g∥*∥f v∥ := le_op_norm _ _
      _ ≤ ∥g∥*∥f∥*∥v∥ := mul_le_mul_of_nonneg_left (le_op_norm _ _) (op_norm_nonneg _)
      _ = (∥g∥*∥f∥)*∥v∥ := by
      rw [mul_assocₓ]
      

theorem norm_comp_le (g : NormedGroupHom V₂ V₃) (f : NormedGroupHom V₁ V₂) : ∥g.comp f∥ ≤ ∥g∥*∥f∥ :=
  mk_normed_group_hom_norm_le _ (mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

theorem norm_comp_le_of_le {g : NormedGroupHom V₂ V₃} {C₁ C₂ : ℝ} (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
    ∥g.comp f∥ ≤ C₂*C₁ :=
  le_transₓ (norm_comp_le g f) $ mul_le_mul hg hf (norm_nonneg _) (le_transₓ (norm_nonneg _) hg)

theorem norm_comp_le_of_le' {g : NormedGroupHom V₂ V₃} (C₁ C₂ C₃ : ℝ) (h : C₃ = C₂*C₁) (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
    ∥g.comp f∥ ≤ C₃ := by
  rw [h]
  exact norm_comp_le_of_le hg hf

/--  Composition of normed groups hom as an additive group morphism. -/
def comp_hom : NormedGroupHom V₂ V₃ →+ NormedGroupHom V₁ V₂ →+ NormedGroupHom V₁ V₃ :=
  AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by
          intros
          ext
          exact g.map_add _ _))
    (by
      intros
      ext
      simp only [comp_apply, Pi.add_apply, Function.comp_app, AddMonoidHom.add_apply, AddMonoidHom.mk'_apply, coe_add])

@[simp]
theorem comp_zero (f : NormedGroupHom V₂ V₃) : f.comp (0 : NormedGroupHom V₁ V₂) = 0 := by
  ext
  exact f.map_zero

@[simp]
theorem zero_comp (f : NormedGroupHom V₁ V₂) : (0 : NormedGroupHom V₂ V₃).comp f = 0 := by
  ext
  rfl

theorem comp_assoc {V₄ : Type _} [SemiNormedGroup V₄] (h : NormedGroupHom V₃ V₄) (g : NormedGroupHom V₂ V₃)
    (f : NormedGroupHom V₁ V₂) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

theorem coe_comp (f : NormedGroupHom V₁ V₂) (g : NormedGroupHom V₂ V₃) :
    (g.comp f : V₁ → V₃) = ((g : V₂ → V₃) ∘ (f : V₁ → V₂)) :=
  rfl

end NormedGroupHom

namespace NormedGroupHom

variable {V W V₁ V₂ V₃ : Type _}

variable [SemiNormedGroup V] [SemiNormedGroup W] [SemiNormedGroup V₁] [SemiNormedGroup V₂] [SemiNormedGroup V₃]

/--  The inclusion of an `add_subgroup`, as bounded group homomorphism. -/
@[simps]
def incl (s : AddSubgroup V) : NormedGroupHom s V :=
  { toFun := (coeₓ : s → V), map_add' := fun v w => AddSubgroup.coe_add _ _ _,
    bound' :=
      ⟨1, fun v => by
        rw [one_mulₓ]
        rfl⟩ }

theorem norm_incl {V' : AddSubgroup V} (x : V') : ∥incl _ x∥ = ∥x∥ :=
  rfl

/-!### Kernel -/


section Kernels

variable (f : NormedGroupHom V₁ V₂) (g : NormedGroupHom V₂ V₃)

/--  The kernel of a bounded group homomorphism. Naturally endowed with a
`semi_normed_group` instance. -/
def ker : AddSubgroup V₁ :=
  f.to_add_monoid_hom.ker

theorem mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 := by
  erw [f.to_add_monoid_hom.mem_ker]
  rfl

/--  Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
    the corestriction of `f` to the kernel of `g`. -/
@[simps]
def ker.lift (h : g.comp f = 0) : NormedGroupHom V₁ g.ker :=
  { toFun := fun v =>
      ⟨f v, by
        erw [g.mem_ker]
        show (g.comp f) v = 0
        rw [h]
        rfl⟩,
    map_add' := fun v w => by
      simp only [map_add]
      rfl,
    bound' := f.bound' }

@[simp]
theorem ker.incl_comp_lift (h : g.comp f = 0) : (incl g.ker).comp (ker.lift f g h) = f := by
  ext
  rfl

@[simp]
theorem ker_zero : (0 : NormedGroupHom V₁ V₂).ker = ⊤ := by
  ext
  simp [mem_ker]

theorem coe_ker : (f.ker : Set V₁) = (f : V₁ → V₂) ⁻¹' {0} :=
  rfl

theorem is_closed_ker {V₂ : Type _} [NormedGroup V₂] (f : NormedGroupHom V₁ V₂) : IsClosed (f.ker : Set V₁) :=
  f.coe_ker ▸ IsClosed.preimage f.continuous (T1Space.t1 0)

end Kernels

/-! ### Range -/


section Range

variable (f : NormedGroupHom V₁ V₂) (g : NormedGroupHom V₂ V₃)

/--  The image of a bounded group homomorphism. Naturally endowed with a
`semi_normed_group` instance. -/
def range : AddSubgroup V₂ :=
  f.to_add_monoid_hom.range

theorem mem_range (v : V₂) : v ∈ f.range ↔ ∃ w, f w = v := by
  rw [range, AddMonoidHom.mem_range]
  rfl

@[simp]
theorem mem_range_self (v : V₁) : f v ∈ f.range :=
  ⟨v, rfl⟩

theorem comp_range : (g.comp f).range = AddSubgroup.map g.to_add_monoid_hom f.range := by
  erw [AddMonoidHom.map_range]
  rfl

theorem incl_range (s : AddSubgroup V₁) : (incl s).range = s := by
  ext x
  exact
    ⟨fun ⟨y, hy⟩ => by
      rw [← hy] <;> simp , fun hx =>
      ⟨⟨x, hx⟩, by
        simp ⟩⟩

@[simp]
theorem range_comp_incl_top : (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range := by
  simpa [comp_range, incl_range, ← AddMonoidHom.range_eq_map]

end Range

variable {f : NormedGroupHom V W}

/--  A `normed_group_hom` is *norm-nonincreasing* if `∥f v∥ ≤ ∥v∥` for all `v`. -/
def norm_noninc (f : NormedGroupHom V W) : Prop :=
  ∀ v, ∥f v∥ ≤ ∥v∥

namespace NormNoninc

theorem norm_noninc_iff_norm_le_one : f.norm_noninc ↔ ∥f∥ ≤ 1 := by
  refine' ⟨fun h => _, fun h => fun v => _⟩
  ·
    refine' op_norm_le_bound _ zero_le_one fun v => _
    simpa [one_mulₓ] using h v
  ·
    simpa using le_of_op_norm_le f h v

theorem zero : (0 : NormedGroupHom V₁ V₂).NormNoninc := fun v => by
  simp

theorem id : (id V).NormNoninc := fun v => le_rfl

theorem comp {g : NormedGroupHom V₂ V₃} {f : NormedGroupHom V₁ V₂} (hg : g.norm_noninc) (hf : f.norm_noninc) :
    (g.comp f).NormNoninc := fun v => (hg (f v)).trans (hf v)

@[simp]
theorem neg_iff {f : NormedGroupHom V₁ V₂} : (-f).NormNoninc ↔ f.norm_noninc :=
  ⟨fun h x => by
    simpa using h x, fun h x => (norm_neg (f x)).le.trans (h x)⟩

end NormNoninc

section Isometry

theorem isometry_iff_norm (f : NormedGroupHom V W) : Isometry f ↔ ∀ v, ∥f v∥ = ∥v∥ :=
  AddMonoidHom.isometry_iff_norm f.to_add_monoid_hom

theorem isometry_of_norm (f : NormedGroupHom V W) (hf : ∀ v, ∥f v∥ = ∥v∥) : Isometry f :=
  f.isometry_iff_norm.mpr hf

theorem norm_eq_of_isometry {f : NormedGroupHom V W} (hf : Isometry f) (v : V) : ∥f v∥ = ∥v∥ :=
  f.isometry_iff_norm.mp hf v

theorem isometry_id : @Isometry V V _ _ (id V) :=
  isometry_id

theorem isometry_comp {g : NormedGroupHom V₂ V₃} {f : NormedGroupHom V₁ V₂} (hg : Isometry g) (hf : Isometry f) :
    Isometry (g.comp f) :=
  hg.comp hf

theorem norm_noninc_of_isometry (hf : Isometry f) : f.norm_noninc := fun v => le_of_eqₓ $ norm_eq_of_isometry hf v

end Isometry

variable {W₁ W₂ W₃ : Type _} [SemiNormedGroup W₁] [SemiNormedGroup W₂] [SemiNormedGroup W₃]

variable (f) (g : NormedGroupHom V W)

variable {f₁ g₁ : NormedGroupHom V₁ W₁}

variable {f₂ g₂ : NormedGroupHom V₂ W₂}

variable {f₃ g₃ : NormedGroupHom V₃ W₃}

/--  The equalizer of two morphisms `f g : normed_group_hom V W`. -/
def equalizer :=
  (f - g).ker

namespace Equalizer

/--  The inclusion of `f.equalizer g` as a `normed_group_hom`. -/
def ι : NormedGroupHom (f.equalizer g) V :=
  incl _

theorem comp_ι_eq : f.comp (ι f g) = g.comp (ι f g) := by
  ext
  rw [comp_apply, comp_apply, ← sub_eq_zero, ← NormedGroupHom.sub_apply]
  exact x.2

variable {f g}

/--  If `φ : normed_group_hom V₁ V` is such that `f.comp φ = g.comp φ`, the induced morphism
`normed_group_hom V₁ (f.equalizer g)`. -/
@[simps]
def lift (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) : NormedGroupHom V₁ (f.equalizer g) :=
  { toFun := fun v =>
      ⟨φ v,
        show (f - g) (φ v) = 0 by
          rw [NormedGroupHom.sub_apply, sub_eq_zero, ← comp_apply, h, comp_apply]⟩,
    map_add' := fun v₁ v₂ => by
      ext
      simp only [map_add, AddSubgroup.coe_add, Subtype.coe_mk],
    bound' := by
      obtain ⟨C, C_pos, hC⟩ := φ.bound
      exact ⟨C, hC⟩ }

@[simp]
theorem ι_comp_lift (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) : (ι _ _).comp (lift φ h) = φ := by
  ext
  rfl

/--  The lifting property of the equalizer as an equivalence. -/
@[simps]
def lift_equiv : { φ : NormedGroupHom V₁ V // f.comp φ = g.comp φ } ≃ NormedGroupHom V₁ (f.equalizer g) :=
  { toFun := fun φ => lift φ φ.prop,
    invFun := fun ψ =>
      ⟨(ι f g).comp ψ, by
        rw [← comp_assoc, ← comp_assoc, comp_ι_eq]⟩,
    left_inv := fun φ => by
      simp ,
    right_inv := fun ψ => by
      ext
      rfl }

/--  Given `φ : normed_group_hom V₁ V₂` and `ψ : normed_group_hom W₁ W₂` such that
`ψ.comp f₁ = f₂.comp φ` and `ψ.comp g₁ = g₂.comp φ`, the induced morphism
`normed_group_hom (f₁.equalizer g₁) (f₂.equalizer g₂)`. -/
def map (φ : NormedGroupHom V₁ V₂) (ψ : NormedGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
    (hg : ψ.comp g₁ = g₂.comp φ) : NormedGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
  lift (φ.comp $ ι _ _) $ by
    simp only [← comp_assoc, ← hf, ← hg]
    simp only [comp_assoc, comp_ι_eq]

variable {φ : NormedGroupHom V₁ V₂} {ψ : NormedGroupHom W₁ W₂}

variable {φ' : NormedGroupHom V₂ V₃} {ψ' : NormedGroupHom W₂ W₃}

@[simp]
theorem ι_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
    (ι f₂ g₂).comp (map φ ψ hf hg) = φ.comp (ι _ _) :=
  ι_comp_lift _ _

@[simp]
theorem map_id : map (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁) := by
  ext
  rfl

theorem comm_sq₂ (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ') :
    (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ) := by
  rw [comp_assoc, hf, ← comp_assoc, hf', comp_assoc]

theorem map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ')
    (hg' : ψ'.comp g₂ = g₃.comp φ') :
    (map φ' ψ' hf' hg').comp (map φ ψ hf hg) = map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq₂ hg hg') := by
  ext
  rfl

theorem ι_norm_noninc : (ι f g).NormNoninc := fun v => le_rfl

/--  The lifting of a norm nonincreasing morphism is norm nonincreasing. -/
theorem lift_norm_noninc (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.norm_noninc) :
    (lift φ h).NormNoninc :=
  hφ

/--  If `φ` satisfies `∥φ∥ ≤ C`, then the same is true for the lifted morphism. -/
theorem norm_lift_le (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : ℝ) (hφ : ∥φ∥ ≤ C) : ∥lift φ h∥ ≤ C :=
  hφ

theorem map_norm_noninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (hφ : φ.norm_noninc) :
    (map φ ψ hf hg).NormNoninc :=
  lift_norm_noninc _ _ $ hφ.comp ι_norm_noninc

theorem norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C : ℝ) (hφ : ∥φ.comp (ι f₁ g₁)∥ ≤ C) :
    ∥map φ ψ hf hg∥ ≤ C :=
  norm_lift_le _ _ _ hφ

end Equalizer

end NormedGroupHom

section ControlledClosure

open Filter Finset

open_locale TopologicalSpace

variable {G : Type _} [NormedGroup G] [CompleteSpace G]

variable {H : Type _} [NormedGroup H]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Given `f : normed_group_hom G H` for some complete `G` and a subgroup `K` of `H`, if every\nelement `x` of `K` has a preimage under `f` whose norm is at most `C*∥x∥` then the same holds for\nelements of the (topological) closure of `K` with constant `C+ε` instead of `C`, for any\npositive `ε`.\n-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `controlled_closure_of_complete [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.app `NormedGroupHom [`G `H])] "}")
    (Term.implicitBinder "{" [`K] [":" (Term.app `AddSubgroup [`H])] "}")
    (Term.implicitBinder "{" [`C `ε] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.explicitBinder "(" [`hC] [":" («term_<_» (numLit "0") "<" `C)] [] ")")
    (Term.explicitBinder "(" [`hε] [":" («term_<_» (numLit "0") "<" `ε)] [] ")")
    (Term.explicitBinder "(" [`hyp] [":" (Term.app `f.surjective_on_with [`K `C])] [] ")")]
   (Term.typeSpec ":" (Term.app `f.surjective_on_with [`K.topological_closure (Init.Logic.«term_+_» `C "+" `ε)])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one
           (Tactic.rcasesPat.paren
            "("
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [":" `H])
            ")"))
          (Tactic.rintroPat.one
           (Tactic.rcasesPat.paren
            "("
            (Tactic.rcasesPatLo
             (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h_in)])
             [":" (Init.Core.«term_∈_» `h " ∈ " `K.topological_closure)])
            ")"))]
         [])
        [])
       (group (Tactic.byCases' "by_cases'" [`hyp_h ":"] («term_=_» `h "=" (numLit "0"))) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hyp_h)] "]") []) [])
            (group (Tactic.use "use" [(numLit "0")]) [])
            (group (Tactic.simp "simp" [] [] [] []) [])])))
        [])
       (group
        (Tactic.set
         "set"
         `b
         [":" (Term.arrow (termℕ "ℕ") "→" (Data.Real.Basic.termℝ "ℝ"))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`i] [])]
           "=>"
           («term_/_»
            (Finset.Data.Finset.Fold.«term_*_»
             («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `i)
             "*"
             («term_/_»
              (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
              "/"
              (numLit "2")))
            "/"
            `C)))
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`b_pos []]
           [(Term.typeSpec
             ":"
             (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_<_» (numLit "0") "<" (Term.app `b [`i]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`i]) [])
               (group
                (Tactic.fieldSimp
                 "field_simp"
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `b) "," (Tactic.simpLemma [] [] `hC)] "]"]
                 []
                 [])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `div_pos
                  [(Term.app `mul_pos [`hε (Term.app `norm_pos_iff.mpr [`hyp_h])])
                   (Term.app
                    `mul_pos
                    [(Term.paren
                      "("
                      [(Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                       [(Term.typeAscription
                         ":"
                         («term_<_»
                          (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                          "<"
                          (Finset.Data.Finset.Fold.«term_*_» («term_^_» (numLit "2") "^" `i) "*" (numLit "2"))))]]
                      ")")
                     `hC])]))
                [])]))))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo
               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `v)])
               [":" (Term.arrow (termℕ "ℕ") "→" `H)])
              ","
              (Tactic.rcasesPatLo
               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `lim_v)])
               [":"
                (Term.app
                 `tendsto
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                    "=>"
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                     " in "
                     (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                     ", "
                     (Term.app `v [`k]))))
                  `at_top
                  (Term.app (Topology.Basic.term𝓝 "𝓝") [`h])])])
              ","
              (Tactic.rcasesPatLo
               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `v_in)])
               [":"
                (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Init.Core.«term_∈_» (Term.app `v [`n]) " ∈ " `K))])
              ","
              (Tactic.rcasesPatLo
               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hv₀)])
               [":"
                («term_<_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» (Term.app `v [(numLit "0")]) "-" `h) "∥")
                 "<"
                 (Term.app `b [(numLit "0")]))])
              ","
              (Tactic.rcasesPatLo
               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hv)])
               [":"
                (Term.forall
                 "∀"
                 []
                 ","
                 (Mathlib.ExtendedBinder.«term∀___,_»
                  "∀"
                  `n
                  (Mathlib.ExtendedBinder.«binderTerm>_» ">" (numLit "0"))
                  ","
                  (Term.forall
                   "∀"
                   []
                   ","
                   («term_<_»
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [`n]) "∥")
                    "<"
                    (Term.app `b [`n])))))])]
             "⟩")])]
         []
         [":=" [(Term.app `controlled_sum_of_mem_closure [`h_in `b_pos])]])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [])]
              ","
              («term∃_,_»
               "∃"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m')] [":" `G]))
               ","
               («term_∧_»
                («term_=_» (Term.app `f [`m']) "=" (Term.app `v [`n]))
                "∧"
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `m' "∥")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_»
                  `C
                  "*"
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [`n]) "∥")))))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             "=>"
             (Term.app `hyp [(Term.app `v [`n]) (Term.app `v_in [`n])]))))))
        [])
       (group (Tactic.choose "choose" [`u `hu `hnorm_u] ["using" `this]) [])
       (group
        (Tactic.set
         "set"
         `s
         [":" (Term.arrow (termℕ "ℕ") "→" `G)]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`n] [])]
           "=>"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
            " in "
            (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
            ", "
            (Term.app `u [`k]))))
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `CauchySeq [`s]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.apply
                 "apply"
                 (Term.app
                  `NormedGroup.cauchy_series_of_le_geometric''
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                   `one_half_lt_one]))
                [])
               (group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one (Tactic.rcasesPat.one `n))
                  (Tactic.rintroPat.one
                   (Tactic.rcasesPat.paren
                    "("
                    (Tactic.rcasesPatLo
                     (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)])
                     [":" («term_≥_» `n "≥" (numLit "1"))])
                    ")"))]
                 [])
                [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_≤_»
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`n]) "∥")
                    "≤"
                    (Finset.Data.Finset.Fold.«term_*_»
                     `C
                     "*"
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [`n]) "∥")))
                   ":="
                   (Term.app `hnorm_u [`n]))
                  (calcStep
                   («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`n])))
                   ":="
                   (Term.app
                    `mul_le_mul_of_nonneg_left
                    [(Term.proj
                      («term_$__» (Term.app `hv [(Term.hole "_")]) "$" (Term.app `nat.succ_le_iff.mp [`hn]))
                      "."
                      `le)
                     `hC.le]))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Finset.Data.Finset.Fold.«term_*_»
                     («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n)
                     "*"
                     («term_/_»
                      (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                      "/"
                      (numLit "2"))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.simp
                         "simp"
                         []
                         []
                         ["["
                          [(Tactic.simpLemma [] [] `b)
                           ","
                           (Tactic.simpLemma [] [] (Term.app `mul_div_cancel' [(Term.hole "_") `hC.ne.symm]))]
                          "]"]
                         [])
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Finset.Data.Finset.Fold.«term_*_»
                     («term_/_»
                      (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                      "/"
                      (numLit "2"))
                     "*"
                     («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n)))
                   ":="
                   (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))])
                [])]))))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `g)]) [":" `G])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hg)]) [])]
             "⟩")])]
         []
         [":=" [(Term.app `cauchy_seq_tendsto_of_complete [`this])]])
        [])
       (group (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`g "," (Term.hole "_") "," (Term.hole "_")] "⟩")) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Rel.Data.Rel.«term_∘_» `f " ∘ " `s)
                   "="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`n] [])]
                     "=>"
                     (Algebra.BigOperators.Basic.«term∑_in_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                      " in "
                      (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                      ", "
                      (Term.app `v [`k]))))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `n)] []) [])
                    (group
                     (Tactic.simp
                      "simp"
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [] `f.map_sum) "," (Tactic.simpLemma [] [] `hu)] "]"]
                      [])
                     [])]))))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`lim_v] []))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               `tendsto_nhds_unique
               [(Term.app (Term.proj (Term.app `f.continuous.tendsto [`g]) "." `comp) [`hg]) `lim_v]))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.suffices'
              "suffices"
              []
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.simpleBinder [`n] [])]
                 ","
                 («term_≤_»
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `s [`n]) "∥")
                  "≤"
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Init.Logic.«term_+_» `C "+" `ε)
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app `le_of_tendsto' [(Term.app `continuous_norm.continuous_at.tendsto.comp [`hg]) `this]))
             [])
            (group (Tactic.intro "intro" [`n]) [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hnorm₀ []]
                [(Term.typeSpec
                  ":"
                  («term_≤_»
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")
                   "≤"
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
                    "+"
                    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        []
                        ":="
                        (calc
                         "calc"
                         [(calcStep
                           («term_≤_»
                            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [(numLit "0")]) "∥")
                            "≤"
                            (Init.Logic.«term_+_»
                             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                             "+"
                             (Analysis.Normed.Group.Basic.«term∥_∥»
                              "∥"
                              («term_-_» (Term.app `v [(numLit "0")]) "-" `h)
                              "∥")))
                           ":="
                           (Term.app `norm_le_insert' [(Term.hole "_") (Term.hole "_")]))
                          (calcStep
                           («term_≤_»
                            (Term.hole "_")
                            "≤"
                            (Init.Logic.«term_+_»
                             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                             "+"
                             (Term.app `b [(numLit "0")])))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group (Tactic.apply "apply" (Term.app `add_le_add_left [`hv₀.le])) [])]))))]))))
                     [])
                    (group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_≤_»
                         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_»
                          `C
                          "*"
                          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [(numLit "0")]) "∥")))
                        ":="
                        (Term.app `hnorm_u [(numLit "0")]))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_»
                          `C
                          "*"
                          (Init.Logic.«term_+_»
                           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                           "+"
                           (Term.app `b [(numLit "0")]))))
                        ":="
                        (Term.app `mul_le_mul_of_nonneg_left [`this `hC.le]))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
                          "+"
                          (Finset.Data.Finset.Fold.«term_*_»
                           `C
                           "*"
                           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
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
                               [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `mul_addₓ)]
                               "]")
                              [])
                             [])]))))])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_≤_»
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                    " in "
                    (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                    ", "
                    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))]
                ":="
                (calc
                 "calc"
                 [(calcStep
                   («term_=_»
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                     " in "
                     (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                     ", "
                     (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
                    "="
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Algebra.BigOperators.Basic.«term∑_in_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                      " in "
                      (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                      ", "
                      («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `k))
                     "*"
                     («term_/_»
                      (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                      "/"
                      (numLit "2"))))
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
                         ["["
                          [(Tactic.simpLemma [] [] `b)
                           ","
                           (Tactic.simpLemma [] [] (Term.app `mul_div_cancel' [(Term.hole "_") `hC.ne.symm]))
                           ","
                           (Tactic.simpLemma [] ["←"] `sum_mul)]
                          "]"]
                         [])
                        [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Finset.Data.Finset.Fold.«term_*_»
                     (numLit "2")
                     "*"
                     («term_/_»
                      (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                      "/"
                      (numLit "2"))))
                   ":="
                   (Term.app
                    `mul_le_mul_of_nonneg_right
                    [(Term.app `sum_geometric_two_le [(Term.hole "_")])
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.nlinarith "nlinarith" [] [] ["[" [`hε "," (Term.app `norm_nonneg [`h])] "]"])
                          [])])))]))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
                   ":="
                   (Term.app `mul_div_cancel' [(Term.hole "_") `two_ne_zero]))]))))
             [])
            (group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `s [`n]) "∥")
                 "≤"
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                  ", "
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`k]) "∥")))
                ":="
                (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Init.Logic.«term_+_»
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   (Term.app `range [`n])
                   ", "
                   (Analysis.Normed.Group.Basic.«term∥_∥»
                    "∥"
                    (Term.app `u [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
                    "∥"))
                  "+"
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
                ":="
                (Term.app `sum_range_succ' [(Term.hole "_") (Term.hole "_")]))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Init.Logic.«term_+_»
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   (Term.app `range [`n])
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_»
                    `C
                    "*"
                    (Analysis.Normed.Group.Basic.«term∥_∥»
                     "∥"
                     (Term.app `v [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
                     "∥")))
                  "+"
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
                ":="
                (Term.app
                 `add_le_add_right
                 [(Term.app
                   `sum_le_sum
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                      "=>"
                      (Term.app `hnorm_u [(Term.hole "_")])))])
                  (Term.hole "_")]))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Init.Logic.«term_+_»
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   (Term.app `range [`n])
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_»
                    `C
                    "*"
                    (Term.app `b [(Init.Logic.«term_+_» `k "+" (numLit "1"))])))
                  "+"
                  (Init.Logic.«term_+_»
                   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
                   "+"
                   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))
                ":="
                (Term.app
                 `add_le_add
                 [(Term.app
                   `sum_le_sum
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`k (Term.hole "_")] [])]
                      "=>"
                      (Term.app
                       `mul_le_mul_of_nonneg_left
                       [(Term.proj (Term.app `hv [(Term.hole "_") `k.succ_pos]) "." `le) `hC.le])))])
                  `hnorm₀]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Init.Logic.«term_+_»
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
                  "+"
                  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
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
                       [(Tactic.rwRule ["←"] `add_assocₓ) "," (Tactic.rwRule [] `sum_range_succ')]
                       "]")
                      [])
                     [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Init.Logic.«term_+_» `C "+" `ε)
                  "*"
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `add_mulₓ)] "]")
                      [])
                     [])
                    (group (Tactic.apply "apply" (Term.app `add_le_add_left [`this])) [])]))))])
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
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.paren
           "("
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [":" `H])
           ")"))
         (Tactic.rintroPat.one
          (Tactic.rcasesPat.paren
           "("
           (Tactic.rcasesPatLo
            (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h_in)])
            [":" (Init.Core.«term_∈_» `h " ∈ " `K.topological_closure)])
           ")"))]
        [])
       [])
      (group (Tactic.byCases' "by_cases'" [`hyp_h ":"] («term_=_» `h "=" (numLit "0"))) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hyp_h)] "]") []) [])
           (group (Tactic.use "use" [(numLit "0")]) [])
           (group (Tactic.simp "simp" [] [] [] []) [])])))
       [])
      (group
       (Tactic.set
        "set"
        `b
        [":" (Term.arrow (termℕ "ℕ") "→" (Data.Real.Basic.termℝ "ℝ"))]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          («term_/_»
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `i)
            "*"
            («term_/_»
             (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
             "/"
             (numLit "2")))
           "/"
           `C)))
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`b_pos []]
          [(Term.typeSpec
            ":"
            (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_<_» (numLit "0") "<" (Term.app `b [`i]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`i]) [])
              (group
               (Tactic.fieldSimp
                "field_simp"
                []
                []
                ["[" [(Tactic.simpLemma [] [] `b) "," (Tactic.simpLemma [] [] `hC)] "]"]
                []
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `div_pos
                 [(Term.app `mul_pos [`hε (Term.app `norm_pos_iff.mpr [`hyp_h])])
                  (Term.app
                   `mul_pos
                   [(Term.paren
                     "("
                     [(Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                      [(Term.typeAscription
                        ":"
                        («term_<_»
                         (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                         "<"
                         (Finset.Data.Finset.Fold.«term_*_» («term_^_» (numLit "2") "^" `i) "*" (numLit "2"))))]]
                     ")")
                    `hC])]))
               [])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo
              (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `v)])
              [":" (Term.arrow (termℕ "ℕ") "→" `H)])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `lim_v)])
              [":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                   "=>"
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                    " in "
                    (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                    ", "
                    (Term.app `v [`k]))))
                 `at_top
                 (Term.app (Topology.Basic.term𝓝 "𝓝") [`h])])])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `v_in)])
              [":"
               (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Init.Core.«term_∈_» (Term.app `v [`n]) " ∈ " `K))])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hv₀)])
              [":"
               («term_<_»
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» (Term.app `v [(numLit "0")]) "-" `h) "∥")
                "<"
                (Term.app `b [(numLit "0")]))])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hv)])
              [":"
               (Term.forall
                "∀"
                []
                ","
                (Mathlib.ExtendedBinder.«term∀___,_»
                 "∀"
                 `n
                 (Mathlib.ExtendedBinder.«binderTerm>_» ">" (numLit "0"))
                 ","
                 (Term.forall
                  "∀"
                  []
                  ","
                  («term_<_»
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [`n]) "∥")
                   "<"
                   (Term.app `b [`n])))))])]
            "⟩")])]
        []
        [":=" [(Term.app `controlled_sum_of_mem_closure [`h_in `b_pos])]])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m')] [":" `G]))
              ","
              («term_∧_»
               («term_=_» (Term.app `f [`m']) "=" (Term.app `v [`n]))
               "∧"
               («term_≤_»
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `m' "∥")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 `C
                 "*"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [`n]) "∥")))))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
            "=>"
            (Term.app `hyp [(Term.app `v [`n]) (Term.app `v_in [`n])]))))))
       [])
      (group (Tactic.choose "choose" [`u `hu `hnorm_u] ["using" `this]) [])
      (group
       (Tactic.set
        "set"
        `s
        [":" (Term.arrow (termℕ "ℕ") "→" `G)]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`n] [])]
          "=>"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
           " in "
           (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
           ", "
           (Term.app `u [`k]))))
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `CauchySeq [`s]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.apply
                "apply"
                (Term.app
                 `NormedGroup.cauchy_series_of_le_geometric''
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                  `one_half_lt_one]))
               [])
              (group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `n))
                 (Tactic.rintroPat.one
                  (Tactic.rcasesPat.paren
                   "("
                   (Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)])
                    [":" («term_≥_» `n "≥" (numLit "1"))])
                   ")"))]
                [])
               [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_≤_»
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`n]) "∥")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_»
                    `C
                    "*"
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [`n]) "∥")))
                  ":="
                  (Term.app `hnorm_u [`n]))
                 (calcStep
                  («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`n])))
                  ":="
                  (Term.app
                   `mul_le_mul_of_nonneg_left
                   [(Term.proj
                     («term_$__» (Term.app `hv [(Term.hole "_")]) "$" (Term.app `nat.succ_le_iff.mp [`hn]))
                     "."
                     `le)
                    `hC.le]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Finset.Data.Finset.Fold.«term_*_»
                    («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n)
                    "*"
                    («term_/_»
                     (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                     "/"
                     (numLit "2"))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.simp
                        "simp"
                        []
                        []
                        ["["
                         [(Tactic.simpLemma [] [] `b)
                          ","
                          (Tactic.simpLemma [] [] (Term.app `mul_div_cancel' [(Term.hole "_") `hC.ne.symm]))]
                         "]"]
                        [])
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Finset.Data.Finset.Fold.«term_*_»
                    («term_/_»
                     (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                     "/"
                     (numLit "2"))
                    "*"
                    («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n)))
                  ":="
                  (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))])
               [])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `g)]) [":" `G])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hg)]) [])]
            "⟩")])]
        []
        [":=" [(Term.app `cauchy_seq_tendsto_of_complete [`this])]])
       [])
      (group (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`g "," (Term.hole "_") "," (Term.hole "_")] "⟩")) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Rel.Data.Rel.«term_∘_» `f " ∘ " `s)
                  "="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`n] [])]
                    "=>"
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                     " in "
                     (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                     ", "
                     (Term.app `v [`k]))))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `n)] []) [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["[" [(Tactic.simpLemma [] [] `f.map_sum) "," (Tactic.simpLemma [] [] `hu)] "]"]
                     [])
                    [])]))))))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`lim_v] []))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              `tendsto_nhds_unique
              [(Term.app (Term.proj (Term.app `f.continuous.tendsto [`g]) "." `comp) [`hg]) `lim_v]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.suffices'
             "suffices"
             []
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.simpleBinder [`n] [])]
                ","
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `s [`n]) "∥")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Init.Logic.«term_+_» `C "+" `ε)
                  "*"
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app `le_of_tendsto' [(Term.app `continuous_norm.continuous_at.tendsto.comp [`hg]) `this]))
            [])
           (group (Tactic.intro "intro" [`n]) [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hnorm₀ []]
               [(Term.typeSpec
                 ":"
                 («term_≤_»
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")
                  "≤"
                  (Init.Logic.«term_+_»
                   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
                   "+"
                   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       []
                       ":="
                       (calc
                        "calc"
                        [(calcStep
                          («term_≤_»
                           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [(numLit "0")]) "∥")
                           "≤"
                           (Init.Logic.«term_+_»
                            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                            "+"
                            (Analysis.Normed.Group.Basic.«term∥_∥»
                             "∥"
                             («term_-_» (Term.app `v [(numLit "0")]) "-" `h)
                             "∥")))
                          ":="
                          (Term.app `norm_le_insert' [(Term.hole "_") (Term.hole "_")]))
                         (calcStep
                          («term_≤_»
                           (Term.hole "_")
                           "≤"
                           (Init.Logic.«term_+_»
                            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                            "+"
                            (Term.app `b [(numLit "0")])))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group (Tactic.apply "apply" (Term.app `add_le_add_left [`hv₀.le])) [])]))))]))))
                    [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_≤_»
                        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")
                        "≤"
                        (Finset.Data.Finset.Fold.«term_*_»
                         `C
                         "*"
                         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [(numLit "0")]) "∥")))
                       ":="
                       (Term.app `hnorm_u [(numLit "0")]))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Finset.Data.Finset.Fold.«term_*_»
                         `C
                         "*"
                         (Init.Logic.«term_+_»
                          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                          "+"
                          (Term.app `b [(numLit "0")]))))
                       ":="
                       (Term.app `mul_le_mul_of_nonneg_left [`this `hC.le]))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
                         "+"
                         (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `mul_addₓ)] "]")
                             [])
                            [])]))))])
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_≤_»
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
                  "≤"
                  (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))]
               ":="
               (calc
                "calc"
                [(calcStep
                  («term_=_»
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                    " in "
                    (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                    ", "
                    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
                   "="
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                     " in "
                     (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                     ", "
                     («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `k))
                    "*"
                    («term_/_»
                     (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                     "/"
                     (numLit "2"))))
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
                        ["["
                         [(Tactic.simpLemma [] [] `b)
                          ","
                          (Tactic.simpLemma [] [] (Term.app `mul_div_cancel' [(Term.hole "_") `hC.ne.symm]))
                          ","
                          (Tactic.simpLemma [] ["←"] `sum_mul)]
                         "]"]
                        [])
                       [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "2")
                    "*"
                    («term_/_»
                     (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                     "/"
                     (numLit "2"))))
                  ":="
                  (Term.app
                   `mul_le_mul_of_nonneg_right
                   [(Term.app `sum_geometric_two_le [(Term.hole "_")])
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.nlinarith "nlinarith" [] [] ["[" [`hε "," (Term.app `norm_nonneg [`h])] "]"])
                         [])])))]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
                  ":="
                  (Term.app `mul_div_cancel' [(Term.hole "_") `two_ne_zero]))]))))
            [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_≤_»
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `s [`n]) "∥")
                "≤"
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                 " in "
                 (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                 ", "
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`k]) "∥")))
               ":="
               (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Init.Logic.«term_+_»
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Term.app `range [`n])
                  ", "
                  (Analysis.Normed.Group.Basic.«term∥_∥»
                   "∥"
                   (Term.app `u [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
                   "∥"))
                 "+"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
               ":="
               (Term.app `sum_range_succ' [(Term.hole "_") (Term.hole "_")]))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Init.Logic.«term_+_»
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Term.app `range [`n])
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   `C
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥»
                    "∥"
                    (Term.app `v [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
                    "∥")))
                 "+"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
               ":="
               (Term.app
                `add_le_add_right
                [(Term.app
                  `sum_le_sum
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                     "=>"
                     (Term.app `hnorm_u [(Term.hole "_")])))])
                 (Term.hole "_")]))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Init.Logic.«term_+_»
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Term.app `range [`n])
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(Init.Logic.«term_+_» `k "+" (numLit "1"))])))
                 "+"
                 (Init.Logic.«term_+_»
                  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
                  "+"
                  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))
               ":="
               (Term.app
                `add_le_add
                [(Term.app
                  `sum_le_sum
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`k (Term.hole "_")] [])]
                     "=>"
                     (Term.app
                      `mul_le_mul_of_nonneg_left
                      [(Term.proj (Term.app `hv [(Term.hole "_") `k.succ_pos]) "." `le) `hC.le])))])
                 `hnorm₀]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Init.Logic.«term_+_»
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
                 "+"
                 (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
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
                      [(Tactic.rwRule ["←"] `add_assocₓ) "," (Tactic.rwRule [] `sum_range_succ')]
                      "]")
                     [])
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Init.Logic.«term_+_» `C "+" `ε)
                 "*"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `add_mulₓ)] "]")
                     [])
                    [])
                   (group (Tactic.apply "apply" (Term.app `add_le_add_left [`this])) [])]))))])
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
     [(group
       (Tactic.suffices'
        "suffices"
        []
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`n] [])]
           ","
           («term_≤_»
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `s [`n]) "∥")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Init.Logic.«term_+_» `C "+" `ε)
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app `le_of_tendsto' [(Term.app `continuous_norm.continuous_at.tendsto.comp [`hg]) `this]))
       [])
      (group (Tactic.intro "intro" [`n]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hnorm₀ []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")
             "≤"
             (Init.Logic.«term_+_»
              (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
              "+"
              (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  []
                  ":="
                  (calc
                   "calc"
                   [(calcStep
                     («term_≤_»
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [(numLit "0")]) "∥")
                      "≤"
                      (Init.Logic.«term_+_»
                       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                       "+"
                       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» (Term.app `v [(numLit "0")]) "-" `h) "∥")))
                     ":="
                     (Term.app `norm_le_insert' [(Term.hole "_") (Term.hole "_")]))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      (Init.Logic.«term_+_»
                       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                       "+"
                       (Term.app `b [(numLit "0")])))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.apply "apply" (Term.app `add_le_add_left [`hv₀.le])) [])]))))]))))
               [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_≤_»
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_»
                    `C
                    "*"
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [(numLit "0")]) "∥")))
                  ":="
                  (Term.app `hnorm_u [(numLit "0")]))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_»
                    `C
                    "*"
                    (Init.Logic.«term_+_»
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
                     "+"
                     (Term.app `b [(numLit "0")]))))
                  ":="
                  (Term.app `mul_le_mul_of_nonneg_left [`this `hC.le]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
                    "+"
                    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `mul_addₓ)] "]")
                        [])
                       [])]))))])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_≤_»
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
              " in "
              (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
              ", "
              (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
             "≤"
             (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))]
          ":="
          (calc
           "calc"
           [(calcStep
             («term_=_»
              (Algebra.BigOperators.Basic.«term∑_in_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
               " in "
               (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
               ", "
               (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
              "="
              (Finset.Data.Finset.Fold.«term_*_»
               (Algebra.BigOperators.Basic.«term∑_in_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                " in "
                (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                ", "
                («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `k))
               "*"
               («term_/_»
                (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                "/"
                (numLit "2"))))
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
                   ["["
                    [(Tactic.simpLemma [] [] `b)
                     ","
                     (Tactic.simpLemma [] [] (Term.app `mul_div_cancel' [(Term.hole "_") `hC.ne.symm]))
                     ","
                     (Tactic.simpLemma [] ["←"] `sum_mul)]
                    "]"]
                   [])
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              (Finset.Data.Finset.Fold.«term_*_»
               (numLit "2")
               "*"
               («term_/_»
                (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
                "/"
                (numLit "2"))))
             ":="
             (Term.app
              `mul_le_mul_of_nonneg_right
              [(Term.app `sum_geometric_two_le [(Term.hole "_")])
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.nlinarith "nlinarith" [] [] ["[" [`hε "," (Term.app `norm_nonneg [`h])] "]"])
                    [])])))]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Finset.Data.Finset.Fold.«term_*_» `ε "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
             ":="
             (Term.app `mul_div_cancel' [(Term.hole "_") `two_ne_zero]))]))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `s [`n]) "∥")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
            " in "
            (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
            ", "
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`k]) "∥")))
          ":="
          (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Init.Logic.«term_+_»
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Term.app `range [`n])
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(Init.Logic.«term_+_» `k "+" (numLit "1"))]) "∥"))
            "+"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
          ":="
          (Term.app `sum_range_succ' [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Init.Logic.«term_+_»
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Term.app `range [`n])
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              `C
              "*"
              (Analysis.Normed.Group.Basic.«term∥_∥»
               "∥"
               (Term.app `v [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
               "∥")))
            "+"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
          ":="
          (Term.app
           `add_le_add_right
           [(Term.app
             `sum_le_sum
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                "=>"
                (Term.app `hnorm_u [(Term.hole "_")])))])
            (Term.hole "_")]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Init.Logic.«term_+_»
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Term.app `range [`n])
             ", "
             (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(Init.Logic.«term_+_» `k "+" (numLit "1"))])))
            "+"
            (Init.Logic.«term_+_»
             (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
             "+"
             (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))
          ":="
          (Term.app
           `add_le_add
           [(Term.app
             `sum_le_sum
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`k (Term.hole "_")] [])]
                "=>"
                (Term.app
                 `mul_le_mul_of_nonneg_left
                 [(Term.proj (Term.app `hv [(Term.hole "_") `k.succ_pos]) "." `le) `hC.le])))])
            `hnorm₀]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Init.Logic.«term_+_»
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
             ", "
             (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
            "+"
            (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `add_assocₓ) "," (Tactic.rwRule [] `sum_range_succ')] "]")
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Init.Logic.«term_+_» `C "+" `ε)
            "*"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `add_mulₓ)] "]")
                [])
               [])
              (group (Tactic.apply "apply" (Term.app `add_le_add_left [`this])) [])]))))])
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
     («term_≤_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `s [`n]) "∥")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
       ", "
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`k]) "∥")))
     ":="
     (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Init.Logic.«term_+_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `range [`n])
        ", "
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(Init.Logic.«term_+_» `k "+" (numLit "1"))]) "∥"))
       "+"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
     ":="
     (Term.app `sum_range_succ' [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Init.Logic.«term_+_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `range [`n])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         `C
         "*"
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v [(Init.Logic.«term_+_» `k "+" (numLit "1"))]) "∥")))
       "+"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(numLit "0")]) "∥")))
     ":="
     (Term.app
      `add_le_add_right
      [(Term.app
        `sum_le_sum
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
           "=>"
           (Term.app `hnorm_u [(Term.hole "_")])))])
       (Term.hole "_")]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Init.Logic.«term_+_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `range [`n])
        ", "
        (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(Init.Logic.«term_+_» `k "+" (numLit "1"))])))
       "+"
       (Init.Logic.«term_+_»
        (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [(numLit "0")]))
        "+"
        (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))))
     ":="
     (Term.app
      `add_le_add
      [(Term.app
        `sum_le_sum
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`k (Term.hole "_")] [])]
           "=>"
           (Term.app
            `mul_le_mul_of_nonneg_left
            [(Term.proj (Term.app `hv [(Term.hole "_") `k.succ_pos]) "." `le) `hC.le])))])
       `hnorm₀]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Init.Logic.«term_+_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
       "+"
       (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `add_assocₓ) "," (Tactic.rwRule [] `sum_range_succ')] "]")
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Init.Logic.«term_+_» `C "+" `ε)
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `add_mulₓ)] "]")
           [])
          [])
         (group (Tactic.apply "apply" (Term.app `add_le_add_left [`this])) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `add_mulₓ)] "]")
        [])
       [])
      (group (Tactic.apply "apply" (Term.app `add_le_add_left [`this])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" (Term.app `add_le_add_left [`this]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `add_le_add_left [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_commₓ) "," (Tactic.rwRule [] `add_mulₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_mulₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    (Init.Logic.«term_+_» `C "+" `ε)
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Init.Logic.«term_+_» `C "+" `ε)
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Init.Logic.«term_+_» `C "+" `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `C "+" `ε) []] ")")
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
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `add_assocₓ) "," (Tactic.rwRule [] `sum_range_succ')] "]")
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
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `add_assocₓ) "," (Tactic.rwRule [] `sum_range_succ')] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_range_succ'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Init.Logic.«term_+_»
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
     " in "
     (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
     ", "
     (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
    "+"
    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
    " in "
    (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
    ", "
    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
   "+"
   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `h "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   " in "
   (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
   ", "
   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Term.app `b [`k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `b [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    Given `f : normed_group_hom G H` for some complete `G` and a subgroup `K` of `H`, if every
    element `x` of `K` has a preimage under `f` whose norm is at most `C*∥x∥` then the same holds for
    elements of the (topological) closure of `K` with constant `C+ε` instead of `C`, for any
    positive `ε`.
    -/
  theorem
    controlled_closure_of_complete
    { f : NormedGroupHom G H }
        { K : AddSubgroup H }
        { C ε : ℝ }
        ( hC : 0 < C )
        ( hε : 0 < ε )
        ( hyp : f.surjective_on_with K C )
      : f.surjective_on_with K.topological_closure C + ε
    :=
      by
        rintro ( h : H ) ( h_in : h ∈ K.topological_closure )
          by_cases' hyp_h : h = 0
          · rw [ hyp_h ] use 0 simp
          set b : ℕ → ℝ := fun i => 1 / 2 ^ i * ε * ∥ h ∥ / 2 / C
          have
            b_pos
              : ∀ i , 0 < b i
              :=
              by
                intro i
                  field_simp [ b , hC ]
                  exact div_pos mul_pos hε norm_pos_iff.mpr hyp_h mul_pos ( by norm_num : ( 0 : ℝ ) < 2 ^ i * 2 ) hC
          obtain
            ⟨
              v : ℕ → H
                ,
                lim_v : tendsto fun n : ℕ => ∑ k in range n + 1 , v k at_top 𝓝 h
                ,
                v_in : ∀ n , v n ∈ K
                ,
                hv₀ : ∥ v 0 - h ∥ < b 0
                ,
                hv : ∀ , ∀ n > 0 , ∀ , ∥ v n ∥ < b n
              ⟩
            := controlled_sum_of_mem_closure h_in b_pos
          have : ∀ n , ∃ m' : G , f m' = v n ∧ ∥ m' ∥ ≤ C * ∥ v n ∥ := fun n : ℕ => hyp v n v_in n
          choose u hu hnorm_u using this
          set s : ℕ → G := fun n => ∑ k in range n + 1 , u k
          have
            : CauchySeq s
              :=
              by
                apply NormedGroup.cauchy_series_of_le_geometric'' by norm_num one_half_lt_one
                  rintro n ( hn : n ≥ 1 )
                  calc
                    ∥ u n ∥ ≤ C * ∥ v n ∥ := hnorm_u n
                      _ ≤ C * b n := mul_le_mul_of_nonneg_left hv _ $ nat.succ_le_iff.mp hn . le hC.le
                      _ = 1 / 2 ^ n * ε * ∥ h ∥ / 2 := by simp [ b , mul_div_cancel' _ hC.ne.symm ]
                      _ = ε * ∥ h ∥ / 2 * 1 / 2 ^ n := mul_commₓ _ _
          obtain ⟨ g : G , hg ⟩ := cauchy_seq_tendsto_of_complete this
          refine' ⟨ g , _ , _ ⟩
          ·
            have : f ∘ s = fun n => ∑ k in range n + 1 , v k := by ext n simp [ f.map_sum , hu ]
              rw [ ← this ] at lim_v
              exact tendsto_nhds_unique f.continuous.tendsto g . comp hg lim_v
          ·
            suffices : ∀ n , ∥ s n ∥ ≤ C + ε * ∥ h ∥
              exact le_of_tendsto' continuous_norm.continuous_at.tendsto.comp hg this
              intro n
              have
                hnorm₀
                  : ∥ u 0 ∥ ≤ C * b 0 + C * ∥ h ∥
                  :=
                  by
                    have
                        :=
                          calc
                            ∥ v 0 ∥ ≤ ∥ h ∥ + ∥ v 0 - h ∥ := norm_le_insert' _ _
                              _ ≤ ∥ h ∥ + b 0 := by apply add_le_add_left hv₀.le
                      calc
                        ∥ u 0 ∥ ≤ C * ∥ v 0 ∥ := hnorm_u 0
                          _ ≤ C * ∥ h ∥ + b 0 := mul_le_mul_of_nonneg_left this hC.le
                          _ = C * b 0 + C * ∥ h ∥ := by rw [ add_commₓ , mul_addₓ ]
              have
                : ∑ k in range n + 1 , C * b k ≤ ε * ∥ h ∥
                  :=
                  calc
                    ∑ k in range n + 1 , C * b k = ∑ k in range n + 1 , 1 / 2 ^ k * ε * ∥ h ∥ / 2
                        :=
                        by simp only [ b , mul_div_cancel' _ hC.ne.symm , ← sum_mul ]
                      _ ≤ 2 * ε * ∥ h ∥ / 2
                        :=
                        mul_le_mul_of_nonneg_right sum_geometric_two_le _ by nlinarith [ hε , norm_nonneg h ]
                      _ = ε * ∥ h ∥ := mul_div_cancel' _ two_ne_zero
              calc
                ∥ s n ∥ ≤ ∑ k in range n + 1 , ∥ u k ∥ := norm_sum_le _ _
                  _ = ∑ k in range n , ∥ u k + 1 ∥ + ∥ u 0 ∥ := sum_range_succ' _ _
                  _ ≤ ∑ k in range n , C * ∥ v k + 1 ∥ + ∥ u 0 ∥ := add_le_add_right sum_le_sum fun _ _ => hnorm_u _ _
                  _ ≤ ∑ k in range n , C * b k + 1 + C * b 0 + C * ∥ h ∥
                    :=
                    add_le_add sum_le_sum fun k _ => mul_le_mul_of_nonneg_left hv _ k.succ_pos . le hC.le hnorm₀
                  _ = ∑ k in range n + 1 , C * b k + C * ∥ h ∥ := by rw [ ← add_assocₓ , sum_range_succ' ]
                  _ ≤ C + ε * ∥ h ∥ := by rw [ add_commₓ , add_mulₓ ] apply add_le_add_left this

/--  Given `f : normed_group_hom G H` for some complete `G`, if every element `x` of the image of
an isometric immersion `j : normed_group_hom K H` has a preimage under `f` whose norm is at most
`C*∥x∥` then the same holds for elements of the (topological) closure of this image with constant
`C+ε` instead of `C`, for any positive `ε`.
This is useful in particular if `j` is the inclusion of a normed group into its completion
(in this case the closure is the full target group).
-/
theorem controlled_closure_range_of_complete {f : NormedGroupHom G H} {K : Type _} [SemiNormedGroup K]
    {j : NormedGroupHom K H} (hj : ∀ x, ∥j x∥ = ∥x∥) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hyp : ∀ k, ∃ g, f g = j k ∧ ∥g∥ ≤ C*∥k∥) : f.surjective_on_with j.range.topological_closure (C+ε) := by
  replace hyp : ∀, ∀ h ∈ j.range, ∀, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥
  ·
    intro h h_in
    rcases(j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
  exact controlled_closure_of_complete hC hε hyp

end ControlledClosure

