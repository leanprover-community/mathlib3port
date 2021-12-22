import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.NormedSpace.Star
import Mathbin.Topology.ContinuousFunction.Algebra
import Mathbin.Data.Real.Sqrt
import Mathbin.Analysis.NormedSpace.LatticeOrderedGroup

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with
the uniform distance.

-/


noncomputable section

open_locale TopologicalSpace Classical Nnreal

open Set Filter Metric Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/--  The type of bounded continuous functions from a topological space to a metric space -/
structure BoundedContinuousFunction (α : Type u) (β : Type v) [TopologicalSpace α] [MetricSpace β] extends
  ContinuousMap α β : Type max u v where
  bounded' : ∃ C, ∀ x y : α, dist (to_fun x) (to_fun y) ≤ C

localized [BoundedContinuousFunction] infixr:25 " →ᵇ " => BoundedContinuousFunction

namespace BoundedContinuousFunction

section Basics

variable [TopologicalSpace α] [MetricSpace β] [MetricSpace γ]

variable {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : CoeFun (α →ᵇ β) fun _ => α → β :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem coe_to_continuous_fun (f : α →ᵇ β) : (f.to_continuous_map : α → β) = f :=
  rfl

/--  See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : α →ᵇ β) : α → β :=
  h

initialize_simps_projections BoundedContinuousFunction (to_continuous_map_to_fun → apply)

protected theorem Bounded (f : α →ᵇ β) : ∃ C, ∀ x y : α, dist (f x) (f y) ≤ C :=
  f.bounded'

@[continuity]
protected theorem Continuous (f : α →ᵇ β) : Continuous f :=
  f.to_continuous_map.continuous

@[ext]
theorem ext (H : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  ext
  exact H x

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h => fun x => h ▸ rfl, ext⟩

theorem coe_injective : @injective (α →ᵇ β) (α → β) coeFn := fun f g h => ext $ congr_funₓ h

theorem bounded_range (f : α →ᵇ β) : Bounded (range f) :=
  bounded_range_iff.2 f.bounded

theorem bounded_image (f : α →ᵇ β) (s : Set α) : Bounded (f '' s) :=
  f.bounded_range.mono $ image_subset_range _ _

theorem eq_of_empty [IsEmpty α] (f g : α →ᵇ β) : f = g :=
  ext $ IsEmpty.elim ‹_›

/--  A continuous function with an explicit bound is a bounded continuous function. -/
def mk_of_bound (f : C(α, β)) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
  ⟨f, ⟨C, h⟩⟩

@[simp]
theorem mk_of_bound_coe {f} {C} {h} : (mk_of_bound f C h : α → β) = (f : α → β) :=
  rfl

/--  A continuous function on a compact space is automatically a bounded continuous function. -/
def mk_of_compact [CompactSpace α] (f : C(α, β)) : α →ᵇ β :=
  ⟨f, bounded_range_iff.1 (is_compact_range f.continuous).Bounded⟩

@[simp]
theorem mk_of_compact_apply [CompactSpace α] (f : C(α, β)) (a : α) : mk_of_compact f a = f a :=
  rfl

/--  If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions -/
@[simps]
def mk_of_discrete [DiscreteTopology α] (f : α → β) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
  ⟨⟨f, continuous_of_discrete_topology⟩, ⟨C, h⟩⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The uniform distance between two bounded continuous functions -/")]
  []
  []
  []
  []
  [])
 (Command.instance
  (Term.attrKind [])
  "instance"
  []
  []
  (Command.declSig
   []
   (Term.typeSpec ":" (Term.app `HasDist [(Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `α " →ᵇ " `β)])))
  (Command.declValSimple
   ":="
   (Term.anonymousCtor
    "⟨"
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`f `g] [])]
       "=>"
       (Term.app
        `Inf
        [(Set.«term{_|_}»
          "{"
          `C
          "|"
          («term_∧_»
           («term_≤_» (numLit "0") "≤" `C)
           "∧"
           (Term.forall
            "∀"
            [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
            ","
            («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
          "}")])))]
    "⟩")
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`f `g] [])]
      "=>"
      (Term.app
       `Inf
       [(Set.«term{_|_}»
         "{"
         `C
         "|"
         («term_∧_»
          («term_≤_» (numLit "0") "≤" `C)
          "∧"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
           ","
           («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
         "}")])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`f `g] [])]
    "=>"
    (Term.app
     `Inf
     [(Set.«term{_|_}»
       "{"
       `C
       "|"
       («term_∧_»
        («term_≤_» (numLit "0") "≤" `C)
        "∧"
        (Term.forall
         "∀"
         [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
         ","
         («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
       "}")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Inf
   [(Set.«term{_|_}»
     "{"
     `C
     "|"
     («term_∧_»
      («term_≤_» (numLit "0") "≤" `C)
      "∧"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
       ","
       («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
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
   `C
   "|"
   («term_∧_»
    («term_≤_» (numLit "0") "≤" `C)
    "∧"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
     ","
     («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_≤_» (numLit "0") "≤" `C)
   "∧"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
    ","
    («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
   ","
   («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`x])
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
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `g [`x]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_≤_» (numLit "0") "≤" `C)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The uniform distance between two bounded continuous functions -/
  instance : HasDist α →ᵇ β := ⟨ fun f g => Inf { C | 0 ≤ C ∧ ∀ x : α , dist f x g x ≤ C } ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `dist_eq [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `dist [`f `g])
     "="
     (Term.app
      `Inf
      [(Set.«term{_|_}»
        "{"
        `C
        "|"
        («term_∧_»
         («term_≤_» (numLit "0") "≤" `C)
         "∧"
         (Term.forall
          "∀"
          [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
          ","
          («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
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
   (Term.app `dist [`f `g])
   "="
   (Term.app
    `Inf
    [(Set.«term{_|_}»
      "{"
      `C
      "|"
      («term_∧_»
       («term_≤_» (numLit "0") "≤" `C)
       "∧"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
        ","
        («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
      "}")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Inf
   [(Set.«term{_|_}»
     "{"
     `C
     "|"
     («term_∧_»
      («term_≤_» (numLit "0") "≤" `C)
      "∧"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
       ","
       («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
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
   `C
   "|"
   («term_∧_»
    («term_≤_» (numLit "0") "≤" `C)
    "∧"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
     ","
     («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_≤_» (numLit "0") "≤" `C)
   "∧"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
    ","
    («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
   ","
   («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]) "≤" `C)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`x])
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
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `g [`x]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_≤_» (numLit "0") "≤" `C)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
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
theorem dist_eq : dist f g = Inf { C | 0 ≤ C ∧ ∀ x : α , dist f x g x ≤ C } := rfl

theorem dist_set_exists : ∃ C, 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C := by
  rcases f.bounded_range.union g.bounded_range with ⟨C, hC⟩
  refine' ⟨max 0 C, le_max_leftₓ _ _, fun x => (hC _ _ _ _).trans (le_max_rightₓ _ _)⟩ <;> [left, right] <;>
    apply mem_range_self

/--  The pointwise distance is controlled by the distance between functions, by definition. -/
theorem dist_coe_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
  le_cInf dist_set_exists $ fun b hb => hb.2 x

private theorem dist_nonneg' : 0 ≤ dist f g :=
  le_cInf dist_set_exists fun C => And.left

/--  The distance between two functions is controlled by the supremum of the pointwise distances -/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C :=
  ⟨fun h x => le_transₓ (dist_coe_le_dist x) h, fun H => cInf_le ⟨0, fun C => And.left⟩ ⟨C0, H⟩⟩

theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
  ⟨fun h x => le_transₓ (dist_coe_le_dist x) h, fun w =>
    (dist_le (le_transₓ dist_nonneg (w (Nonempty.some ‹_›)))).mpr w⟩

theorem dist_lt_of_nonempty_compact [Nonempty α] [CompactSpace α] (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
  by
  have c : Continuous fun x => dist (f x) (g x) := by
    continuity
  obtain ⟨x, -, le⟩ := IsCompact.exists_forall_ge compact_univ Set.univ_nonempty (Continuous.continuous_on c)
  exact lt_of_le_of_ltₓ (dist_le_iff_of_nonempty.mpr fun y => le y trivialₓ) (w x)

theorem dist_lt_iff_of_compact [CompactSpace α] (C0 : (0 : ℝ) < C) : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  fconstructor
  ·
    intro w x
    exact lt_of_le_of_ltₓ (dist_coe_le_dist x) w
  ·
    by_cases' h : Nonempty α
    ·
      skip
      exact dist_lt_of_nonempty_compact
    ·
      rintro -
      convert C0
      apply le_antisymmₓ _ dist_nonneg'
      rw [dist_eq]
      exact cInf_le ⟨0, fun C => And.left⟩ ⟨le_reflₓ _, fun x => False.elim (h (Nonempty.intro x))⟩

theorem dist_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C :=
  ⟨fun w x => lt_of_le_of_ltₓ (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

-- failed to format: format: uncaught backtrack exception
/-- The type of bounded continuous functions, with the uniform distance, is a metric space. -/
  instance
    : MetricSpace ( α →ᵇ β )
    where
      dist_self f := le_antisymmₓ ( ( dist_le ( le_reflₓ _ ) ) . 2 $ fun x => by simp ) dist_nonneg'
        eq_of_dist_eq_zero
          f g hfg
          :=
          by ext x <;> exact eq_of_dist_eq_zero ( le_antisymmₓ ( hfg ▸ dist_coe_le_dist _ ) dist_nonneg )
        dist_comm f g := by simp [ dist_eq , dist_comm ]
        dist_triangle
          f g h
          :=
          ( dist_le ( add_nonneg dist_nonneg' dist_nonneg' ) ) . 2
            $
            fun x => le_transₓ ( dist_triangle _ _ _ ) ( add_le_add ( dist_coe_le_dist _ ) ( dist_coe_le_dist _ ) )

/--  On an empty space, bounded continuous functions are at distance 0 -/
theorem dist_zero_of_empty [IsEmpty α] : dist f g = 0 :=
  dist_eq_zero.2 (eq_of_empty f g)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `dist_eq_supr [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `dist [`f `g])
     "="
     (Order.CompleteLattice.«term⨆_,_»
      "⨆"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
      ", "
      (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.cases' "cases'" [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [`α]))] [] []) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `supr_of_empty')
                ","
                (Tactic.rwRule [] `Real.Sup_empty)
                ","
                (Tactic.rwRule [] `dist_zero_of_empty)]
               "]")
              [])
             [])])))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj («term_$__» `dist_le_iff_of_nonempty.mpr "$" (Term.app `le_csupr [(Term.hole "_")])) "." `antisymm)
          [(Term.app `csupr_le [`dist_coe_le_dist])]))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `dist_set_exists.imp
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`C `hC] [])]
             "=>"
             (Term.app (Term.proj `forall_range_iff "." (fieldIdx "2")) [(Term.proj `hC "." (fieldIdx "2"))])))]))
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
     [(group (Tactic.cases' "cases'" [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [`α]))] [] []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `supr_of_empty')
               ","
               (Tactic.rwRule [] `Real.Sup_empty)
               ","
               (Tactic.rwRule [] `dist_zero_of_empty)]
              "]")
             [])
            [])])))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj («term_$__» `dist_le_iff_of_nonempty.mpr "$" (Term.app `le_csupr [(Term.hole "_")])) "." `antisymm)
         [(Term.app `csupr_le [`dist_coe_le_dist])]))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `dist_set_exists.imp
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`C `hC] [])]
            "=>"
            (Term.app (Term.proj `forall_range_iff "." (fieldIdx "2")) [(Term.proj `hC "." (fieldIdx "2"))])))]))
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
    `dist_set_exists.imp
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`C `hC] [])]
       "=>"
       (Term.app (Term.proj `forall_range_iff "." (fieldIdx "2")) [(Term.proj `hC "." (fieldIdx "2"))])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `dist_set_exists.imp
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`C `hC] [])]
      "=>"
      (Term.app (Term.proj `forall_range_iff "." (fieldIdx "2")) [(Term.proj `hC "." (fieldIdx "2"))])))])
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
    [(Term.simpleBinder [`C `hC] [])]
    "=>"
    (Term.app (Term.proj `forall_range_iff "." (fieldIdx "2")) [(Term.proj `hC "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `forall_range_iff "." (fieldIdx "2")) [(Term.proj `hC "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `hC "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hC
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `forall_range_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `forall_range_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist_set_exists.imp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj («term_$__» `dist_le_iff_of_nonempty.mpr "$" (Term.app `le_csupr [(Term.hole "_")])) "." `antisymm)
    [(Term.app `csupr_le [`dist_coe_le_dist])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj («term_$__» `dist_le_iff_of_nonempty.mpr "$" (Term.app `le_csupr [(Term.hole "_")])) "." `antisymm)
   [(Term.app `csupr_le [`dist_coe_le_dist])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `csupr_le [`dist_coe_le_dist])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dist_coe_le_dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `csupr_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `csupr_le [`dist_coe_le_dist]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj («term_$__» `dist_le_iff_of_nonempty.mpr "$" (Term.app `le_csupr [(Term.hole "_")])) "." `antisymm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__» `dist_le_iff_of_nonempty.mpr "$" (Term.app `le_csupr [(Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_csupr [(Term.hole "_")])
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
  `le_csupr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `dist_le_iff_of_nonempty.mpr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__» `dist_le_iff_of_nonempty.mpr "$" (Term.app `le_csupr [(Term.hole "_")])) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `supr_of_empty')
          ","
          (Tactic.rwRule [] `Real.Sup_empty)
          ","
          (Tactic.rwRule [] `dist_zero_of_empty)]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
    [(Tactic.rwRule [] `supr_of_empty')
     ","
     (Tactic.rwRule [] `Real.Sup_empty)
     ","
     (Tactic.rwRule [] `dist_zero_of_empty)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dist_zero_of_empty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Real.Sup_empty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr_of_empty'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases' "cases'" [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [`α]))] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_empty_or_nonempty [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_empty_or_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `dist [`f `g])
   "="
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
    ", "
    (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
   ", "
   (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dist [(Term.app `f [`x]) (Term.app `g [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`x])
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
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `g [`x]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
  dist_eq_supr
  : dist f g = ⨆ x : α , dist f x g x
  :=
    by
      cases' is_empty_or_nonempty α
        · rw [ supr_of_empty' , Real.Sup_empty , dist_zero_of_empty ]
        refine' dist_le_iff_of_nonempty.mpr $ le_csupr _ . antisymm csupr_le dist_coe_le_dist
        exact dist_set_exists.imp fun C hC => forall_range_iff . 2 hC . 2

variable (α) {β}

/--  Constant as a continuous bounded function. -/
@[simps (config := { fullyApplied := ff })]
def const (b : β) : α →ᵇ β :=
  ⟨ContinuousMap.const b, 0, by
    simp [le_reflₓ]⟩

variable {α}

theorem const_apply' (a : α) (b : β) : (const α b : α → β) a = b :=
  rfl

/--  If the target space is inhabited, so is the space of bounded continuous functions -/
instance [Inhabited β] : Inhabited (α →ᵇ β) :=
  ⟨const α (default β)⟩

theorem lipschitz_evalx (x : α) : LipschitzWith 1 fun f : α →ᵇ β => f x :=
  LipschitzWith.mk_one $ fun f g => dist_coe_le_dist x

theorem uniform_continuous_coe : @UniformContinuous (α →ᵇ β) (α → β) _ _ coeFn :=
  uniform_continuous_pi.2 $ fun x => (lipschitz_evalx x).UniformContinuous

theorem continuous_coe : Continuous fun f : α →ᵇ β x => f x :=
  UniformContinuous.continuous uniform_continuous_coe

/--  When `x` is fixed, `(f : α →ᵇ β) ↦ f x` is continuous -/
@[continuity]
theorem continuous_evalx {x : α} : Continuous fun f : α →ᵇ β => f x :=
  (continuous_apply x).comp continuous_coe

/--  The evaluation map is continuous, as a joint function of `u` and `x` -/
@[continuity]
theorem continuous_eval : Continuous fun p : (α →ᵇ β) × α => p.1 p.2 :=
  (continuous_prod_of_continuous_lipschitz _ 1 fun f => f.continuous) $ lipschitz_evalx

/--  Bounded continuous functions taking values in a complete space form a complete space. -/
instance [CompleteSpace β] : CompleteSpace (α →ᵇ β) :=
  complete_of_cauchy_seq_tendsto $ fun f : ℕ → α →ᵇ β hf : CauchySeq f => by
    rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have f_bdd := fun x n m N hn hm => le_transₓ (dist_coe_le_dist x) (b_bound n m N hn hm)
    have fx_cau : ∀ x, CauchySeq fun n => f n x := fun x => cauchy_seq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩
    choose F hF using fun x => cauchy_seq_tendsto_of_complete (fx_cau x)
    have fF_bdd : ∀ x N, dist (f N x) (F x) ≤ b N := fun x N =>
      le_of_tendsto (tendsto_const_nhds.dist (hF x))
        (Filter.eventually_at_top.2 ⟨N, fun n hn => f_bdd x N n N (le_reflₓ N) hn⟩)
    refine' ⟨⟨⟨F, _⟩, _⟩, _⟩
    ·
      have : TendstoUniformly (fun n x => f n x) F at_top := by
        refine' Metric.tendsto_uniformly_iff.2 fun ε ε0 => _
        refine' ((tendsto_order.1 b_lim).2 ε ε0).mono fun n hn x => _
        rw [dist_comm]
        exact lt_of_le_of_ltₓ (fF_bdd x n) hn
      exact this.continuous (eventually_of_forall $ fun N => (f N).Continuous)
    ·
      rcases(f 0).Bounded with ⟨C, hC⟩
      refine' ⟨C+b 0+b 0, fun x y => _⟩
      calc dist (F x) (F y) ≤ dist (f 0 x) (f 0 y)+dist (f 0 x) (F x)+dist (f 0 y) (F y) :=
        dist_triangle4_left _ _ _ _ _ ≤ C+b 0+b 0 := by
        mono*
    ·
      refine' tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) _ b_lim)
      exact fun N => (dist_le (b0 _)).2 fun x => fF_bdd x N

/--  Composition of a bounded continuous function and a continuous function. -/
@[simps (config := { fullyApplied := ff })]
def comp_continuous {δ : Type _} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) : δ →ᵇ β :=
  { toContinuousMap := f.1.comp g, bounded' := f.bounded'.imp fun C hC x y => hC _ _ }

theorem lipschitz_comp_continuous {δ : Type _} [TopologicalSpace δ] (g : C(δ, α)) :
    LipschitzWith 1 fun f : α →ᵇ β => f.comp_continuous g :=
  LipschitzWith.mk_one $ fun f₁ f₂ => (dist_le dist_nonneg).2 $ fun x => dist_coe_le_dist (g x)

theorem continuous_comp_continuous {δ : Type _} [TopologicalSpace δ] (g : C(δ, α)) :
    Continuous fun f : α →ᵇ β => f.comp_continuous g :=
  (lipschitz_comp_continuous g).Continuous

/--  Restrict a bounded continuous function to a set. -/
@[simps (config := { fullyApplied := ff }) apply]
def restrict (f : α →ᵇ β) (s : Set α) : s →ᵇ β :=
  f.comp_continuous (ContinuousMap.id.restrict s)

/--  Composition (in the target) of a bounded continuous function with a Lipschitz map again
gives a bounded continuous function -/
def comp (G : β → γ) {C : ℝ≥0 } (H : LipschitzWith C G) (f : α →ᵇ β) : α →ᵇ γ :=
  ⟨⟨fun x => G (f x), H.continuous.comp f.continuous⟩,
    let ⟨D, hD⟩ := f.bounded
    ⟨max C 0*D, fun x y =>
      calc dist (G (f x)) (G (f y)) ≤ C*dist (f x) (f y) := H.dist_le_mul _ _
        _ ≤ max C 0*dist (f x) (f y) := mul_le_mul_of_nonneg_right (le_max_leftₓ C 0) dist_nonneg
        _ ≤ max C 0*D := mul_le_mul_of_nonneg_left (hD _ _) (le_max_rightₓ C 0)
        ⟩⟩

/--  The composition operator (in the target) with a Lipschitz map is Lipschitz -/
theorem lipschitz_comp {G : β → γ} {C : ℝ≥0 } (H : LipschitzWith C G) :
    LipschitzWith C (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  LipschitzWith.of_dist_le_mul $ fun f g =>
    (dist_le (mul_nonneg C.2 dist_nonneg)).2 $ fun x =>
      calc dist (G (f x)) (G (g x)) ≤ C*dist (f x) (g x) := H.dist_le_mul _ _
        _ ≤ C*dist f g := mul_le_mul_of_nonneg_left (dist_coe_le_dist _) C.2
        

/--  The composition operator (in the target) with a Lipschitz map is uniformly continuous -/
theorem uniform_continuous_comp {G : β → γ} {C : ℝ≥0 } (H : LipschitzWith C G) :
    UniformContinuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  (lipschitz_comp H).UniformContinuous

/--  The composition operator (in the target) with a Lipschitz map is continuous -/
theorem continuous_comp {G : β → γ} {C : ℝ≥0 } (H : LipschitzWith C G) : Continuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  (lipschitz_comp H).Continuous

/--  Restriction (in the target) of a bounded continuous function taking values in a subset -/
def cod_restrict (s : Set β) (f : α →ᵇ β) (H : ∀ x, f x ∈ s) : α →ᵇ s :=
  ⟨⟨s.cod_restrict f H, continuous_subtype_mk _ f.continuous⟩, f.bounded⟩

section Extend

variable {δ : Type _} [TopologicalSpace δ] [DiscreteTopology δ]

/--  A version of `function.extend` for bounded continuous maps. We assume that the domain has
discrete topology, so we only need to verify boundedness. -/
def extend (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : δ →ᵇ β :=
  { toFun := extend f g h, continuous_to_fun := continuous_of_discrete_topology,
    bounded' := by
      rw [← bounded_range_iff, range_extend f.injective, Metric.bounded_union]
      exact ⟨g.bounded_range, h.bounded_image _⟩ }

@[simp]
theorem extend_apply (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) (x : α) : extend f g h (f x) = g x :=
  extend_apply f.injective _ _ _

@[simp]
theorem extend_comp (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : (extend f g h ∘ f) = g :=
  extend_comp f.injective _ _

theorem extend_apply' {f : α ↪ δ} {x : δ} (hx : x ∉ range f) (g : α →ᵇ β) (h : δ →ᵇ β) : extend f g h x = h x :=
  extend_apply' _ _ _ hx

theorem extend_of_empty [IsEmpty α] (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : extend f g h = h :=
  coe_injective $ Function.extend_of_empty f g h

@[simp]
theorem dist_extend_extend (f : α ↪ δ) (g₁ g₂ : α →ᵇ β) (h₁ h₂ : δ →ᵇ β) :
    dist (g₁.extend f h₁) (g₂.extend f h₂) =
      max (dist g₁ g₂) (dist (h₁.restrict (range fᶜ)) (h₂.restrict (range fᶜ))) :=
  by
  refine' le_antisymmₓ ((dist_le $ le_max_iff.2 $ Or.inl dist_nonneg).2 $ fun x => _) (max_leₓ _ _)
  ·
    rcases em (∃ y, f y = x) with (⟨x, rfl⟩ | hx)
    ·
      simp only [extend_apply]
      exact (dist_coe_le_dist x).trans (le_max_leftₓ _ _)
    ·
      simp only [extend_apply' hx]
      lift x to (range fᶜ : Set δ) using hx
      calc dist (h₁ x) (h₂ x) = dist (h₁.restrict (range fᶜ) x) (h₂.restrict (range fᶜ) x) :=
        rfl _ ≤ dist (h₁.restrict (range fᶜ)) (h₂.restrict (range fᶜ)) := dist_coe_le_dist x _ ≤ _ := le_max_rightₓ _ _
  ·
    refine' (dist_le dist_nonneg).2 fun x => _
    rw [← extend_apply f g₁ h₁, ← extend_apply f g₂ h₂]
    exact dist_coe_le_dist _
  ·
    refine' (dist_le dist_nonneg).2 fun x => _
    calc dist (h₁ x) (h₂ x) = dist (extend f g₁ h₁ x) (extend f g₂ h₂ x) := by
      rw [extend_apply' x.coe_prop, extend_apply' x.coe_prop]_ ≤ _ := dist_coe_le_dist _

theorem isometry_extend (f : α ↪ δ) (h : δ →ᵇ β) : Isometry fun g : α →ᵇ β => extend f g h :=
  isometry_emetric_iff_metric.2 $ fun g₁ g₂ => by
    simp [dist_nonneg]

end Extend

end Basics

section ArzelaAscoli

variable [TopologicalSpace α] [CompactSpace α] [MetricSpace β]

variable {f g : α →ᵇ β} {x : α} {C : ℝ}

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y z «expr ∈ » U)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y z «expr ∈ » U)
/--  First version, with pointwise equicontinuity and range in a compact space -/
theorem arzela_ascoli₁ [CompactSpace β] (A : Set (α →ᵇ β)) (closed : IsClosed A)
    (H : ∀ x : α, ∀ ε > 0, ∀, ∃ U ∈ 𝓝 x, ∀ y z _ : y ∈ U _ : z ∈ U f : α →ᵇ β, f ∈ A → dist (f y) (f z) < ε) :
    IsCompact A := by
  refine' compact_of_totally_bounded_is_closed _ closed
  refine' totally_bounded_of_finite_discretization fun ε ε0 => _
  rcases exists_between ε0 with ⟨ε₁, ε₁0, εε₁⟩
  let ε₂ := ε₁ / 2 / 2
  have ε₂0 : ε₂ > 0 := half_pos (half_pos ε₁0)
  have : ∀ x : α, ∃ U, x ∈ U ∧ IsOpen U ∧ ∀ y z _ : y ∈ U _ : z ∈ U {f : α →ᵇ β}, f ∈ A → dist (f y) (f z) < ε₂ :=
    fun x =>
    let ⟨U, nhdsU, hU⟩ := H x _ ε₂0
    let ⟨V, VU, openV, xV⟩ := _root_.mem_nhds_iff.1 nhdsU
    ⟨V, xV, openV, fun y z hy hz f hf => hU y z (VU hy) (VU hz) f hf⟩
  choose U hU using this
  rcases compact_univ.elim_finite_subcover_image (fun x _ => (hU x).2.1) fun x hx =>
      mem_bUnion (mem_univ _) (hU x).1 with
    ⟨tα, _, ⟨_⟩, htα⟩
  rcases@finite_cover_balls_of_compact β _ _ compact_univ _ ε₂0 with ⟨tβ, _, ⟨_⟩, htβ⟩
  skip
  choose F hF using fun y =>
    show ∃ z ∈ tβ, dist y z < ε₂ by
      simpa using htβ (mem_univ y)
  refine'
    ⟨tα → tβ, by
      infer_instance, fun f a => ⟨F (f a), (hF (f a)).1⟩, _⟩
  rintro ⟨f, hf⟩ ⟨g, hg⟩ f_eq_g
  refine' lt_of_le_of_ltₓ ((dist_le $ le_of_ltₓ ε₁0).2 fun x => _) εε₁
  obtain ⟨x', x'tα, hx'⟩ : ∃ x' ∈ tα, x ∈ U x' := mem_bUnion_iff.1 (htα (mem_univ x))
  calc dist (f x) (g x) ≤ (dist (f x) (f x')+dist (g x) (g x'))+dist (f x') (g x') :=
    dist_triangle4_right _ _ _ _ _ ≤ (ε₂+ε₂)+ε₁ / 2 := le_of_ltₓ (add_lt_add (add_lt_add _ _) _)_ = ε₁ := by
    rw [add_halves, add_halves]
  ·
    exact (hU x').2.2 _ _ hx' (hU x').1 hf
  ·
    exact (hU x').2.2 _ _ hx' (hU x').1 hg
  ·
    have F_f_g : F (f x') = F (g x') := (congr_argₓ (fun f : tα → tβ => (f ⟨x', x'tα⟩ : β)) f_eq_g : _)
    calc dist (f x') (g x') ≤ dist (f x') (F (f x'))+dist (g x') (F (f x')) :=
      dist_triangle_right _ _ _ _ = dist (f x') (F (f x'))+dist (g x') (F (g x')) := by
      rw [F_f_g]_ < ε₂+ε₂ := add_lt_add (hF (f x')).2 (hF (g x')).2_ = ε₁ / 2 := add_halves _

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y z «expr ∈ » U)
/--  Second version, with pointwise equicontinuity and range in a compact subset -/
theorem arzela_ascoli₂ (s : Set β) (hs : IsCompact s) (A : Set (α →ᵇ β)) (closed : IsClosed A)
    (in_s : ∀ f : α →ᵇ β x : α, f ∈ A → f x ∈ s)
    (H : ∀ x : α, ∀ ε > 0, ∀, ∃ U ∈ 𝓝 x, ∀ y z _ : y ∈ U _ : z ∈ U f : α →ᵇ β, f ∈ A → dist (f y) (f z) < ε) :
    IsCompact A := by
  have M : LipschitzWith 1 coeₓ := LipschitzWith.subtype_coe s
  let F : (α →ᵇ s) → α →ᵇ β := comp coeₓ M
  refine' compact_of_is_closed_subset ((_ : IsCompact (F ⁻¹' A)).Image (continuous_comp M)) closed fun f hf => _
  ·
    have : CompactSpace s := is_compact_iff_compact_space.1 hs
    refine'
      arzela_ascoli₁ _ (continuous_iff_is_closed.1 (continuous_comp M) _ closed) fun x ε ε0 =>
        Bex.imp_right (fun U U_nhds hU y z hy hz f hf => _) (H x ε ε0)
    calc dist (f y) (f z) = dist (F f y) (F f z) := rfl _ < ε := hU y z hy hz (F f) hf
  ·
    let g := cod_restrict s f fun x => in_s f x hf
    rw
      [show f = F g by
        ext <;> rfl] at
      hf⊢
    exact ⟨g, hf, rfl⟩

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y z «expr ∈ » U)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y z «expr ∈ » U)
/--  Third (main) version, with pointwise equicontinuity and range in a compact subset, but
without closedness. The closure is then compact -/
theorem arzela_ascoli (s : Set β) (hs : IsCompact s) (A : Set (α →ᵇ β)) (in_s : ∀ f : α →ᵇ β x : α, f ∈ A → f x ∈ s)
    (H : ∀ x : α, ∀ ε > 0, ∀, ∃ U ∈ 𝓝 x, ∀ y z _ : y ∈ U _ : z ∈ U f : α →ᵇ β, f ∈ A → dist (f y) (f z) < ε) :
    IsCompact (Closure A) :=
  arzela_ascoli₂ s hs (Closure A) is_closed_closure
    (fun f x hf =>
      (mem_of_closed' hs.is_closed).2 $ fun ε ε0 =>
        let ⟨g, gA, dist_fg⟩ := Metric.mem_closure_iff.1 hf ε ε0
        ⟨g x, in_s g x gA, lt_of_le_of_ltₓ (dist_coe_le_dist _) dist_fg⟩)
    fun x ε ε0 =>
    show ∃ U ∈ 𝓝 x, ∀ y z _ : y ∈ U _ : z ∈ U, ∀ f : α →ᵇ β, f ∈ Closure A → dist (f y) (f z) < ε by
      refine' Bex.imp_right (fun U U_set hU y z hy hz f hf => _) (H x (ε / 2) (half_pos ε0))
      rcases Metric.mem_closure_iff.1 hf (ε / 2 / 2) (half_pos (half_pos ε0)) with ⟨g, gA, dist_fg⟩
      replace dist_fg := fun x => lt_of_le_of_ltₓ (dist_coe_le_dist x) dist_fg
      calc dist (f y) (f z) ≤ (dist (f y) (g y)+dist (f z) (g z))+dist (g y) (g z) :=
        dist_triangle4_right _ _ _ _ _ < ((ε / 2 / 2)+ε / 2 / 2)+ε / 2 :=
        add_lt_add (add_lt_add (dist_fg y) (dist_fg z)) (hU y z hy hz g gA)_ = ε := by
        rw [add_halves, add_halves]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y z «expr ∈ » U)
theorem equicontinuous_of_continuity_modulus {α : Type u} [MetricSpace α] (b : ℝ → ℝ) (b_lim : tendsto b (𝓝 0) (𝓝 0))
    (A : Set (α →ᵇ β)) (H : ∀ x y : α f : α →ᵇ β, f ∈ A → dist (f x) (f y) ≤ b (dist x y)) (x : α) (ε : ℝ)
    (ε0 : 0 < ε) : ∃ U ∈ 𝓝 x, ∀ y z _ : y ∈ U _ : z ∈ U f : α →ᵇ β, f ∈ A → dist (f y) (f z) < ε := by
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  refine' ⟨ball x (δ / 2), ball_mem_nhds x (half_pos δ0), fun y z hy hz f hf => _⟩
  have : dist y z < δ :=
    calc dist y z ≤ dist y x+dist z x := dist_triangle_right _ _ _
      _ < (δ / 2)+δ / 2 := add_lt_add hy hz
      _ = δ := add_halves _
      
  calc dist (f y) (f z) ≤ b (dist y z) := H y z f hf _ ≤ |b (dist y z)| := le_abs_self _ _ = dist (b (dist y z)) 0 := by
    simp [Real.dist_eq]_ < ε :=
    hδ
      (by
        simpa [Real.dist_eq] using this)

end ArzelaAscoli

section HasLipschitzAdd

variable [TopologicalSpace α] [MetricSpace β] [AddMonoidₓ β]

instance : HasZero (α →ᵇ β) :=
  ⟨const α 0⟩

@[simp]
theorem coe_zero : ((0 : α →ᵇ β) : α → β) = 0 :=
  rfl

theorem forall_coe_zero_iff_zero (f : α →ᵇ β) : (∀ x, f x = 0) ↔ f = 0 :=
  (@ext_iff _ _ _ _ f 0).symm

@[simp]
theorem zero_comp_continuous [TopologicalSpace γ] (f : C(γ, α)) : (0 : α →ᵇ β).comp_continuous f = 0 :=
  rfl

variable [HasLipschitzAdd β]

variable (f g : α →ᵇ β) {x : α} {C : ℝ}

-- failed to format: format: uncaught backtrack exception
/-- The pointwise sum of two bounded continuous functions is again bounded continuous. -/
  instance
    : Add ( α →ᵇ β )
    where
      add
        f g
        :=
        BoundedContinuousFunction.mkOfBound
          ( f.to_continuous_map + g.to_continuous_map )
            ( ( ↑ HasLipschitzAdd.c β ) * max ( Classical.some f.bounded ) ( Classical.some g.bounded ) )
            (
              by
                intro x y
                  refine' le_transₓ ( lipschitz_with_lipschitz_const_add ⟨ f x , g x ⟩ ⟨ f y , g y ⟩ ) _
                  rw [ Prod.dist_eq ]
                  refine' mul_le_mul_of_nonneg_left _ ( HasLipschitzAdd.c β ) . coe_nonneg
                  apply max_le_max
                  exact Classical.some_spec f.bounded x y
                  exact Classical.some_spec g.bounded x y
              )

@[simp]
theorem coe_add : (⇑f+g) = f+g :=
  rfl

theorem add_apply : (f+g) x = f x+g x :=
  rfl

theorem add_comp_continuous [TopologicalSpace γ] (h : C(γ, α)) :
    (g+f).comp_continuous h = g.comp_continuous h+f.comp_continuous h :=
  rfl

instance : AddMonoidₓ (α →ᵇ β) :=
  { BoundedContinuousFunction.hasAdd, BoundedContinuousFunction.hasZero with
    add_assoc := fun f g h => by
      ext <;> simp [add_assocₓ],
    zero_add := fun f => by
      ext <;> simp ,
    add_zero := fun f => by
      ext <;> simp }

instance : HasLipschitzAdd (α →ᵇ β) where
  lipschitz_add :=
    ⟨HasLipschitzAdd.c β, by
      have C_nonneg := (HasLipschitzAdd.c β).coe_nonneg
      rw [lipschitz_with_iff_dist_le_mul]
      rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
      rw [dist_le (mul_nonneg C_nonneg dist_nonneg)]
      intro x
      refine' le_transₓ (lipschitz_with_lipschitz_const_add ⟨f₁ x, g₁ x⟩ ⟨f₂ x, g₂ x⟩) _
      refine' mul_le_mul_of_nonneg_left _ C_nonneg
      apply max_le_max <;> exact dist_coe_le_dist x⟩

/--  Coercion of a `normed_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn` -/
@[simps]
def coe_fn_add_hom : (α →ᵇ β) →+ α → β :=
  { toFun := coeFn, map_zero' := coe_zero, map_add' := coe_add }

variable (α β)

/--  The additive map forgetting that a bounded continuous function is bounded.
-/
@[simps]
def to_continuous_map_add_hom : (α →ᵇ β) →+ C(α, β) :=
  { toFun := to_continuous_map,
    map_zero' := by
      ext
      simp ,
    map_add' := by
      intros
      ext
      simp }

end HasLipschitzAdd

section CommHasLipschitzAdd

variable [TopologicalSpace α] [MetricSpace β] [AddCommMonoidₓ β] [HasLipschitzAdd β]

@[to_additive]
instance : AddCommMonoidₓ (α →ᵇ β) :=
  { BoundedContinuousFunction.addMonoid with
    add_comm := fun f g => by
      ext <;> simp [add_commₓ] }

open_locale BigOperators

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
    (Term.explicitBinder
     "("
     [`f]
     [":" (Term.arrow `ι "→" (Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `α " →ᵇ " `β))]
     []
     ")")]
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
      (Term.paren "(" [(Term.app `f [`i]) [(Term.typeAscription ":" (Term.arrow `α "→" `β))]] ")")))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj
     (Term.app
      (Term.explicit "@" `coe_fn_add_hom)
      [`α `β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
    (Term.app
     (Term.explicit "@" `coe_fn_add_hom)
     [`α `β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
   (Term.app
    (Term.explicit "@" `coe_fn_add_hom)
    [`α `β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
   "."
   `map_sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.explicit "@" `coe_fn_add_hom) [`α `β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `coe_fn_add_hom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coe_fn_add_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.explicit "@" `coe_fn_add_hom) [`α `β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
  []]
 ")")
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
    (Term.paren "(" [(Term.app `f [`i]) [(Term.typeAscription ":" (Term.arrow `α "→" `β))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.paren "(" [(Term.app `f [`i]) [(Term.typeAscription ":" (Term.arrow `α "→" `β))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(Term.app `f [`i]) [(Term.typeAscription ":" (Term.arrow `α "→" `β))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow `α "→" `β)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
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
@[ simp ]
  theorem
    coe_sum
    { ι : Type _ } ( s : Finset ι ) ( f : ι → α →ᵇ β ) : ⇑ ∑ i in s , f i = ∑ i in s , ( f i : α → β )
    := @ coe_fn_add_hom α β _ _ _ _ . map_sum f s

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_apply [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`f]
     [":" (Term.arrow `ι "→" (Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `α " →ᵇ " `β))]
     []
     ")")
    (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
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
      [`a])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `f [`i `a])))))
  (Command.declValSimple
   ":="
   (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
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
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
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
    [`a])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Term.app `f [`i `a])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i `a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
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
  { ι : Type _ } ( s : Finset ι ) ( f : ι → α →ᵇ β ) ( a : α ) : ∑ i in s , f i a = ∑ i in s , f i a
  := by simp

end CommHasLipschitzAdd

section NormedGroup

variable [TopologicalSpace α] [NormedGroup β]

variable (f g : α →ᵇ β) {x : α} {C : ℝ}

instance : HasNorm (α →ᵇ β) :=
  ⟨fun u => dist u 0⟩

theorem norm_def : ∥f∥ = dist f 0 :=
  rfl

/--  The norm of a bounded continuous function is the supremum of `∥f x∥`.
We use `Inf` to ensure that the definition works if `α` has no elements. -/
theorem norm_eq (f : α →ᵇ β) : ∥f∥ = Inf { C : ℝ | 0 ≤ C ∧ ∀ x : α, ∥f x∥ ≤ C } := by
  simp [norm_def, BoundedContinuousFunction.dist_eq]

/--  When the domain is non-empty, we do not need the `0 ≤ C` condition in the formula for ∥f∥ as an
`Inf`. -/
theorem norm_eq_of_nonempty [h : Nonempty α] : ∥f∥ = Inf { C : ℝ | ∀ x : α, ∥f x∥ ≤ C } := by
  (
    obtain ⟨a⟩ := h)
  rw [norm_eq]
  congr
  ext
  simp only [and_iff_right_iff_imp]
  exact fun h' => le_transₓ (norm_nonneg (f a)) (h' a)

@[simp]
theorem norm_eq_zero_of_empty [h : IsEmpty α] : ∥f∥ = 0 :=
  dist_zero_of_empty

theorem norm_coe_le_norm (x : α) : ∥f x∥ ≤ ∥f∥ :=
  calc ∥f x∥ = dist (f x) ((0 : α →ᵇ β) x) := by
    simp [dist_zero_right]
    _ ≤ ∥f∥ := dist_coe_le_dist _
    

theorem dist_le_two_norm' {f : γ → β} {C : ℝ} (hC : ∀ x, ∥f x∥ ≤ C) (x y : γ) : dist (f x) (f y) ≤ 2*C :=
  calc dist (f x) (f y) ≤ ∥f x∥+∥f y∥ := dist_le_norm_add_norm _ _
    _ ≤ C+C := add_le_add (hC x) (hC y)
    _ = 2*C := (two_mul _).symm
    

/--  Distance between the images of any two points is at most twice the norm of the function. -/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2*∥f∥ :=
  dist_le_two_norm' f.norm_coe_le_norm x y

variable {f}

/--  The norm of a function is controlled by the supremum of the pointwise norms -/
theorem norm_le (C0 : (0 : ℝ) ≤ C) : ∥f∥ ≤ C ↔ ∀ x : α, ∥f x∥ ≤ C := by
  simpa using @dist_le _ _ _ _ f 0 _ C0

theorem norm_le_of_nonempty [Nonempty α] {f : α →ᵇ β} {M : ℝ} : ∥f∥ ≤ M ↔ ∀ x, ∥f x∥ ≤ M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_le_iff_of_nonempty

theorem norm_lt_iff_of_compact [CompactSpace α] {f : α →ᵇ β} {M : ℝ} (M0 : 0 < M) : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M := by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_compact M0

theorem norm_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] {f : α →ᵇ β} {M : ℝ} : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
  by
  simp_rw [norm_def, ← dist_zero_right]
  exact dist_lt_iff_of_nonempty_compact

variable (f)

/--  Norm of `const α b` is less than or equal to `∥b∥`. If `α` is nonempty,
then it is equal to `∥b∥`. -/
theorem norm_const_le (b : β) : ∥const α b∥ ≤ ∥b∥ :=
  (norm_le (norm_nonneg b)).2 $ fun x => le_reflₓ _

@[simp]
theorem norm_const_eq [h : Nonempty α] (b : β) : ∥const α b∥ = ∥b∥ :=
  le_antisymmₓ (norm_const_le b) $ h.elim $ fun x => (const α b).norm_coe_le_norm x

/--  Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
def of_normed_group {α : Type u} {β : Type v} [TopologicalSpace α] [NormedGroup β] (f : α → β) (Hf : Continuous f)
    (C : ℝ) (H : ∀ x, ∥f x∥ ≤ C) : α →ᵇ β :=
  ⟨⟨fun n => f n, Hf⟩, ⟨_, dist_le_two_norm' H⟩⟩

@[simp]
theorem coe_of_normed_group {α : Type u} {β : Type v} [TopologicalSpace α] [NormedGroup β] (f : α → β)
    (Hf : Continuous f) (C : ℝ) (H : ∀ x, ∥f x∥ ≤ C) : (of_normed_group f Hf C H : α → β) = f :=
  rfl

theorem norm_of_normed_group_le {f : α → β} (hfc : Continuous f) {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ x, ∥f x∥ ≤ C) :
    ∥of_normed_group f hfc C hfC∥ ≤ C :=
  (norm_le hC).2 hfC

/--  Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group -/
def of_normed_group_discrete {α : Type u} {β : Type v} [TopologicalSpace α] [DiscreteTopology α] [NormedGroup β]
    (f : α → β) (C : ℝ) (H : ∀ x, norm (f x) ≤ C) : α →ᵇ β :=
  of_normed_group f continuous_of_discrete_topology C H

@[simp]
theorem coe_of_normed_group_discrete {α : Type u} {β : Type v} [TopologicalSpace α] [DiscreteTopology α] [NormedGroup β]
    (f : α → β) (C : ℝ) (H : ∀ x, ∥f x∥ ≤ C) : (of_normed_group_discrete f C H : α → β) = f :=
  rfl

/--  Taking the pointwise norm of a bounded continuous function with values in a `normed_group`,
yields a bounded continuous function with values in ℝ. -/
def norm_comp : α →ᵇ ℝ :=
  of_normed_group (norm ∘ f)
    (by
      continuity)
    ∥f∥ fun x => by
    simp only [f.norm_coe_le_norm, norm_norm]

@[simp]
theorem coe_norm_comp : (f.norm_comp : α → ℝ) = (norm ∘ f) :=
  rfl

@[simp]
theorem norm_norm_comp : ∥f.norm_comp∥ = ∥f∥ := by
  simp only [norm_eq, coe_norm_comp, norm_norm]

theorem bdd_above_range_norm_comp : BddAbove $ Set.Range $ (norm ∘ f) :=
  (Real.bounded_iff_bdd_below_bdd_above.mp $ @bounded_range _ _ _ _ f.norm_comp).2

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `norm_eq_supr_norm [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")
     "="
     (Order.CompleteLattice.«term⨆_,_»
      "⨆"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
      ", "
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [`α]))]
         []
         ["with" [(Lean.binderIdent `hα) (Lean.binderIdent "_")]])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_=_» (Term.app `range [(Rel.Data.Rel.«term_∘_» `norm " ∘ " `f)]) "=" («term∅» "∅"))
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
                      [(Tactic.rwRule [] `f.norm_eq_zero_of_empty)
                       ","
                       (Tactic.rwRule [] `supr)
                       ","
                       (Tactic.rwRule [] `this)
                       ","
                       (Tactic.rwRule [] `Real.Sup_empty)]
                      "]")
                     [])
                    [])])))))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `hα)
                ","
                (Tactic.simpLemma [] [] `range_eq_empty)
                ","
                (Tactic.simpLemma [] [] `not_nonempty_iff)]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `norm_eq_of_nonempty)
                ","
                (Tactic.rwRule [] `supr)
                ","
                (Tactic.rwRule
                 ["←"]
                 (Term.app
                  `cInf_upper_bounds_eq_cSup
                  [`f.bdd_above_range_norm_comp (Term.app `range_nonempty [(Term.hole "_")])]))]
               "]")
              [])
             [])
            (group (Tactic.congr "congr" [] []) [])
            (group (Tactic.ext "ext" [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `forall_apply_eq_imp_iff')
                ","
                (Tactic.simpLemma [] [] `mem_range)
                ","
                (Tactic.simpLemma [] [] `exists_imp_distrib)]
               "]"]
              [])
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
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [`α]))]
        []
        ["with" [(Lean.binderIdent `hα) (Lean.binderIdent "_")]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_=_» (Term.app `range [(Rel.Data.Rel.«term_∘_» `norm " ∘ " `f)]) "=" («term∅» "∅"))
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
                     [(Tactic.rwRule [] `f.norm_eq_zero_of_empty)
                      ","
                      (Tactic.rwRule [] `supr)
                      ","
                      (Tactic.rwRule [] `this)
                      ","
                      (Tactic.rwRule [] `Real.Sup_empty)]
                     "]")
                    [])
                   [])])))))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `hα)
               ","
               (Tactic.simpLemma [] [] `range_eq_empty)
               ","
               (Tactic.simpLemma [] [] `not_nonempty_iff)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `norm_eq_of_nonempty)
               ","
               (Tactic.rwRule [] `supr)
               ","
               (Tactic.rwRule
                ["←"]
                (Term.app
                 `cInf_upper_bounds_eq_cSup
                 [`f.bdd_above_range_norm_comp (Term.app `range_nonempty [(Term.hole "_")])]))]
              "]")
             [])
            [])
           (group (Tactic.congr "congr" [] []) [])
           (group (Tactic.ext "ext" [] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `forall_apply_eq_imp_iff')
               ","
               (Tactic.simpLemma [] [] `mem_range)
               ","
               (Tactic.simpLemma [] [] `exists_imp_distrib)]
              "]"]
             [])
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
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `norm_eq_of_nonempty)
          ","
          (Tactic.rwRule [] `supr)
          ","
          (Tactic.rwRule
           ["←"]
           (Term.app
            `cInf_upper_bounds_eq_cSup
            [`f.bdd_above_range_norm_comp (Term.app `range_nonempty [(Term.hole "_")])]))]
         "]")
        [])
       [])
      (group (Tactic.congr "congr" [] []) [])
      (group (Tactic.ext "ext" [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `forall_apply_eq_imp_iff')
          ","
          (Tactic.simpLemma [] [] `mem_range)
          ","
          (Tactic.simpLemma [] [] `exists_imp_distrib)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
   ["["
    [(Tactic.simpLemma [] [] `forall_apply_eq_imp_iff')
     ","
     (Tactic.simpLemma [] [] `mem_range)
     ","
     (Tactic.simpLemma [] [] `exists_imp_distrib)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exists_imp_distrib
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `forall_apply_eq_imp_iff'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `norm_eq_of_nonempty)
     ","
     (Tactic.rwRule [] `supr)
     ","
     (Tactic.rwRule
      ["←"]
      (Term.app
       `cInf_upper_bounds_eq_cSup
       [`f.bdd_above_range_norm_comp (Term.app `range_nonempty [(Term.hole "_")])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `cInf_upper_bounds_eq_cSup [`f.bdd_above_range_norm_comp (Term.app `range_nonempty [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range_nonempty [(Term.hole "_")])
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
  `range_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range_nonempty [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f.bdd_above_range_norm_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `cInf_upper_bounds_eq_cSup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `norm_eq_of_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_=_» (Term.app `range [(Rel.Data.Rel.«term_∘_» `norm " ∘ " `f)]) "=" («term∅» "∅"))
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
                [(Tactic.rwRule [] `f.norm_eq_zero_of_empty)
                 ","
                 (Tactic.rwRule [] `supr)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [] `Real.Sup_empty)]
                "]")
               [])
              [])])))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `hα)
          ","
          (Tactic.simpLemma [] [] `range_eq_empty)
          ","
          (Tactic.simpLemma [] [] `not_nonempty_iff)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
   ["["
    [(Tactic.simpLemma [] [] `hα)
     ","
     (Tactic.simpLemma [] [] `range_eq_empty)
     ","
     (Tactic.simpLemma [] [] `not_nonempty_iff)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `not_nonempty_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `range_eq_empty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hα
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_=_» (Term.app `range [(Rel.Data.Rel.«term_∘_» `norm " ∘ " `f)]) "=" («term∅» "∅"))
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
           [(Tactic.rwRule [] `f.norm_eq_zero_of_empty)
            ","
            (Tactic.rwRule [] `supr)
            ","
            (Tactic.rwRule [] `this)
            ","
            (Tactic.rwRule [] `Real.Sup_empty)]
           "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSuffices_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.sufficesDecl', expected 'Lean.Parser.Term.sufficesDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
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
    [(Tactic.rwRule [] `f.norm_eq_zero_of_empty)
     ","
     (Tactic.rwRule [] `supr)
     ","
     (Tactic.rwRule [] `this)
     ","
     (Tactic.rwRule [] `Real.Sup_empty)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Real.Sup_empty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f.norm_eq_zero_of_empty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_=_» (Term.app `range [(Rel.Data.Rel.«term_∘_» `norm " ∘ " `f)]) "=" («term∅» "∅"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∅» "∅")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∅»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `range [(Rel.Data.Rel.«term_∘_» `norm " ∘ " `f)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Rel.Data.Rel.«term_∘_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Rel.Data.Rel.«term_∘_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Rel.Data.Rel.«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Rel.Data.Rel.«term_∘_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Rel.Data.Rel.«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Rel.Data.Rel.«term_∘_» `norm " ∘ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Rel.Data.Rel.«term_∘_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Rel.Data.Rel.«term_∘_» `norm " ∘ " `f) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1022, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases'
   "cases'"
   [(Tactic.casesTarget [] (Term.app `is_empty_or_nonempty [`α]))]
   []
   ["with" [(Lean.binderIdent `hα) (Lean.binderIdent "_")]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '_', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_empty_or_nonempty [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_empty_or_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")
   "="
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `α]))
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
  norm_eq_supr_norm
  : ∥ f ∥ = ⨆ x : α , ∥ f x ∥
  :=
    by
      cases' is_empty_or_nonempty α with hα _
        ·
          suffices range norm ∘ f = ∅ by rw [ f.norm_eq_zero_of_empty , supr , this , Real.Sup_empty ]
            simp only [ hα , range_eq_empty , not_nonempty_iff ]
        ·
          rw [ norm_eq_of_nonempty , supr , ← cInf_upper_bounds_eq_cSup f.bdd_above_range_norm_comp range_nonempty _ ]
            congr
            ext
            simp only [ forall_apply_eq_imp_iff' , mem_range , exists_imp_distrib ]

/--  The pointwise opposite of a bounded continuous function is again bounded continuous. -/
instance : Neg (α →ᵇ β) :=
  ⟨fun f => of_normed_group (-f) f.continuous.neg ∥f∥ $ fun x => trans_rel_right _ (norm_neg _) (f.norm_coe_le_norm x)⟩

/--  The pointwise difference of two bounded continuous functions is again bounded continuous. -/
instance : Sub (α →ᵇ β) :=
  ⟨fun f g =>
    of_normed_group (f - g) (f.continuous.sub g.continuous) (∥f∥+∥g∥) $ fun x => by
      simp only [sub_eq_add_neg]
      exact
        le_transₓ (norm_add_le _ _)
          (add_le_add (f.norm_coe_le_norm x) $ trans_rel_right _ (norm_neg _) (g.norm_coe_le_norm x))⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl

theorem neg_apply : (-f) x = -f x :=
  rfl

instance : AddCommGroupₓ (α →ᵇ β) :=
  { BoundedContinuousFunction.addMonoid, BoundedContinuousFunction.hasNeg, BoundedContinuousFunction.hasSub with
    add_left_neg := fun f => by
      ext <;> simp ,
    add_comm := fun f g => by
      ext <;> simp [add_commₓ],
    sub_eq_add_neg := fun f g => by
      ext
      apply sub_eq_add_neg }

@[simp]
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl

theorem sub_apply : (f - g) x = f x - g x :=
  rfl

-- failed to format: format: uncaught backtrack exception
instance : NormedGroup ( α →ᵇ β ) where dist_eq f g := by simp only [ norm_eq , dist_eq , dist_eq_norm , sub_apply ]

theorem abs_diff_coe_le_dist : ∥f x - g x∥ ≤ dist f g := by
  rw [dist_eq_norm]
  exact (f - g).norm_coe_le_norm x

theorem coe_le_coe_add_dist {f g : α →ᵇ ℝ} : f x ≤ g x+dist f g :=
  sub_le_iff_le_add'.1 $ (abs_le.1 $ @dist_coe_le_dist _ _ _ _ f g x).2

end NormedGroup

section HasBoundedSmul

/-!
### `has_bounded_smul` (in particular, topological module) structure

In this section, if `β` is a metric space and a `𝕜`-module whose addition and scalar multiplication
are compatible with the metric structure, then we show that the space of bounded continuous
functions from `α` to `β` inherits a so-called `has_bounded_smul` structure (in particular, a
`has_continuous_mul` structure, which is the mathlib formulation of being a topological module), by
using pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type _} [MetricSpace 𝕜] [Semiringₓ 𝕜]

variable [TopologicalSpace α] [MetricSpace β] [AddCommMonoidₓ β] [Module 𝕜 β] [HasBoundedSmul 𝕜 β]

variable {f g : α →ᵇ β} {x : α} {C : ℝ}

instance : HasScalar 𝕜 (α →ᵇ β) :=
  ⟨fun c f =>
    BoundedContinuousFunction.mkOfBound (c • f.to_continuous_map) (dist c 0*Classical.some f.bounded)
      (by
        intro x y
        refine' (dist_smul_pair c (f x) (f y)).trans _
        refine' mul_le_mul_of_nonneg_left _ dist_nonneg
        exact Classical.some_spec f.bounded x y)⟩

@[simp]
theorem coe_smul (c : 𝕜) (f : α →ᵇ β) : ⇑(c • f) = fun x => c • f x :=
  rfl

theorem smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x :=
  rfl

-- failed to format: format: uncaught backtrack exception
instance
  : HasBoundedSmul 𝕜 ( α →ᵇ β )
  where
    dist_smul_pair'
        c f₁ f₂
        :=
        by
          rw [ dist_le ( mul_nonneg dist_nonneg dist_nonneg ) ]
            intro x
            refine' ( dist_smul_pair c ( f₁ x ) ( f₂ x ) ) . trans _
            exact mul_le_mul_of_nonneg_left ( dist_coe_le_dist x ) dist_nonneg
      dist_pair_smul'
        c₁ c₂ f
        :=
        by
          rw [ dist_le ( mul_nonneg dist_nonneg dist_nonneg ) ]
            intro x
            refine' ( dist_pair_smul c₁ c₂ ( f x ) ) . trans _
            convert mul_le_mul_of_nonneg_left ( dist_coe_le_dist x ) dist_nonneg
            simp

variable [HasLipschitzAdd β]

instance : Module 𝕜 (α →ᵇ β) :=
  { BoundedContinuousFunction.addCommMonoid with smul := · • ·,
    smul_add := fun c f g => ext $ fun x => smul_add c (f x) (g x),
    add_smul := fun c₁ c₂ f => ext $ fun x => add_smul c₁ c₂ (f x),
    mul_smul := fun c₁ c₂ f => ext $ fun x => mul_smul c₁ c₂ (f x),
    one_smul := fun f => ext $ fun x => one_smul 𝕜 (f x), smul_zero := fun c => ext $ fun x => smul_zero c,
    zero_smul := fun f => ext $ fun x => zero_smul 𝕜 (f x) }

variable (𝕜)

/--  The evaluation at a point, as a continuous linear map from `α →ᵇ β` to `β`. -/
def eval_clm (x : α) : (α →ᵇ β) →L[𝕜] β :=
  { toFun := fun f => f x,
    map_add' := fun f g => by
      simp only [Pi.add_apply, coe_add],
    map_smul' := fun c f => by
      simp only [coe_smul, RingHom.id_apply] }

@[simp]
theorem eval_clm_apply (x : α) (f : α →ᵇ β) : eval_clm 𝕜 x f = f x :=
  rfl

variable (α β)

/--  The linear map forgetting that a bounded continuous function is bounded. -/
@[simps]
def to_continuous_map_linear_map : (α →ᵇ β) →ₗ[𝕜] C(α, β) :=
  { toFun := to_continuous_map,
    map_smul' := by
      intros
      ext
      simp ,
    map_add' := by
      intros
      ext
      simp }

end HasBoundedSmul

section NormedSpace

/-!
### Normed space structure

In this section, if `β` is a normed space, then we show that the space of bounded
continuous functions from `α` to `β` inherits a normed space structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type _}

variable [TopologicalSpace α] [NormedGroup β]

variable {f g : α →ᵇ β} {x : α} {C : ℝ}

instance [NormedField 𝕜] [NormedSpace 𝕜 β] : NormedSpace 𝕜 (α →ᵇ β) :=
  ⟨fun c f => by
    refine' norm_of_normed_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
    exact fun x => trans_rel_right _ (norm_smul _ _) (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _))⟩

variable [NondiscreteNormedField 𝕜] [NormedSpace 𝕜 β]

variable [NormedGroup γ] [NormedSpace 𝕜 γ]

variable (α)

/-- 
Postcomposition of bounded continuous functions into a normed module by a continuous linear map is
a continuous linear map.
Upgraded version of `continuous_linear_map.comp_left_continuous`, similar to
`linear_map.comp_left`. -/
protected def _root_.continuous_linear_map.comp_left_continuous_bounded (g : β →L[𝕜] γ) : (α →ᵇ β) →L[𝕜] α →ᵇ γ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        of_normed_group (g ∘ f) (g.continuous.comp f.continuous) (∥g∥*∥f∥) fun x =>
          g.le_op_norm_of_le (f.norm_coe_le_norm x),
      map_add' := fun f g => by
        ext <;> simp ,
      map_smul' := fun c f => by
        ext <;> simp }
    ∥g∥ fun f => norm_of_normed_group_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg f)) _

@[simp]
theorem _root_.continuous_linear_map.comp_left_continuous_bounded_apply (g : β →L[𝕜] γ) (f : α →ᵇ β) (x : α) :
    (g.comp_left_continuous_bounded α f) x = g (f x) :=
  rfl

end NormedSpace

section NormedRing

/-!
### Normed ring structure

In this section, if `R` is a normed ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable [TopologicalSpace α] {R : Type _} [NormedRing R]

instance : Ringₓ (α →ᵇ R) :=
  { BoundedContinuousFunction.addCommGroup with one := const α 1,
    mul := fun f g =>
      of_normed_group (f*g) (f.continuous.mul g.continuous) (∥f∥*∥g∥) $ fun x =>
        le_transₓ (NormedRing.norm_mul (f x) (g x)) $
          mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _),
    one_mul := fun f => ext $ fun x => one_mulₓ (f x), mul_one := fun f => ext $ fun x => mul_oneₓ (f x),
    mul_assoc := fun f₁ f₂ f₃ => ext $ fun x => mul_assocₓ _ _ _,
    left_distrib := fun f₁ f₂ f₃ => ext $ fun x => left_distrib _ _ _,
    right_distrib := fun f₁ f₂ f₃ => ext $ fun x => right_distrib _ _ _ }

@[simp]
theorem coe_mul (f g : α →ᵇ R) : (⇑f*g) = f*g :=
  rfl

theorem mul_apply (f g : α →ᵇ R) (x : α) : (f*g) x = f x*g x :=
  rfl

instance : NormedRing (α →ᵇ R) :=
  { BoundedContinuousFunction.normedGroup with
    norm_mul := fun f g => norm_of_normed_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ }

end NormedRing

section NormedCommRing

/-!
### Normed commutative ring structure

In this section, if `R` is a normed commutative ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed commutative ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable [TopologicalSpace α] {R : Type _} [NormedCommRing R]

instance : CommRingₓ (α →ᵇ R) :=
  { BoundedContinuousFunction.ring with mul_comm := fun f₁ f₂ => ext $ fun x => mul_commₓ _ _ }

instance : NormedCommRing (α →ᵇ R) :=
  { BoundedContinuousFunction.commRing, BoundedContinuousFunction.normedGroup with }

end NormedCommRing

section NormedAlgebra

/-!
### Normed algebra structure

In this section, if `γ` is a normed algebra, then we show that the space of bounded
continuous functions from `α` to `γ` inherits a normed algebra structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type _} [NormedField 𝕜]

variable [TopologicalSpace α] [NormedGroup β] [NormedSpace 𝕜 β]

variable [NormedRing γ] [NormedAlgebra 𝕜 γ]

variable {f g : α →ᵇ γ} {x : α} {c : 𝕜}

/--  `bounded_continuous_function.const` as a `ring_hom`. -/
def C : 𝕜 →+* α →ᵇ γ :=
  { toFun := fun c : 𝕜 => const α ((algebraMap 𝕜 γ) c), map_one' := ext $ fun x => (algebraMap 𝕜 γ).map_one,
    map_mul' := fun c₁ c₂ => ext $ fun x => (algebraMap 𝕜 γ).map_mul _ _,
    map_zero' := ext $ fun x => (algebraMap 𝕜 γ).map_zero,
    map_add' := fun c₁ c₂ => ext $ fun x => (algebraMap 𝕜 γ).map_add _ _ }

instance : Algebra 𝕜 (α →ᵇ γ) :=
  { BoundedContinuousFunction.module, BoundedContinuousFunction.ring with toRingHom := C,
    commutes' := fun c f => ext $ fun x => Algebra.commutes' _ _,
    smul_def' := fun c f => ext $ fun x => Algebra.smul_def' _ _ }

@[simp]
theorem algebra_map_apply (k : 𝕜) (a : α) : algebraMap 𝕜 (α →ᵇ γ) k a = k • 1 := by
  rw [Algebra.algebra_map_eq_smul_one]
  rfl

instance [Nonempty α] : NormedAlgebra 𝕜 (α →ᵇ γ) :=
  { BoundedContinuousFunction.algebra with
    norm_algebra_map_eq := fun c => by
      calc ∥(algebraMap 𝕜 (α →ᵇ γ)).toFun c∥ = ∥(algebraMap 𝕜 γ) c∥ := _ _ = ∥c∥ := norm_algebra_map_eq _ _
      apply norm_const_eq ((algebraMap 𝕜 γ) c)
      assumption }

/-!
### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded continuous
functions from `α` to `𝕜`. -/


instance has_scalar' : HasScalar (α →ᵇ 𝕜) (α →ᵇ β) :=
  ⟨fun f : α →ᵇ 𝕜 g : α →ᵇ β =>
    of_normed_group (fun x => f x • g x) (f.continuous.smul g.continuous) (∥f∥*∥g∥) fun x =>
      calc ∥f x • g x∥ ≤ ∥f x∥*∥g x∥ := NormedSpace.norm_smul_le _ _
        _ ≤ ∥f∥*∥g∥ := mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
        ⟩

instance module' : Module (α →ᵇ 𝕜) (α →ᵇ β) :=
  Module.ofCore $
    { smul := · • ·, smul_add := fun c f₁ f₂ => ext $ fun x => smul_add _ _ _,
      add_smul := fun c₁ c₂ f => ext $ fun x => add_smul _ _ _,
      mul_smul := fun c₁ c₂ f => ext $ fun x => mul_smul _ _ _, one_smul := fun f => ext $ fun x => one_smul 𝕜 (f x) }

theorem norm_smul_le (f : α →ᵇ 𝕜) (g : α →ᵇ β) : ∥f • g∥ ≤ ∥f∥*∥g∥ :=
  norm_of_normed_group_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

end NormedAlgebra

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of bounded
continuous functions from `α` to `β`, by using the star operation pointwise.

If `𝕜` is normed field and a ⋆-ring over which `β` is a normed algebra and a
star module, then the space of bounded continuous functions from `α` to `β`
is a star module.

If `β` is a ⋆-ring in addition to being a normed ⋆-group, then `α →ᵇ β`
inherits a ⋆-ring structure.

In summary, if `β` is a C⋆-algebra over `𝕜`, then so is  `α →ᵇ β`; note that
completeness is guaranteed when `β` is complete (see
`bounded_continuous_function.complete`). -/


section NormedGroup

variable {𝕜 : Type _} [NormedField 𝕜] [StarRing 𝕜]

variable [TopologicalSpace α] [NormedGroup β] [StarAddMonoid β] [NormedStarMonoid β]

variable [NormedSpace 𝕜 β] [StarModule 𝕜 β]

-- failed to format: format: uncaught backtrack exception
instance
  : StarAddMonoid ( α →ᵇ β )
  where
    star f := f.comp star starNormedGroupHom . lipschitz
      star_involutive f := ext $ fun x => star_star ( f x )
      star_add f g := ext $ fun x => star_add ( f x ) ( g x )

/--  The right-hand side of this equality can be parsed `star ∘ ⇑f` because of the
instance `pi.has_star`. Upon inspecting the goal, one sees `⊢ ⇑(star f) = star ⇑f`.-/
@[simp]
theorem coe_star (f : α →ᵇ β) : ⇑star f = star f :=
  rfl

@[simp]
theorem star_apply (f : α →ᵇ β) (x : α) : star f x = star (f x) :=
  rfl

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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
   (Term.typeSpec ":" (Term.app `NormedStarMonoid [(Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `α " →ᵇ " `β)])))
  (Command.whereStructInst
   "where"
   [(group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `norm_star
        [(Term.simpleBinder [(Term.simpleBinder [`f] [])] [])]
        []
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `norm_eq)] "]"] []) [])
            (group (Tactic.congr "congr" [] []) [])
            (group (Tactic.ext "ext" [] []) [])
            (group
             (Mathlib.Tactic.Conv.convLHS
              "conv_lhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Mathlib.Tactic.Conv.find
                   "find"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.hole "_") "∥")
                   "=>"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.tacticErw__
                        "erw"
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule
                           []
                           (Term.app
                            (Term.explicit "@" `norm_star)
                            [`β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `f [`x])]))]
                         "]")
                        [])
                       [])])))
                  [])])))
             [])]))))))
     [])])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructField', expected 'Lean.Parser.Command.whereStructField.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `norm_eq)] "]"] []) [])
      (group (Tactic.congr "congr" [] []) [])
      (group (Tactic.ext "ext" [] []) [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Mathlib.Tactic.Conv.find
             "find"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.hole "_") "∥")
             "=>"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      (Term.explicit "@" `norm_star)
                      [`β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `f [`x])]))]
                   "]")
                  [])
                 [])])))
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
  (Mathlib.Tactic.Conv.convLHS
   "conv_lhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Mathlib.Tactic.Conv.find
        "find"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.hole "_") "∥")
        "=>"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 (Term.explicit "@" `norm_star)
                 [`β (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `f [`x])]))]
              "]")
             [])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.find', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.Conv.convSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : NormedStarMonoid α →ᵇ β
  where norm_star f := by simp only [ norm_eq ] congr ext conv_lhs => find ∥ _ ∥ => erw [ @ norm_star β _ _ _ f x ]

-- failed to format: format: uncaught backtrack exception
instance : StarModule 𝕜 ( α →ᵇ β ) where star_smul k f := ext $ fun x => star_smul k ( f x )

end NormedGroup

section CstarRing

variable [TopologicalSpace α]

variable [NormedRing β] [StarRing β]

instance [NormedStarMonoid β] : StarRing (α →ᵇ β) :=
  { BoundedContinuousFunction.starAddMonoid with star_mul := fun f g => ext $ fun x => star_mul (f x) (g x) }

variable [CstarRing β]

instance : CstarRing (α →ᵇ β) where
  norm_star_mul_self := by
    intro f
    refine' le_antisymmₓ _ _
    ·
      rw [← sq, norm_le (sq_nonneg _)]
      dsimp [star_apply]
      intro x
      rw [CstarRing.norm_star_mul_self, ← sq]
      refine' sq_le_sq' _ _
      ·
        linarith [norm_nonneg (f x), norm_nonneg f]
      ·
        exact norm_coe_le_norm f x
    ·
      rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _), norm_le (Real.sqrt_nonneg _)]
      intro x
      rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CstarRing.norm_star_mul_self]
      exact norm_coe_le_norm (star f*f) x

end CstarRing

section NormedLatticeOrderedGroup

variable [TopologicalSpace α] [NormedLatticeAddCommGroup β]

instance : PartialOrderₓ (α →ᵇ β) :=
  PartialOrderₓ.lift (fun f => f.to_fun)
    (by
      tidy)

/-- 
Continuous normed lattice group valued functions form a meet-semilattice
-/
instance : SemilatticeInf (α →ᵇ β) :=
  { BoundedContinuousFunction.partialOrder with
    inf := fun f g =>
      { toFun := fun t => f t⊓g t, continuous_to_fun := f.continuous.inf g.continuous,
        bounded' := by
          cases' f.bounded' with C₁ hf
          cases' g.bounded' with C₂ hg
          refine' ⟨C₁+C₂, fun x y => _⟩
          simp_rw [NormedGroup.dist_eq]  at hf hg⊢
          exact (norm_inf_sub_inf_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) },
    inf_le_left := fun f g => ContinuousMap.le_def.mpr fun _ => inf_le_left,
    inf_le_right := fun f g => ContinuousMap.le_def.mpr fun _ => inf_le_right,
    le_inf := fun f g₁ g₂ w₁ w₂ =>
      ContinuousMap.le_def.mpr fun _ => le_inf (ContinuousMap.le_def.mp w₁ _) (ContinuousMap.le_def.mp w₂ _) }

instance : SemilatticeSup (α →ᵇ β) :=
  { BoundedContinuousFunction.partialOrder with
    sup := fun f g =>
      { toFun := fun t => f t⊔g t, continuous_to_fun := f.continuous.sup g.continuous,
        bounded' := by
          cases' f.bounded' with C₁ hf
          cases' g.bounded' with C₂ hg
          refine' ⟨C₁+C₂, fun x y => _⟩
          simp_rw [NormedGroup.dist_eq]  at hf hg⊢
          exact (norm_sup_sub_sup_le_add_norm _ _ _ _).trans (add_le_add (hf _ _) (hg _ _)) },
    le_sup_left := fun f g => ContinuousMap.le_def.mpr fun _ => le_sup_left,
    le_sup_right := fun f g => ContinuousMap.le_def.mpr fun _ => le_sup_right,
    sup_le := fun f g₁ g₂ w₁ w₂ =>
      ContinuousMap.le_def.mpr fun _ => sup_le (ContinuousMap.le_def.mp w₁ _) (ContinuousMap.le_def.mp w₂ _) }

instance : Lattice (α →ᵇ β) :=
  { BoundedContinuousFunction.semilatticeSup, BoundedContinuousFunction.semilatticeInf with }

@[simp]
theorem coe_fn_sup (f g : α →ᵇ β) : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem coe_fn_abs (f : α →ᵇ β) : ⇑|f| = |f| :=
  rfl

instance : NormedLatticeAddCommGroup (α →ᵇ β) :=
  { BoundedContinuousFunction.lattice with
    add_le_add_left := by
      intro f g h₁ h t
      simp only [coe_to_continuous_fun, Pi.add_apply, add_le_add_iff_left, coe_add, ContinuousMap.to_fun_eq_coe]
      exact h₁ _,
    solid := by
      intro f g h
      have i1 : ∀ t, ∥f t∥ ≤ ∥g t∥ := fun t => solid (h t)
      rw [norm_le (norm_nonneg _)]
      exact fun t => (i1 t).trans (norm_coe_le_norm g t) }

end NormedLatticeOrderedGroup

end BoundedContinuousFunction

