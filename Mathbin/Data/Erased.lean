import Mathbin.Data.Equiv.Basic

/-!
# A type for VM-erased data

This file defines a type `erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `erased α` is
represented as `0`, just like types and proofs.
-/


universe u

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " `erased α` is the same as `α`, except that the elements\n  of `erased α` are erased in the VM in the same way as types\n  and proofs. This can be used to track data without storing it\n  literally. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `Erased [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`α] [":" (Term.sort "Sort" [`u])] [] ")")]
   [(Term.typeSpec ":" (Term.sort "Sort" [(Level.max "max" [(numLit "1") `u])]))])
  (Command.declValSimple
   ":="
   (Init.Data.Sigma.Basic.«termΣ'_,_»
    "Σ'"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.arrow `α "→" (Term.prop "Prop"))]))
    ", "
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
     ","
     («term_=_» (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" («term_=_» `a "=" `b))) "=" `s)))
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
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.arrow `α "→" (Term.prop "Prop"))]))
   ", "
   («term∃_,_»
    "∃"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    ","
    («term_=_» (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" («term_=_» `a "=" `b))) "=" `s)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   ","
   («term_=_» (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" («term_=_» `a "=" `b))) "=" `s))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" («term_=_» `a "=" `b))) "=" `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" («term_=_» `a "=" `b)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `a "=" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" («term_=_» `a "=" `b))) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    `erased α` is the same as `α`, except that the elements
      of `erased α` are erased in the VM in the same way as types
      and proofs. This can be used to track data without storing it
      literally. -/
  def Erased ( α : Sort u ) : Sort max 1 u := Σ' s : α → Prop , ∃ a , fun b => a = b = s

namespace Erased

/--  Erase a value. -/
@[inline]
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/--  Extracts the erased value, noncomputably. -/
noncomputable def out {α} : Erased α → α
  | ⟨s, h⟩ => Classical.some h

/-- 
Extracts the erased value, if it is a type.

Note: `(mk a).out_type` is not definitionally equal to `a`.
-/
@[reducible]
def out_type (a : Erased (Sort u)) : Sort u :=
  out a

/--  Extracts the erased value, if it is a proof. -/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a

@[simp]
theorem out_mk {α} (a : α) : (mk a).out = a := by
  let h
  show Classical.some h = a
  have := Classical.some_spec h
  exact cast (congr_funₓ this a).symm rfl

@[simp]
theorem mk_out {α} : ∀ a : Erased α, mk (out a) = a
  | ⟨s, h⟩ => by
    simp [mk] <;> congr <;> exact Classical.some_spec h

@[ext]
theorem out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b := by
  simpa using congr_argₓ mk h

/--  Equivalence between `erased α` and `α`. -/
noncomputable def Equivₓ α : Erased α ≃ α :=
  ⟨out, mk, mk_out, out_mk⟩

instance (α : Type u) : HasRepr (Erased α) :=
  ⟨fun _ => "erased"⟩

instance (α : Type u) : HasToString (Erased α) :=
  ⟨fun _ => "erased"⟩

unsafe instance (α : Type u) : has_to_format (Erased α) :=
  ⟨fun _ => ("erased" : format)⟩

/--  Computably produce an erased value from a proof of nonemptiness. -/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)

@[simp]
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩

instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

/-- 
`(>>=)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `monad`).
-/
def bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]
theorem bind_eq_out {α β} a f : @bind α β a f = f a.out := by
  delta' bind bind._proof_1 <;> cases f a.out <;> rfl

/-- 
Collapses two levels of erasure.
-/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id

@[simp]
theorem join_eq_out {α} a : @join α a = a.out :=
  bind_eq_out _ _

/-- 
`(<$>)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `functor`).
-/
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)

@[simp]
theorem map_out {α β} {f : α → β} (a : Erased α) : (a.map f).out = f a.out := by
  simp [map]

instance : Monadₓ Erased where
  pure := @mk
  bind := @bind
  map := @map

@[simp]
theorem pure_def {α} : (pure : α → Erased α) = @mk _ :=
  rfl

@[simp]
theorem bind_def {α β} : (· >>= · : Erased α → (α → Erased β) → Erased β) = @bind _ _ :=
  rfl

@[simp]
theorem map_def {α β} : (· <$> · : (α → β) → Erased α → Erased β) = @map _ _ :=
  rfl

instance : IsLawfulMonad Erased := by
  refine' { .. } <;> intros <;> ext <;> simp

end Erased

