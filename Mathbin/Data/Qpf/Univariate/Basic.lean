import Mathbin.Data.Pfunctor.Univariate.M

/-!

# Quotients of Polynomial Functors

We assume the following:

`P`   : a polynomial functor
`W`   : its W-type
`M`   : its M-type
`F`   : a functor

We define:

`q`   : `qpf` data, representing `F` as a quotient of `P`

The main goal is to construct:

`fix`   : the initial algebra with structure map `F fix → fix`.
`cofix` : the final coalgebra with structure map `cofix → F cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.

The present theory focuses on the univariate case for qpfs

## References

* [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]

-/


universe u

/-- 
Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means that for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of the object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/
class Qpf (F : Type u → Type u) [Functor F] where
  p : Pfunctor.{u}
  abs : ∀ {α}, P.obj α → F α
  repr : ∀ {α}, F α → P.obj α
  abs_repr : ∀ {α} x : F α, abs (reprₓ x) = x
  abs_map : ∀ {α β} f : α → β p : P.obj α, abs (f <$> p) = f <$> abs p

namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

include q

open functor (Liftp Liftr)

theorem id_map {α : Type _} (x : F α) : id <$> x = x := by
  rw [← abs_repr x]
  cases' reprₓ x with a f
  rw [← abs_map]
  rfl

theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) (x : F α) : (g ∘ f) <$> x = g <$> f <$> x := by
  rw [← abs_repr x]
  cases' reprₓ x with a f
  rw [← abs_map, ← abs_map, ← abs_map]
  rfl

theorem IsLawfulFunctor (h : ∀ α β : Type u, @Functor.mapConst F _ α _ = Functor.map ∘ Function.const β) :
    IsLawfulFunctor F :=
  { map_const_eq := h, id_map := @id_map F _ _, comp_map := @comp_map F _ _ }

section

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : F α) : liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  ·
    rintro ⟨y, hy⟩
    cases' h : reprₓ y with a f
    use a, fun i => (f i).val
    constructor
    ·
      rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨a, f, h₀, h₁⟩
  dsimp  at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, h₀]
  rfl

theorem liftp_iff' {α : Type u} (p : α → Prop) (x : F α) : liftp p x ↔ ∃ u : q.P.obj α, abs u = x ∧ ∀ i, p (u.snd i) :=
  by
  constructor
  ·
    rintro ⟨y, hy⟩
    cases' h : reprₓ y with a f
    use ⟨a, fun i => (f i).val⟩
    dsimp
    constructor
    ·
      rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨⟨a, f⟩, h₀, h₁⟩
  dsimp  at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, ← h₀]
  rfl

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : F α) :
    liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  ·
    rintro ⟨u, xeq, yeq⟩
    cases' h : reprₓ u with a f
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    ·
      rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    ·
      rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  dsimp
  constructor
  ·
    rw [xeq, ← abs_map]
    rfl
  rw [yeq, ← abs_map]
  rfl

end

/--  does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {α : Type _} (g : F α → α) : q.P.W → α
  | ⟨a, f⟩ => g (abs ⟨a, fun x => recF (f x)⟩)

theorem recF_eq {α : Type _} (g : F α → α) (x : q.P.W) : recF g x = g (abs (recF g <$> x.dest)) := by
  cases x <;> rfl

theorem recF_eq' {α : Type _} (g : F α → α) (a : q.P.A) (f : q.P.B a → q.P.W) :
    recF g ⟨a, f⟩ = g (abs (recF g <$> ⟨a, f⟩)) :=
  rfl

/--  two trees are equivalent if their F-abstractions are -/
inductive Wequiv : q.P.W → q.P.W → Prop
  | ind (a : q.P.A) (f f' : q.P.B a → q.P.W) : (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
  | abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
  | trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w

/--  recF is insensitive to the representation -/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) : Wequiv x y → recF u x = recF u y := by
  cases' x with a f
  cases' y with b g
  intro h
  induction h
  case qpf.Wequiv.ind a f f' h ih =>
    simp only [recF_eq', Pfunctor.map_eq, Function.comp, ih]
  case qpf.Wequiv.abs a f a' f' h =>
    simp only [recF_eq', abs_map, h]
  case qpf.Wequiv.trans x y z e₁ e₂ ih₁ ih₂ =>
    exact Eq.trans ih₁ ih₂

theorem Wequiv.abs' (x y : q.P.W) (h : abs x.dest = abs y.dest) : Wequiv x y := by
  cases x
  cases y
  apply Wequiv.abs
  apply h

theorem Wequiv.refl (x : q.P.W) : Wequiv x x := by
  cases' x with a f <;> exact Wequiv.abs a f a f rfl

theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x := by
  cases' x with a f
  cases' y with b g
  intro h
  induction h
  case qpf.Wequiv.ind a f f' h ih =>
    exact Wequiv.ind _ _ _ ih
  case qpf.Wequiv.abs a f a' f' h =>
    exact Wequiv.abs _ _ _ _ h.symm
  case qpf.Wequiv.trans x y z e₁ e₂ ih₁ ih₂ =>
    exact Qpf.Wequiv.trans _ _ _ ih₂ ih₁

/--  maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W → q.P.W :=
  recF (Pfunctor.W.mk ∘ reprₓ)

theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x := by
  induction' x with a f ih
  apply Wequiv.trans
  ·
    change Wequiv (Wrepr ⟨a, f⟩) (Pfunctor.W.mk (Wrepr <$> ⟨a, f⟩))
    apply Wequiv.abs'
    have : Wrepr ⟨a, f⟩ = Pfunctor.W.mk (reprₓ (abs (Wrepr <$> ⟨a, f⟩))) := rfl
    rw [this, Pfunctor.W.dest_mk, abs_repr]
    rfl
  apply Wequiv.ind
  exact ih

/-- 
Define the fixed point as the quotient of trees under the equivalence relation `Wequiv`.
-/
def W_setoid : Setoidₓ q.P.W :=
  ⟨Wequiv, @Wequiv.refl _ _ _, @Wequiv.symm _ _ _, @Wequiv.trans _ _ _⟩

attribute [local instance] W_setoid

/--  inductive type defined as initial algebra of a Quotient of Polynomial Functor -/
@[nolint has_inhabited_instance]
def fix (F : Type u → Type u) [Functor F] [q : Qpf F] :=
  Quotientₓ (W_setoid : Setoidₓ q.P.W)

/--  recursor of a type defined by a qpf -/
def fix.rec {α : Type _} (g : F α → α) : fix F → α :=
  Quot.lift (recF g) (recF_eq_of_Wequiv g)

/--  access the underlying W-type of a fixpoint data type -/
def fix_to_W : fix F → q.P.W :=
  Quotientₓ.lift Wrepr (recF_eq_of_Wequiv fun x => @Pfunctor.W.mk q.P (reprₓ x))

/--  constructor of a type defined by a qpf -/
def fix.mk (x : F (fix F)) : fix F :=
  Quot.mk _ (Pfunctor.W.mk (fix_to_W <$> reprₓ x))

/--  destructor of a type defined by a qpf -/
def fix.dest : fix F → F (fix F) :=
  fix.rec (Functor.map fix.mk)

theorem fix.rec_eq {α : Type _} (g : F α → α) (x : F (fix F)) : fix.rec g (fix.mk x) = g (fix.rec g <$> x) :=
  have : recF g ∘ fix_to_W = fix.rec g := by
    apply funext
    apply Quotientₓ.ind
    intro x
    apply recF_eq_of_Wequiv
    rw [fix_to_W]
    apply Wrepr_equiv
  by
  conv => lhs rw [fix.rec, fix.mk]dsimp
  cases' h : reprₓ x with a f
  rw [Pfunctor.map_eq, recF_eq, ← Pfunctor.map_eq, Pfunctor.W.dest_mk, ← Pfunctor.comp_map, abs_map, ← h, abs_repr,
    this]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `fix.ind_aux [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a] [":" `q.P.A] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow (Term.app `q.P.B [`a]) "→" `q.P.W)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `fix.mk
      [(Term.app
        `abs
        [(Term.anonymousCtor
          "⟨"
          [`a
           ","
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.app `f [`x]) "⟧")))]
          "⟩")])])
     "="
     (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.anonymousCtor "⟨" [`a "," `f] "⟩") "⟧"))))
  (Command.declValSimple
   ":="
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `fix.mk
          [(Term.app
            `abs
            [(Term.anonymousCtor
              "⟨"
              [`a
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x] [])]
                 "=>"
                 (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.app `f [`x]) "⟧")))]
              "⟩")])])
         "="
         (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.app `Wrepr [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "⟧")))]
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.apply "apply" `Quot.sound) [])
          (group (Tactic.apply "apply" `Wequiv.abs') [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Pfunctor.W.dest_mk)
              ","
              (Tactic.rwRule [] `abs_map)
              ","
              (Tactic.rwRule [] `abs_repr)
              ","
              (Tactic.rwRule ["←"] `abs_map)
              ","
              (Tactic.rwRule [] `Pfunctor.map_eq)]
             "]")
            [])
           [])
          (group
           (Tactic.Conv.conv
            "conv"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(group (Tactic.Conv.rhs "rhs") [])
               (group
                (Tactic.Conv.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Wrepr)
                   ","
                   (Tactic.simpLemma [] [] `recF_eq)
                   ","
                   (Tactic.simpLemma [] [] `Pfunctor.W.dest_mk)
                   ","
                   (Tactic.simpLemma [] [] `abs_repr)]
                  "]"]
                 [])
                [])])))
           [])
          (group (Tactic.tacticRfl "rfl") [])])))))
    []
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
        (group (Tactic.apply "apply" `Quot.sound) [])
        (group (Tactic.apply "apply" `Wrepr_equiv) [])]))))
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
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.app
         `fix.mk
         [(Term.app
           `abs
           [(Term.anonymousCtor
             "⟨"
             [`a
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x] [])]
                "=>"
                (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.app `f [`x]) "⟧")))]
             "⟩")])])
        "="
        (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.app `Wrepr [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "⟧")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.apply "apply" `Quot.sound) [])
         (group (Tactic.apply "apply" `Wequiv.abs') [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Pfunctor.W.dest_mk)
             ","
             (Tactic.rwRule [] `abs_map)
             ","
             (Tactic.rwRule [] `abs_repr)
             ","
             (Tactic.rwRule ["←"] `abs_map)
             ","
             (Tactic.rwRule [] `Pfunctor.map_eq)]
            "]")
           [])
          [])
         (group
          (Tactic.Conv.conv
           "conv"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(group (Tactic.Conv.rhs "rhs") [])
              (group
               (Tactic.Conv.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Wrepr)
                  ","
                  (Tactic.simpLemma [] [] `recF_eq)
                  ","
                  (Tactic.simpLemma [] [] `Pfunctor.W.dest_mk)
                  ","
                  (Tactic.simpLemma [] [] `abs_repr)]
                 "]"]
                [])
               [])])))
          [])
         (group (Tactic.tacticRfl "rfl") [])])))))
   []
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
       (group (Tactic.apply "apply" `Quot.sound) [])
       (group (Tactic.apply "apply" `Wrepr_equiv) [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
      (group (Tactic.apply "apply" `Quot.sound) [])
      (group (Tactic.apply "apply" `Wrepr_equiv) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" `Wrepr_equiv)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Wrepr_equiv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `Quot.sound)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Quot.sound
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" `Quot.sound) [])
      (group (Tactic.apply "apply" `Wequiv.abs') [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Pfunctor.W.dest_mk)
          ","
          (Tactic.rwRule [] `abs_map)
          ","
          (Tactic.rwRule [] `abs_repr)
          ","
          (Tactic.rwRule ["←"] `abs_map)
          ","
          (Tactic.rwRule [] `Pfunctor.map_eq)]
         "]")
        [])
       [])
      (group
       (Tactic.Conv.conv
        "conv"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.rhs "rhs") [])
           (group
            (Tactic.Conv.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Wrepr)
               ","
               (Tactic.simpLemma [] [] `recF_eq)
               ","
               (Tactic.simpLemma [] [] `Pfunctor.W.dest_mk)
               ","
               (Tactic.simpLemma [] [] `abs_repr)]
              "]"]
             [])
            [])])))
       [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.Conv.conv
   "conv"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.rhs "rhs") [])
      (group
       (Tactic.Conv.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `Wrepr)
          ","
          (Tactic.simpLemma [] [] `recF_eq)
          ","
          (Tactic.simpLemma [] [] `Pfunctor.W.dest_mk)
          ","
          (Tactic.simpLemma [] [] `abs_repr)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.conv', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
theorem
  fix.ind_aux
  ( a : q.P.A ) ( f : q.P.B a → q.P.W ) : fix.mk abs ⟨ a , fun x => ⟦ f x ⟧ ⟩ = ⟦ ⟨ a , f ⟩ ⟧
  :=
    have
      : fix.mk abs ⟨ a , fun x => ⟦ f x ⟧ ⟩ = ⟦ Wrepr ⟨ a , f ⟩ ⟧
        :=
        by
          apply Quot.sound
            apply Wequiv.abs'
            rw [ Pfunctor.W.dest_mk , abs_map , abs_repr , ← abs_map , Pfunctor.map_eq ]
            conv => rhs simp only [ Wrepr , recF_eq , Pfunctor.W.dest_mk , abs_repr ]
            rfl
      by rw [ this ] apply Quot.sound apply Wrepr_equiv

theorem fix.ind_rec {α : Type u} (g₁ g₂ : fix F → α)
    (h : ∀ x : F (fix F), g₁ <$> x = g₂ <$> x → g₁ (fix.mk x) = g₂ (fix.mk x)) : ∀ x, g₁ x = g₂ x := by
  apply Quot.ind
  intro x
  induction' x with a f ih
  change g₁ (⟦⟨a, f⟩⟧) = g₂ (⟦⟨a, f⟩⟧)
  rw [← fix.ind_aux a f]
  apply h
  rw [← abs_map, ← abs_map, Pfunctor.map_eq, Pfunctor.map_eq]
  dsimp [Function.comp]
  congr with x
  apply ih

theorem fix.rec_unique {α : Type u} (g : F α → α) (h : fix F → α) (hyp : ∀ x, h (fix.mk x) = g (h <$> x)) :
    fix.rec g = h := by
  ext x
  apply fix.ind_rec
  intro x hyp'
  rw [hyp, ← hyp', fix.rec_eq]

theorem fix.mk_dest (x : fix F) : fix.mk (fix.dest x) = x := by
  change (fix.mk ∘ fix.dest) x = id x
  apply fix.ind_rec
  intro x
  dsimp
  rw [fix.dest, fix.rec_eq, id_map, comp_map]
  intro h
  rw [h]

theorem fix.dest_mk (x : F (fix F)) : fix.dest (fix.mk x) = x := by
  unfold fix.dest
  rw [fix.rec_eq, ← fix.dest, ← comp_map]
  conv => rhs rw [← id_map x]
  congr with x
  apply fix.mk_dest

theorem fix.ind (p : fix F → Prop) (h : ∀ x : F (fix F), liftp p x → p (fix.mk x)) : ∀ x, p x := by
  apply Quot.ind
  intro x
  induction' x with a f ih
  change p (⟦⟨a, f⟩⟧)
  rw [← fix.ind_aux a f]
  apply h
  rw [liftp_iff]
  refine' ⟨_, _, rfl, _⟩
  apply ih

end Qpf

namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

include q

open functor (Liftp Liftr)

/--  does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
def corecF {α : Type _} (g : α → F α) : α → q.P.M :=
  Pfunctor.M.corec fun x => reprₓ (g x)

theorem corecF_eq {α : Type _} (g : α → F α) (x : α) : Pfunctor.M.dest (corecF g x) = corecF g <$> reprₓ (g x) := by
  rw [corecF, Pfunctor.M.dest_corec]

/--  A pre-congruence on q.P.M *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def is_precongr (r : q.P.M → q.P.M → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y → abs (Quot.mk r <$> Pfunctor.M.dest x) = abs (Quot.mk r <$> Pfunctor.M.dest y)

/--  The maximal congruence on q.P.M -/
def Mcongr : q.P.M → q.P.M → Prop := fun x y => ∃ r, is_precongr r ∧ r x y

/--  coinductive type defined as the final coalgebra of a qpf -/
def cofix (F : Type u → Type u) [Functor F] [q : Qpf F] :=
  Quot (@Mcongr F _ q)

instance [Inhabited q.P.A] : Inhabited (cofix F) :=
  ⟨Quot.mk _ (default _)⟩

/--  corecursor for type defined by `cofix` -/
def cofix.corec {α : Type _} (g : α → F α) (x : α) : cofix F :=
  Quot.mk _ (corecF g x)

/--  destructor for type defined by `cofix` -/
def cofix.dest : cofix F → F (cofix F) :=
  Quot.lift (fun x => Quot.mk Mcongr <$> abs (Pfunctor.M.dest x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      dsimp
      have : ∀ x y, r x y → Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      dsimp
      conv => lhs rw [comp_map, ← abs_map, pr rxy, abs_map, ← comp_map])

theorem cofix.dest_corec {α : Type u} (g : α → F α) (x : α) : cofix.dest (cofix.corec g x) = cofix.corec g <$> g x := by
  conv => lhs rw [cofix.dest, cofix.corec]
  dsimp
  rw [corecF_eq, abs_map, abs_repr, ← comp_map]
  rfl

private theorem cofix.bisim_aux (r : cofix F → cofix F → Prop) (h' : ∀ x, r x x)
    (h : ∀ x y, r x y → Quot.mk r <$> cofix.dest x = Quot.mk r <$> cofix.dest y) : ∀ x y, r x y → x = y := by
  intro x
  apply Quot.induction_on x
  clear x
  intro x y
  apply Quot.induction_on y
  clear y
  intro y rxy
  apply Quot.sound
  let r' := fun x y => r (Quot.mk _ x) (Quot.mk _ y)
  have : is_precongr r' := by
    intro a b r'ab
    have h₀ :
      Quot.mk r <$> Quot.mk Mcongr <$> abs (Pfunctor.M.dest a) =
        Quot.mk r <$> Quot.mk Mcongr <$> abs (Pfunctor.M.dest b) :=
      h _ _ r'ab
    have h₁ : ∀ u v : q.P.M, Mcongr u v → Quot.mk r' u = Quot.mk r' v := by
      intro u v cuv
      apply Quot.sound
      dsimp [r']
      rw [Quot.sound cuv]
      apply h'
    let f : Quot r → Quot r' :=
      Quot.lift (Quot.lift (Quot.mk r') h₁)
        (by
          intro c
          apply Quot.induction_on c
          clear c
          intro c d
          apply Quot.induction_on d
          clear d
          intro d rcd
          apply Quot.sound
          apply rcd)
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this, Pfunctor.comp_map _ _ f, Pfunctor.comp_map _ _ (Quot.mk r), abs_map, abs_map, abs_map, h₀]
    rw [Pfunctor.comp_map _ _ f, Pfunctor.comp_map _ _ (Quot.mk r), abs_map, abs_map, abs_map]
  refine' ⟨r', this, rxy⟩

theorem cofix.bisim_rel (r : cofix F → cofix F → Prop)
    (h : ∀ x y, r x y → Quot.mk r <$> cofix.dest x = Quot.mk r <$> cofix.dest y) : ∀ x y, r x y → x = y :=
  let r' x y := x = y ∨ r x y
  by
  intro x y rxy
  apply cofix.bisim_aux r'
  ·
    intro x
    left
    rfl
  ·
    intro x y r'xy
    cases r'xy
    ·
      rw [r'xy]
    have : ∀ x y, r x y → r' x y := fun x y h => Or.inr h
    rw [← Quot.factor_mk_eq _ _ this]
    dsimp
    rw [@comp_map _ _ q _ _ _ (Quot.mk r), @comp_map _ _ q _ _ _ (Quot.mk r)]
    rw [h _ _ r'xy]
  right
  exact rxy

theorem cofix.bisim (r : cofix F → cofix F → Prop) (h : ∀ x y, r x y → liftr r (cofix.dest x) (cofix.dest y)) :
    ∀ x y, r x y → x = y := by
  apply cofix.bisim_rel
  intro x y rxy
  rcases(liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq, dyeq, ← abs_map, ← abs_map, Pfunctor.map_eq, Pfunctor.map_eq]
  congr 2 with i
  apply Quot.sound
  apply h'

theorem cofix.bisim' {α : Type _} (Q : α → Prop) (u v : α → cofix F)
    (h :
      ∀ x,
        Q x →
          ∃ a f f',
            cofix.dest (u x) = abs ⟨a, f⟩ ∧
              cofix.dest (v x) = abs ⟨a, f'⟩ ∧ ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : cofix F => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩
      rw [liftr_iff]
      refine' ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩

end Qpf

namespace Qpf

variable {F₂ : Type u → Type u} [Functor F₂] [q₂ : Qpf F₂]

variable {F₁ : Type u → Type u} [Functor F₁] [q₁ : Qpf F₁]

include q₂ q₁

/--  composition of qpfs gives another qpf  -/
def comp : Qpf (Functor.Comp F₂ F₁) :=
  { p := Pfunctor.comp q₂.P q₁.P,
    abs := fun α => by
      dsimp [Functor.Comp]
      intro p
      exact abs ⟨p.1.1, fun x => abs ⟨p.1.2 x, fun y => p.2 ⟨x, y⟩⟩⟩,
    repr := fun α => by
      dsimp [Functor.Comp]
      intro y
      refine' ⟨⟨(reprₓ y).1, fun u => (reprₓ ((reprₓ y).2 u)).1⟩, _⟩
      dsimp [Pfunctor.comp]
      intro x
      exact (reprₓ ((reprₓ y).2 x.1)).snd x.2,
    abs_repr := fun α => by
      abstract 
        dsimp [Functor.Comp]
        intro x
        conv => rhs rw [← abs_repr x]
        cases' h : reprₓ x with a f
        dsimp
        congr with x
        cases' h' : reprₓ (f x) with b g
        dsimp
        rw [← h', abs_repr],
    abs_map := fun α β f => by
      abstract 
        dsimp [Functor.Comp, Pfunctor.comp]
        intro p
        cases' p with a g
        dsimp
        cases' a with b h
        dsimp
        symm
        trans
        symm
        apply abs_map
        congr
        rw [Pfunctor.map_eq]
        dsimp [Function.comp]
        simp [abs_map]
        constructor
        rfl
        ext x
        rw [← abs_map]
        rfl }

end Qpf

namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

variable {G : Type u → Type u} [Functor G]

variable {FG_abs : ∀ {α}, F α → G α}

variable {FG_repr : ∀ {α}, G α → F α}

/--  Given a qpf `F` and a well-behaved surjection `FG_abs` from F α to
functor G α, `G` is a qpf. We can consider `G` a quotient on `F` where
elements `x y : F α` are in the same equivalence class if
`FG_abs x = FG_abs y`  -/
def quotient_qpf (FG_abs_repr : ∀ {α} x : G α, FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} f : α → β x : F α, FG_abs (f <$> x) = f <$> FG_abs x) : Qpf G :=
  { p := q.P, abs := fun {α} p => FG_abs (abs p), repr := fun {α} x => reprₓ (FG_repr x),
    abs_repr := fun {α} x => by
      rw [abs_repr, FG_abs_repr],
    abs_map := fun {α β} f x => by
      rw [abs_map, FG_abs_map] }

end Qpf

namespace Qpf

variable {F : Type u → Type u} [Functor F] [q : Qpf F]

include q

open functor (Liftp Liftr Supp)

open Set

theorem mem_supp {α : Type u} (x : F α) (u : α) : u ∈ supp x ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f '' univ := by
  rw [supp]
  dsimp
  constructor
  ·
    intro h a f haf
    have : liftp (fun u => u ∈ f '' univ) x := by
      rw [liftp_iff]
      refine' ⟨a, f, haf.symm, fun i => mem_image_of_mem _ (mem_univ _)⟩
    exact h this
  intro h p
  rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]
  apply h'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `supp_eq [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [`u])] "}")
    (Term.explicitBinder "(" [`x] [":" (Term.app `F [`α])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `supp [`x])
     "="
     (Set.«term{_|_}»
      "{"
      `u
      "|"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`a `f] [])]
       ","
       (Term.arrow
        («term_=_» (Term.app `abs [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "=" `x)
        "→"
        (Init.Core.«term_∈_» `u " ∈ " (Set.Data.Set.Basic.term_''_ `f " '' " `univ))))
      "}"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.«tactic_<;>_» (Tactic.ext "ext" [] []) "<;>" (Tactic.apply "apply" `mem_supp)) [])])))
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
     [(group (Tactic.«tactic_<;>_» (Tactic.ext "ext" [] []) "<;>" (Tactic.apply "apply" `mem_supp)) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.ext "ext" [] []) "<;>" (Tactic.apply "apply" `mem_supp))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" `mem_supp)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_supp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `supp [`x])
   "="
   (Set.«term{_|_}»
    "{"
    `u
    "|"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`a `f] [])]
     ","
     (Term.arrow
      («term_=_» (Term.app `abs [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "=" `x)
      "→"
      (Init.Core.«term_∈_» `u " ∈ " (Set.Data.Set.Basic.term_''_ `f " '' " `univ))))
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `u
   "|"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`a `f] [])]
    ","
    (Term.arrow
     («term_=_» (Term.app `abs [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "=" `x)
     "→"
     (Init.Core.«term_∈_» `u " ∈ " (Set.Data.Set.Basic.term_''_ `f " '' " `univ))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`a `f] [])]
   ","
   (Term.arrow
    («term_=_» (Term.app `abs [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "=" `x)
    "→"
    (Init.Core.«term_∈_» `u " ∈ " (Set.Data.Set.Basic.term_''_ `f " '' " `univ))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   («term_=_» (Term.app `abs [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "=" `x)
   "→"
   (Init.Core.«term_∈_» `u " ∈ " (Set.Data.Set.Basic.term_''_ `f " '' " `univ)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `u " ∈ " (Set.Data.Set.Basic.term_''_ `f " '' " `univ))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.term_''_ `f " '' " `univ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  («term_=_» (Term.app `abs [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")]) "=" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `abs [(Term.anonymousCtor "⟨" [`a "," `f] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`a "," `f] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `abs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
  supp_eq
  { α : Type u } ( x : F α ) : supp x = { u | ∀ a f , abs ⟨ a , f ⟩ = x → u ∈ f '' univ }
  := by ext <;> apply mem_supp

theorem has_good_supp_iff {α : Type u} (x : F α) :
    (∀ p, liftp p x ↔ ∀, ∀ u ∈ supp x, ∀, p u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ a' f', abs ⟨a', f'⟩ = x → f '' univ ⊆ f' '' univ :=
  by
  constructor
  ·
    intro h
    have : liftp (supp x) x := by
      rw [h] <;> intro u <;> exact id
    rw [liftp_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine' ⟨a, f, xeq.symm, _⟩
    intro a' f' h''
    rintro u ⟨i, _, hfi⟩
    have : u ∈ supp x := by
      rw [← hfi] <;> apply h'
    exact (mem_supp x u).mp this _ _ h''
  rintro ⟨a, f, xeq, h⟩ p
  rw [liftp_iff]
  constructor
  ·
    rintro ⟨a', f', xeq', h'⟩ u usuppx
    rcases(mem_supp x u).mp usuppx a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]
    apply h'
  intro h'
  refine' ⟨a, f, xeq.symm, _⟩
  intro i
  apply h'
  rw [mem_supp]
  intro a' f' xeq'
  apply h a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)

variable (q)

/--  A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def is_uniform : Prop :=
  ∀ ⦃α : Type u⦄ a a' : q.P.A f : q.P.B a → α f' : q.P.B a' → α, abs ⟨a, f⟩ = abs ⟨a', f'⟩ → f '' univ = f' '' univ

/--  does `abs` preserve `liftp`? -/
def liftp_preservation : Prop :=
  ∀ ⦃α⦄ p : α → Prop x : q.P.obj α, liftp p (abs x) ↔ liftp p x

/--  does `abs` preserve `supp`? -/
def supp_preservation : Prop :=
  ∀ ⦃α⦄ x : q.P.obj α, supp (abs x) = supp x

variable (q)

theorem supp_eq_of_is_uniform (h : q.is_uniform) {α : Type u} (a : q.P.A) (f : q.P.B a → α) :
    supp (abs ⟨a, f⟩) = f '' univ := by
  ext u
  rw [mem_supp]
  constructor
  ·
    intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]
  apply h'

theorem liftp_iff_of_is_uniform (h : q.is_uniform) {α : Type u} (x : F α) (p : α → Prop) :
    liftp p x ↔ ∀, ∀ u ∈ supp x, ∀, p u := by
  rw [liftp_iff, ← abs_repr x]
  cases' reprₓ x with a f
  constructor
  ·
    rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_is_uniform h, h _ _ _ _ abseq]
    rintro ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine' ⟨a, f, rfl, fun i => h' _ _⟩
  rw [supp_eq_of_is_uniform h]
  exact ⟨i, mem_univ i, rfl⟩

theorem supp_map (h : q.is_uniform) {α β : Type u} (g : α → β) (x : F α) : supp (g <$> x) = g '' supp x := by
  rw [← abs_repr x]
  cases' reprₓ x with a f
  rw [← abs_map, Pfunctor.map_eq]
  rw [supp_eq_of_is_uniform h, supp_eq_of_is_uniform h, image_comp]

theorem supp_preservation_iff_uniform : q.supp_preservation ↔ q.is_uniform := by
  constructor
  ·
    intro h α a a' f f' h'
    rw [← Pfunctor.supp_eq, ← Pfunctor.supp_eq, ← h, h', h]
  ·
    rintro h α ⟨a, f⟩
    rwa [supp_eq_of_is_uniform, Pfunctor.supp_eq]

theorem supp_preservation_iff_liftp_preservation : q.supp_preservation ↔ q.liftp_preservation := by
  constructor <;> intro h
  ·
    rintro α p ⟨a, f⟩
    have h' := h
    rw [supp_preservation_iff_uniform] at h'
    dsimp only [supp_preservation, supp]  at h
    rwa [liftp_iff_of_is_uniform, supp_eq_of_is_uniform, Pfunctor.liftp_iff'] <;>
      try
        assumption
    ·
      simp only [image_univ, mem_range, exists_imp_distrib]
      constructor <;> intros <;> subst_vars <;> solve_by_elim
  ·
    rintro α ⟨a, f⟩
    simp only [liftp_preservation] at h
    simp only [supp, h]

theorem liftp_preservation_iff_uniform : q.liftp_preservation ↔ q.is_uniform := by
  rw [← supp_preservation_iff_liftp_preservation, supp_preservation_iff_uniform]

end Qpf

