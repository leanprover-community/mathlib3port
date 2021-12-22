import Mathbin.Data.Set.Basic

/-!

# Partial Equivalences

In this file, we define partial equivalences `pequiv`, which are a bijection between a subset of `α`
and a subset of `β`. Notationally, a `pequiv` is denoted by "`≃.`" (note that the full stop is part
of the notation). The way we store these internally is with two functions `f : α → option β` and
the reverse function `g : β → option α`, with the condition that if `f a` is `option.some b`,
then `g b` is `option.some a`.

## Main results

- `pequiv.of_set`: creates a `pequiv` from a set `s`,
  which sends an element to itself if it is in `s`.
- `pequiv.single`: given two elements `a : α` and `b : β`, create a `pequiv` that sends them to
  each other, and ignores all other elements.
- `pequiv.injective_of_forall_ne_is_some`/`injective_of_forall_is_some`: If the domain of a `pequiv`
  is all of `α` (except possibly one point), its `to_fun` is injective.

## Canonical order

`pequiv` is canonically ordered by inclusion; that is, if a function `f` defined on a subset `s`
is equal to `g` on that subset, but `g` is also defined on a larger set, then `f ≤ g`. We also have
a definition of `⊥`, which is the empty `pequiv` (sends all to `none`), which in the end gives us a
`semilattice_inf` with an `order_bot` instance.

## Tags

pequiv, partial equivalence

-/


universe u v w x

/--  A `pequiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `local_equiv` for a version that requires `to_fun` and
`inv_fun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
structure Pequiv (α : Type u) (β : Type v) where
  toFun : α → Option β
  invFun : β → Option α
  inv : ∀ a : α b : β, a ∈ inv_fun b ↔ b ∈ to_fun a

infixr:25 " ≃. " => Pequiv

namespace Pequiv

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Function Option

instance : CoeFun (α ≃. β) fun _ => α → Option β :=
  ⟨to_fun⟩

@[simp]
theorem coe_mk_apply (f₁ : α → Option β) (f₂ : β → Option α) h (x : α) : (Pequiv.mk f₁ f₂ h : α → Option β) x = f₁ x :=
  rfl

@[ext]
theorem ext : ∀ {f g : α ≃. β} h : ∀ x, f x = g x, f = g
  | ⟨f₁, f₂, hf⟩, ⟨g₁, g₂, hg⟩, h =>
    have h : f₁ = g₁ := funext h
    have : ∀ b, f₂ b = g₂ b := by
      subst h
      intro b
      have hf := fun a => hf a b
      have hg := fun a => hg a b
      cases' h : g₂ b with a
      ·
        simp only [h, Option.not_mem_none, false_iffₓ] at hg
        simp only [hg, iff_falseₓ] at hf
        rwa [Option.eq_none_iff_forall_not_mem]
      ·
        rw [← Option.mem_def, hf, ← hg, h, Option.mem_def]
    by
    simp [funext_iff]

theorem ext_iff {f g : α ≃. β} : f = g ↔ ∀ x, f x = g x :=
  ⟨congr_funₓ ∘ congr_argₓ _, ext⟩

/--  The identity map as a partial equivalence. -/
@[refl]
protected def refl (α : Type _) : α ≃. α :=
  { toFun := some, invFun := some, inv := fun _ _ => eq_comm }

/--  The inverse partial equivalence. -/
@[symm]
protected def symm (f : α ≃. β) : β ≃. α :=
  { toFun := f.2, invFun := f.1, inv := fun _ _ => (f.inv _ _).symm }

theorem mem_iff_mem (f : α ≃. β) : ∀ {a : α} {b : β}, a ∈ f.symm b ↔ b ∈ f a :=
  f.3

theorem eq_some_iff (f : α ≃. β) : ∀ {a : α} {b : β}, f.symm b = some a ↔ f a = some b :=
  f.3

/--  Composition of partial equivalences `f : α ≃. β` and `g : β ≃. γ`. -/
@[trans]
protected def trans (f : α ≃. β) (g : β ≃. γ) : α ≃. γ :=
  { toFun := fun a => (f a).bind g, invFun := fun a => (g.symm a).bind f.symm,
    inv := fun a b => by
      simp_all [And.comm, eq_some_iff f, eq_some_iff g] }

@[simp]
theorem refl_apply (a : α) : Pequiv.refl α a = some a :=
  rfl

@[simp]
theorem symm_refl : (Pequiv.refl α).symm = Pequiv.refl α :=
  rfl

@[simp]
theorem symm_symm (f : α ≃. β) : f.symm.symm = f := by
  cases f <;> rfl

theorem symm_injective : Function.Injective (@Pequiv.symm α β) :=
  left_inverse.injective symm_symm

theorem trans_assoc (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) : (f.trans g).trans h = f.trans (g.trans h) :=
  ext fun _ => Option.bind_assoc _ _ _

theorem mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) : c ∈ f.trans g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b :=
  Option.bind_eq_some'

theorem trans_eq_some (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    f.trans g a = some c ↔ ∃ b, f a = some b ∧ g b = some c :=
  Option.bind_eq_some'

theorem trans_eq_none (f : α ≃. β) (g : β ≃. γ) (a : α) : f.trans g a = none ↔ ∀ b c, b ∉ f a ∨ c ∉ g b := by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  push_neg
  tauto

@[simp]
theorem refl_trans (f : α ≃. β) : (Pequiv.refl α).trans f = f := by
  ext <;> dsimp [Pequiv.trans] <;> rfl

@[simp]
theorem trans_refl (f : α ≃. β) : f.trans (Pequiv.refl β) = f := by
  ext <;> dsimp [Pequiv.trans] <;> simp

protected theorem inj (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) : a₁ = a₂ := by
  rw [← mem_iff_mem] at * <;> cases h : f.symm b <;> simp_all

/--  If the domain of a `pequiv` is `α` except a point, its forward direction is injective. -/
theorem injective_of_forall_ne_is_some (f : α ≃. β) (a₂ : α) (h : ∀ a₁ : α, a₁ ≠ a₂ → is_some (f a₁)) : injective f :=
  has_left_inverse.injective
    ⟨fun b => Option.recOn b a₂ fun b' => Option.recOn (f.symm b') a₂ id, fun x => by
      classical
      cases hfx : f x
      ·
        have : x = a₂
        exact
          not_imp_comm.1 (h x)
            (hfx.symm ▸ by
              simp )
        simp [this]
      ·
        simp only [hfx]
        rw [(eq_some_iff f).2 hfx]
        rfl⟩

/--  If the domain of a `pequiv` is all of `α`, its forward direction is injective. -/
theorem injective_of_forall_is_some {f : α ≃. β} (h : ∀ a : α, is_some (f a)) : injective f :=
  (Classical.em (Nonempty α)).elim (fun hn => injective_of_forall_ne_is_some f (Classical.choice hn) fun a _ => h a)
    fun hn x => (hn ⟨x⟩).elim

section OfSet

variable (s : Set α) [DecidablePred (· ∈ s)]

/--  Creates a `pequiv` that is the identity on `s`, and `none` outside of it. -/
def of_set (s : Set α) [DecidablePred (· ∈ s)] : α ≃. α :=
  { toFun := fun a => if a ∈ s then some a else none, invFun := fun a => if a ∈ s then some a else none,
    inv := fun a b => by
      split_ifs with hb ha ha
      ·
        simp [eq_comm]
      ·
        simp [ne_of_mem_of_not_mem hb ha]
      ·
        simp [ne_of_mem_of_not_mem ha hb]
      ·
        simp }

theorem mem_of_set_self_iff {s : Set α} [DecidablePred (· ∈ s)] {a : α} : a ∈ of_set s a ↔ a ∈ s := by
  dsimp [of_set] <;> split_ifs <;> simp

theorem mem_of_set_iff {s : Set α} [DecidablePred (· ∈ s)] {a b : α} : a ∈ of_set s b ↔ a = b ∧ a ∈ s := by
  dsimp [of_set]
  split_ifs
  ·
    simp only [iff_self_and, Option.mem_def, eq_comm]
    rintro rfl
    exact h
  ·
    simp only [false_iffₓ, not_and, Option.not_mem_none]
    rintro rfl
    exact h

@[simp]
theorem of_set_eq_some_iff {s : Set α} {h : DecidablePred (· ∈ s)} {a b : α} : of_set s b = some a ↔ a = b ∧ a ∈ s :=
  mem_of_set_iff

@[simp]
theorem of_set_eq_some_self_iff {s : Set α} {h : DecidablePred (· ∈ s)} {a : α} : of_set s a = some a ↔ a ∈ s :=
  mem_of_set_self_iff

@[simp]
theorem of_set_symm : (of_set s).symm = of_set s :=
  rfl

@[simp]
theorem of_set_univ : of_set Set.Univ = Pequiv.refl α :=
  rfl

@[simp]
theorem of_set_eq_refl {s : Set α} [DecidablePred (· ∈ s)] : of_set s = Pequiv.refl α ↔ s = Set.Univ :=
  ⟨fun h => by
    rw [Set.eq_univ_iff_forall]
    intro
    rw [← mem_of_set_self_iff, h]
    exact rfl, fun h => by
    simp only [of_set_univ.symm, h] <;> congr⟩

end OfSet

theorem symm_trans_rev (f : α ≃. β) (g : β ≃. γ) : (f.trans g).symm = g.symm.trans f.symm :=
  rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `self_trans_symm [])
  (Command.declSig
   [(Term.explicitBinder "(" [`f] [":" (Data.Pequiv.«term_≃._» `α " ≃. " `β)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `f.trans [`f.symm])
     "="
     (Term.app `of_set [(Set.«term{_|_}» "{" `a "|" (Term.proj (Term.app `f [`a]) "." `isSome) "}")]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [] []) [])
       (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Pequiv.trans)] "]"] [] []) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] (Term.app `eq_some_iff [`f]))
           ","
           (Tactic.simpLemma [] [] `Option.is_some_iff_exists)
           ","
           (Tactic.simpLemma [] [] `Option.mem_def)
           ","
           (Tactic.simpLemma [] [] `bind_eq_some')
           ","
           (Tactic.simpLemma [] [] `of_set_eq_some_iff)]
          "]"]
         [])
        [])
       (group (Tactic.constructor "constructor") [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb₁)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb₂)]) [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor "⟨" [(Term.app `Pequiv.inj [(Term.hole "_") `hb₂ `hb₁]) "," `b "," `hb₂] "⟩"))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              ["("
               "config"
               ":="
               (Term.structInst
                "{"
                []
                [(group
                  (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                  [])]
                (Term.optEllipsis [])
                []
                "}")
               ")"]
              []
              []
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
     [(group (Tactic.ext "ext" [] []) [])
      (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Pequiv.trans)] "]"] [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] (Term.app `eq_some_iff [`f]))
          ","
          (Tactic.simpLemma [] [] `Option.is_some_iff_exists)
          ","
          (Tactic.simpLemma [] [] `Option.mem_def)
          ","
          (Tactic.simpLemma [] [] `bind_eq_some')
          ","
          (Tactic.simpLemma [] [] `of_set_eq_some_iff)]
         "]"]
        [])
       [])
      (group (Tactic.constructor "constructor") [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb₁)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb₂)]) [])]
                "⟩"))]
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor "⟨" [(Term.app `Pequiv.inj [(Term.hole "_") `hb₂ `hb₁]) "," `b "," `hb₂] "⟩"))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             []
             []
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
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        []
        []
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
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   []
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
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
  self_trans_symm
  ( f : α ≃. β ) : f.trans f.symm = of_set { a | f a . isSome }
  :=
    by
      ext
        dsimp [ Pequiv.trans ]
        simp only [ eq_some_iff f , Option.is_some_iff_exists , Option.mem_def , bind_eq_some' , of_set_eq_some_iff ]
        constructor
        · rintro ⟨ b , hb₁ , hb₂ ⟩ exact ⟨ Pequiv.inj _ hb₂ hb₁ , b , hb₂ ⟩
        · simp ( config := { contextual := Bool.true._@._internal._hyg.0 } )

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `symm_trans_self [])
  (Command.declSig
   [(Term.explicitBinder "(" [`f] [":" (Data.Pequiv.«term_≃._» `α " ≃. " `β)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `f.symm.trans [`f])
     "="
     (Term.app `of_set [(Set.«term{_|_}» "{" `b "|" (Term.proj (Term.app `f.symm [`b]) "." `isSome) "}")]))))
  (Command.declValSimple
   ":="
   («term_$__»
    `symm_injective
    "$"
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
           [(Tactic.simpLemma [] [] `symm_trans_rev)
            ","
            (Tactic.simpLemma [] [] `self_trans_symm)
            ","
            (Tactic.simpErase "-" `symm_symm)]
           "]"]
          [])
         [])]))))
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
   `symm_injective
   "$"
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
          [(Tactic.simpLemma [] [] `symm_trans_rev)
           ","
           (Tactic.simpLemma [] [] `self_trans_symm)
           ","
           (Tactic.simpErase "-" `symm_symm)]
          "]"]
         [])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
         [(Tactic.simpLemma [] [] `symm_trans_rev)
          ","
          (Tactic.simpLemma [] [] `self_trans_symm)
          ","
          (Tactic.simpErase "-" `symm_symm)]
         "]"]
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
   []
   ["["
    [(Tactic.simpLemma [] [] `symm_trans_rev)
     ","
     (Tactic.simpLemma [] [] `self_trans_symm)
     ","
     (Tactic.simpErase "-" `symm_symm)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `symm_symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `self_trans_symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `symm_trans_rev
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `symm_injective
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `f.symm.trans [`f])
   "="
   (Term.app `of_set [(Set.«term{_|_}» "{" `b "|" (Term.proj (Term.app `f.symm [`b]) "." `isSome) "}")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `of_set [(Set.«term{_|_}» "{" `b "|" (Term.proj (Term.app `f.symm [`b]) "." `isSome) "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `b "|" (Term.proj (Term.app `f.symm [`b]) "." `isSome) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f.symm [`b]) "." `isSome)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f.symm [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f.symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f.symm [`b]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  symm_trans_self
  ( f : α ≃. β ) : f.symm.trans f = of_set { b | f.symm b . isSome }
  := symm_injective $ by simp [ symm_trans_rev , self_trans_symm , - symm_symm ]

theorem trans_symm_eq_iff_forall_is_some {f : α ≃. β} : f.trans f.symm = Pequiv.refl α ↔ ∀ a, is_some (f a) := by
  rw [self_trans_symm, of_set_eq_refl, Set.eq_univ_iff_forall] <;> rfl

instance : HasBot (α ≃. β) :=
  ⟨{ toFun := fun _ => none, invFun := fun _ => none,
      inv := by
        simp }⟩

instance : Inhabited (α ≃. β) :=
  ⟨⊥⟩

@[simp]
theorem bot_apply (a : α) : (⊥ : α ≃. β) a = none :=
  rfl

@[simp]
theorem symm_bot : (⊥ : α ≃. β).symm = ⊥ :=
  rfl

@[simp]
theorem trans_bot (f : α ≃. β) : f.trans (⊥ : β ≃. γ) = ⊥ := by
  ext <;> dsimp [Pequiv.trans] <;> simp

@[simp]
theorem bot_trans (f : β ≃. γ) : (⊥ : α ≃. β).trans f = ⊥ := by
  ext <;> dsimp [Pequiv.trans] <;> simp

theorem is_some_symm_get (f : α ≃. β) {a : α} (h : is_some (f a)) : is_some (f.symm (Option.getₓ h)) :=
  is_some_iff_exists.2
    ⟨a, by
      rw [f.eq_some_iff, some_get]⟩

section Single

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/--  Create a `pequiv` which sends `a` to `b` and `b` to `a`, but is otherwise `none`. -/
def single (a : α) (b : β) : α ≃. β :=
  { toFun := fun x => if x = a then some b else none, invFun := fun x => if x = b then some a else none,
    inv := fun _ _ => by
      simp <;> split_ifs <;> cc }

theorem mem_single (a : α) (b : β) : b ∈ single a b a :=
  if_pos rfl

theorem mem_single_iff (a₁ a₂ : α) (b₁ b₂ : β) : b₁ ∈ single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  dsimp [single] <;> split_ifs <;> simp [eq_comm]

@[simp]
theorem symm_single (a : α) (b : β) : (single a b).symm = single b a :=
  rfl

@[simp]
theorem single_apply (a : α) (b : β) : single a b a = some b :=
  if_pos rfl

theorem single_apply_of_ne {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) : single a₁ b a₂ = none :=
  if_neg h.symm

theorem single_trans_of_mem (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c ∈ f b) : (single a b).trans f = single a c := by
  ext
  dsimp [single, Pequiv.trans]
  split_ifs <;> simp_all

theorem trans_single_of_mem {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b ∈ f a) : f.trans (single b c) = single a c :=
  symm_injective $ single_trans_of_mem _ ((mem_iff_mem f).2 h)

@[simp]
theorem single_trans_single (a : α) (b : β) (c : γ) : (single a b).trans (single b c) = single a c :=
  single_trans_of_mem _ (mem_single _ _)

@[simp]
theorem single_subsingleton_eq_refl [Subsingleton α] (a b : α) : single a b = Pequiv.refl α := by
  ext i j
  dsimp [single]
  rw [if_pos (Subsingleton.elimₓ i a), Subsingleton.elimₓ i j, Subsingleton.elimₓ b j]

theorem trans_single_of_eq_none {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none) : f.trans (single b c) = ⊥ := by
  ext
  simp only [eq_none_iff_forall_not_mem, Option.mem_def, f.eq_some_iff] at h
  dsimp [Pequiv.trans, single]
  simp
  intros
  split_ifs <;> simp_all

theorem single_trans_of_eq_none (a : α) {b : β} {f : β ≃. δ} (h : f b = none) : (single a b).trans f = ⊥ :=
  symm_injective $ trans_single_of_eq_none _ h

theorem single_trans_single_of_ne {b₁ b₂ : β} (h : b₁ ≠ b₂) (a : α) (c : γ) : (single a b₁).trans (single b₂ c) = ⊥ :=
  single_trans_of_eq_none _ (single_apply_of_ne h.symm _)

end Single

section Order

-- failed to format: format: uncaught backtrack exception
instance
  : PartialOrderₓ ( α ≃. β )
  where
    le f g := ∀ a : α b : β , b ∈ f a → b ∈ g a
      le_refl _ _ _ := id
      le_trans f g h fg gh a b := gh a b ∘ fg a b
      le_antisymm
        f g fg gf
        :=
        ext
          (
            by
              intro a
                cases' h : g a with b
                · exact eq_none_iff_forall_not_mem . 2 fun b hb => Option.not_mem_none b $ h ▸ fg a b hb
                · exact gf _ _ h
            )

theorem le_def {f g : α ≃. β} : f ≤ g ↔ ∀ a : α b : β, b ∈ f a → b ∈ g a :=
  Iff.rfl

instance : OrderBot (α ≃. β) :=
  { Pequiv.hasBot with bot_le := fun _ _ _ h => (not_mem_none _ h).elim }

instance [DecidableEq α] [DecidableEq β] : SemilatticeInf (α ≃. β) :=
  { Pequiv.partialOrder with
    inf := fun f g =>
      { toFun := fun a => if f a = g a then f a else none,
        invFun := fun b => if f.symm b = g.symm b then f.symm b else none,
        inv := fun a b => by
          have := @mem_iff_mem _ _ f a b
          have := @mem_iff_mem _ _ g a b
          split_ifs <;> finish },
    inf_le_left := fun _ _ _ _ => by
      simp <;> split_ifs <;> cc,
    inf_le_right := fun _ _ _ _ => by
      simp <;> split_ifs <;> cc,
    le_inf := fun f g h fg gh a b => by
      have := fg a b
      have := gh a b
      simp [le_def]
      split_ifs <;> finish }

end Order

end Pequiv

namespace Equivₓ

variable {α : Type _} {β : Type _} {γ : Type _}

/--  Turns an `equiv` into a `pequiv` of the whole type. -/
def to_pequiv (f : α ≃ β) : α ≃. β :=
  { toFun := some ∘ f, invFun := some ∘ f.symm,
    inv := by
      simp [Equivₓ.eq_symm_apply, eq_comm] }

@[simp]
theorem to_pequiv_refl : (Equivₓ.refl α).toPequiv = Pequiv.refl α :=
  rfl

theorem to_pequiv_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).toPequiv = f.to_pequiv.trans g.to_pequiv :=
  rfl

theorem to_pequiv_symm (f : α ≃ β) : f.symm.to_pequiv = f.to_pequiv.symm :=
  rfl

theorem to_pequiv_apply (f : α ≃ β) (x : α) : f.to_pequiv x = some (f x) :=
  rfl

end Equivₓ

