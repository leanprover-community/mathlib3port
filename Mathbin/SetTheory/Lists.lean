import Mathbin.Data.List.Basic

/-!
# A computable model of ZFA without infinity

In this file we define finite hereditary lists. This is useful for calculations in naive set theory.

We distinguish two kinds of ZFA lists:
* Atoms. Directly correspond to an element of the original type.
* Proper ZFA lists. Can thought of (but aren't implemented) as a list of ZFA lists (not necessarily
  proper).

For example, `lists ℕ` contains stuff like `23`, `[]`, `[37]`, `[1, [[2], 3], 4]`.

## Implementation note

As we want to be able to append both atoms and proper ZFA lists to proper ZFA lists, it's handy that
atoms and proper ZFA lists belong to the same type, even though atoms of `α` could be modelled as
`α` directly. But we don't want to be able to append anything to atoms.

This calls for a two-steps definition of ZFA lists:
* First, define ZFA prelists as atoms and proper ZFA prelists. Those proper ZFA prelists are defined
  by inductive appending of (not necessarily proper) ZFA lists.
* Second, define ZFA lists by rubbing out the distinction between atoms and proper lists.

## Main declarations

* `lists' α ff`: Atoms as ZFA prelists. Basically a copy of `α`.
* `lists' α tt`: Proper ZFA prelists. Defined inductively from the empty ZFA prelist (`lists'.nil`)
  and from appending a ZFA prelist to a proper ZFA prelist (`lists'.cons a l`).
* `lists α`: ZFA lists. Sum of the atoms and proper ZFA prelists.

## TODO

The next step is to define ZFA sets as lists quotiented by `lists.equiv`.
(-/


variable {α : Type _}

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler decidable_eq
/--  Prelists, helper type to define `lists`. `lists' α ff` are the "atoms", a copy of `α`.
`lists' α tt` are the "proper" ZFA prelists, inductively defined from the empty ZFA prelist and from
appending a ZFA prelist to a proper ZFA prelist. It is made so that you can't append anything to an
atom while having only one appending function for appending both atoms and proper ZFC prelists to a
proper ZFA prelist. -/
inductive Lists'.{u} (α : Type u) : Bool → Type u
  | atom : α → Lists' ff
  | nil : Lists' tt
  | cons' {b} : Lists' b → Lists' tt → Lists' tt
  deriving [anonymous]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Hereditarily finite list, aka ZFA list. A ZFA list is either an \"atom\" (`b = ff`), corresponding\nto an element of `α`, or a \"proper\" ZFA list, inductively defined from the empty ZFA list and from\nappending a ZFA list to a proper ZFA list. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `Lists [])
  (Command.optDeclSig [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [(Level.hole "_")])] [] ")")] [])
  (Command.declValSimple
   ":="
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
    ", "
    (Term.app `Lists' [`α `b]))
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
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
   ", "
   (Term.app `Lists' [`α `b]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Lists' [`α `b])
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
  `Lists'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
    Hereditarily finite list, aka ZFA list. A ZFA list is either an "atom" (`b = ff`), corresponding
    to an element of `α`, or a "proper" ZFA list, inductively defined from the empty ZFA list and from
    appending a ZFA list to a proper ZFA list. -/
  def Lists ( α : Type _ ) := Σ b , Lists' α b

namespace Lists'

instance [Inhabited α] : ∀ b, Inhabited (Lists' α b)
  | tt => ⟨nil⟩
  | ff => ⟨atom (default _)⟩

/--  Appending a ZFA list to a proper ZFA prelist. -/
def cons : Lists α → Lists' α tt → Lists' α tt
  | ⟨b, a⟩, l => cons' a l

/--  Converts a ZFA prelist to a `list` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def to_list : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom a => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.to_list

@[simp]
theorem to_list_cons (a : Lists α) l : to_list (cons a l) = a :: l.to_list := by
  cases a <;> simp [cons]

/--  Converts a `list` of ZFA lists to a proper ZFA prelist. -/
@[simp]
def of_list : List (Lists α) → Lists' α tt
  | [] => nil
  | a :: l => cons a (of_list l)

@[simp]
theorem to_of_list (l : List (Lists α)) : to_list (of_list l) = l := by
  induction l <;> simp

@[simp]
theorem of_to_list : ∀ l : Lists' α tt, of_list (to_list l) = l :=
  suffices
    ∀ b h : tt = b l : Lists' α b,
      let l' : Lists' α tt := by
        rw [h] <;> exact l
      of_list (to_list l') = l' from
    this _ rfl
  fun b h l => by
  induction l
  ·
    cases h
  ·
    exact rfl
  case lists'.cons' b a l IH₁ IH₂ =>
    intro
    change l' with cons' a l
    simpa [cons] using IH₂ rfl

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl l : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α tt} : Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩
  inductive Lists'.Subset : Lists' α tt → Lists' α tt → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' → a' ∈ Lists'.toList l' → Lists'.Subset l l' → Lists'.Subset (Lists'.cons a l) l'
end

local infixl:50 " ~ " => Lists.Equiv

/--  Equivalence of ZFA lists. Defined inductively. -/
add_decl_doc Lists.Equiv

/--  Subset relation for ZFA lists. Defined inductively. -/
add_decl_doc Lists'.Subset

namespace Lists'

instance : HasSubset (Lists' α tt) :=
  ⟨Lists'.Subset⟩

/--  ZFA prelist membership. A ZFA list is in a ZFA prelist if some element of this ZFA prelist is
equivalent as a ZFA list to this ZFA list. -/
instance {b} : HasMem (Lists α) (Lists' α b) :=
  ⟨fun a l => ∃ a' ∈ l.to_list, a ~ a'⟩

theorem mem_def {b a} {l : Lists' α b} : a ∈ l ↔ ∃ a' ∈ l.to_list, a ~ a' :=
  Iff.rfl

@[simp]
theorem mem_cons {a y l} : a ∈ @cons α y l ↔ a ~ y ∨ a ∈ l := by
  simp [mem_def, or_and_distrib_right, exists_or_distrib]

theorem cons_subset {a} {l₁ l₂ : Lists' α tt} : Lists'.cons a l₁ ⊆ l₂ ↔ a ∈ l₂ ∧ l₁ ⊆ l₂ := by
  refine' ⟨fun h => _, fun ⟨⟨a', m, e⟩, s⟩ => subset.cons e m s⟩
  generalize h' : Lists'.cons a l₁ = l₁'  at h
  cases' h with l a' a'' l l' e m s
  ·
    cases a
    cases h'
  cases a
  cases a'
  cases h'
  exact ⟨⟨_, m, e⟩, s⟩

theorem of_list_subset {l₁ l₂ : List (Lists α)} (h : l₁ ⊆ l₂) : Lists'.ofList l₁ ⊆ Lists'.ofList l₂ := by
  induction l₁
  ·
    exact subset.nil
  refine' subset.cons (Lists.Equiv.refl _) _ (l₁_ih (List.subset_of_cons_subsetₓ h))
  simp at h
  simp [h]

@[refl]
theorem subset.refl {l : Lists' α tt} : l ⊆ l := by
  rw [← Lists'.of_to_list l] <;> exact of_list_subset (List.Subset.refl _)

theorem subset_nil {l : Lists' α tt} : l ⊆ Lists'.nil → l = Lists'.nil := by
  rw [← of_to_list l]
  induction to_list l <;> intro h
  ·
    rfl
  rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩

theorem mem_of_subset' {a} {l₁ l₂ : Lists' α tt} (s : l₁ ⊆ l₂) (h : a ∈ l₁.to_list) : a ∈ l₂ := by
  induction' s with _ a a' l l' e m s IH
  ·
    cases h
  simp at h
  rcases h with (rfl | h)
  exacts[⟨_, m, e⟩, IH h]

theorem subset_def {l₁ l₂ : Lists' α tt} : l₁ ⊆ l₂ ↔ ∀, ∀ a ∈ l₁.to_list, ∀, a ∈ l₂ :=
  ⟨fun H a => mem_of_subset' H, fun H => by
    rw [← of_to_list l₁]
    revert H
    induction to_list l₁ <;> intro
    ·
      exact subset.nil
    ·
      simp at H
      exact cons_subset.2 ⟨H.1, ih H.2⟩⟩

end Lists'

namespace Lists

/--  Sends `a : α` to the corresponding atom in `lists α`. -/
@[matchPattern]
def atom (a : α) : Lists α :=
  ⟨_, Lists'.atom a⟩

/--  Converts a proper ZFA prelist to a ZFA list. -/
@[matchPattern]
def of' (l : Lists' α tt) : Lists α :=
  ⟨_, l⟩

/--  Converts a ZFA list to a `list` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def to_list : Lists α → List (Lists α)
  | ⟨b, l⟩ => l.to_list

/--  Predicate stating that a ZFA list is proper. -/
def is_list (l : Lists α) : Prop :=
  l.1

/--  Converts a `list` of ZFA lists to a ZFA list. -/
def of_list (l : List (Lists α)) : Lists α :=
  of' (Lists'.ofList l)

theorem is_list_to_list (l : List (Lists α)) : is_list (of_list l) :=
  Eq.refl _

theorem to_of_list (l : List (Lists α)) : to_list (of_list l) = l := by
  simp [of_list, of']

theorem of_to_list : ∀ {l : Lists α}, is_list l → of_list (to_list l) = l
  | ⟨tt, l⟩, _ => by
    simp [of_list, of']

instance : Inhabited (Lists α) :=
  ⟨of' Lists'.nil⟩

instance [DecidableEq α] : DecidableEq (Lists α) := by
  unfold Lists <;> infer_instance

instance [SizeOf α] : SizeOf (Lists α) := by
  unfold Lists <;> infer_instance

/--  A recursion principle for pairs of ZFA lists and proper ZFA prelists. -/
def induction_mut (C : Lists α → Sort _) (D : Lists' α tt → Sort _) (C0 : ∀ a, C (atom a)) (C1 : ∀ l, D l → C (of' l))
    (D0 : D Lists'.nil) (D1 : ∀ a l, C a → D l → D (Lists'.cons a l)) : PProd (∀ l, C l) (∀ l, D l) := by
  suffices
    ∀ {b} l : Lists' α b,
      PProd (C ⟨_, l⟩)
        (match b, l with
        | tt, l => D l
        | ff, l => PUnit)by
    exact ⟨fun ⟨b, l⟩ => (this _).1, fun l => (this l).2⟩
  intros
  induction' l with a b a l IH₁ IH₂
  ·
    exact ⟨C0 _, ⟨⟩⟩
  ·
    exact ⟨C1 _ D0, D0⟩
  ·
    suffices
    ·
      exact ⟨C1 _ this, this⟩
    exact D1 ⟨_, _⟩ _ IH₁.1 IH₂.2

/--  Membership of ZFA list. A ZFA list belongs to a proper ZFA list if it belongs to the latter as a
proper ZFA prelist. An atom has no members. -/
def mem (a : Lists α) : Lists α → Prop
  | ⟨ff, l⟩ => False
  | ⟨tt, l⟩ => a ∈ l

instance : HasMem (Lists α) (Lists α) :=
  ⟨mem⟩

theorem is_list_of_mem {a : Lists α} : ∀ {l : Lists α}, a ∈ l → is_list l
  | ⟨_, Lists'.nil⟩, _ => rfl
  | ⟨_, Lists'.cons' _ _⟩, _ => rfl

theorem equiv.antisymm_iff {l₁ l₂ : Lists' α tt} : of' l₁ ~ of' l₂ ↔ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁ := by
  refine' ⟨fun h => _, fun ⟨h₁, h₂⟩ => equiv.antisymm h₁ h₂⟩
  cases' h with _ _ _ h₁ h₂
  ·
    simp [Lists'.Subset.refl]
  ·
    exact ⟨h₁, h₂⟩

attribute [refl] Equivₓ.refl

theorem equiv_atom {a} {l : Lists α} : atom a ~ l ↔ atom a = l :=
  ⟨fun h => by
    cases h <;> rfl, fun h => h ▸ Equivₓ.refl _⟩

theorem Equivₓ.symm {l₁ l₂ : Lists α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  cases' h with _ _ _ h₁ h₂ <;> [rfl, exact equiv.antisymm h₂ h₁]

theorem Equivₓ.trans : ∀ {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ := by
  let trans := fun l₁ : Lists α => ∀ ⦃l₂ l₃⦄, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
  suffices PProd (∀ l₁, trans l₁) (∀ l : Lists' α tt, ∀ l' ∈ l.to_list, ∀, trans l')by
    exact this.1
  apply induction_mut
  ·
    intro a l₂ l₃ h₁ h₂
    rwa [← equiv_atom.1 h₁] at h₂
  ·
    intro l₁ IH l₂ l₃ h₁ h₂
    cases' h₁ with _ _ l₂
    ·
      exact h₂
    cases' h₂ with _ _ l₃
    ·
      exact h₁
    cases' equiv.antisymm_iff.1 h₁ with hl₁ hr₁
    cases' equiv.antisymm_iff.1 h₂ with hl₂ hr₂
    apply equiv.antisymm_iff.2 <;> constructor <;> apply Lists'.subset_def.2
    ·
      intro a₁ m₁
      rcases Lists'.mem_of_subset' hl₁ m₁ with ⟨a₂, m₂, e₁₂⟩
      rcases Lists'.mem_of_subset' hl₂ m₂ with ⟨a₃, m₃, e₂₃⟩
      exact ⟨a₃, m₃, IH _ m₁ e₁₂ e₂₃⟩
    ·
      intro a₃ m₃
      rcases Lists'.mem_of_subset' hr₂ m₃ with ⟨a₂, m₂, e₃₂⟩
      rcases Lists'.mem_of_subset' hr₁ m₂ with ⟨a₁, m₁, e₂₁⟩
      exact ⟨a₁, m₁, (IH _ m₁ e₂₁.symm e₃₂.symm).symm⟩
  ·
    rintro _ ⟨⟩
  ·
    intro a l IH₁ IH₂
    simpa [IH₁] using IH₂

instance : Setoidₓ (Lists α) :=
  ⟨· ~ ·, Equivₓ.refl, @Equivₓ.symm _, @Equivₓ.trans _⟩

section Decidable

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `equiv.decidable_meas [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (Term.arrow
      («term_$__»
       (Term.app
        `Psum
        [(Init.Data.Sigma.Basic.«termΣ'_,_»
          "Σ'"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l₁)] [":" (Term.app `Lists [`α])]))
          ", "
          (Term.app `Lists [`α]))])
       "$"
       (Term.app
        `Psum
        [(Init.Data.Sigma.Basic.«termΣ'_,_»
          "Σ'"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l₁)] [":" (Term.app `Lists' [`α `tt])]))
          ", "
          (Term.app `Lists' [`α `tt]))
         (Init.Data.Sigma.Basic.«termΣ'_,_»
          "Σ'"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Lists [`α])]))
          ", "
          (Term.app `Lists' [`α `tt]))]))
      "→"
      (termℕ "ℕ")))])
  (Command.declValEqns
   (Term.matchAltsWhereDecls
    (Term.matchAlts
     [(Term.matchAlt
       "|"
       [(Term.app `Psum.inl [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")])]
       "=>"
       (Init.Logic.«term_+_» (Term.app `sizeof [`l₁]) "+" (Term.app `sizeof [`l₂])))
      (Term.matchAlt
       "|"
       [(«term_$__» `Psum.inr "$" (Term.app `Psum.inl [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")]))]
       "=>"
       (Init.Logic.«term_+_» (Term.app `sizeof [`l₁]) "+" (Term.app `sizeof [`l₂])))
      (Term.matchAlt
       "|"
       [(«term_$__» `Psum.inr "$" (Term.app `Psum.inr [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")]))]
       "=>"
       (Init.Logic.«term_+_» (Term.app `sizeof [`l₁]) "+" (Term.app `sizeof [`l₂])))])
    []))
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAltsWhereDecls', expected 'Lean.Parser.Term.matchAltsWhereDecls.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Term.app `sizeof [`l₁]) "+" (Term.app `sizeof [`l₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sizeof [`l₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sizeof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `sizeof [`l₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sizeof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» `Psum.inr "$" (Term.app `Psum.inr [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Psum.inr [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Psum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `Psum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Term.app `sizeof [`l₁]) "+" (Term.app `sizeof [`l₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sizeof [`l₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sizeof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `sizeof [`l₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sizeof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» `Psum.inr "$" (Term.app `Psum.inl [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Psum.inl [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Psum.inl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `Psum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Term.app `sizeof [`l₁]) "+" (Term.app `sizeof [`l₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sizeof [`l₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sizeof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `sizeof [`l₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sizeof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Psum.inl [(Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`l₁ "," `l₂] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Psum.inl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.arrow
   («term_$__»
    (Term.app
     `Psum
     [(Init.Data.Sigma.Basic.«termΣ'_,_»
       "Σ'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l₁)] [":" (Term.app `Lists [`α])]))
       ", "
       (Term.app `Lists [`α]))])
    "$"
    (Term.app
     `Psum
     [(Init.Data.Sigma.Basic.«termΣ'_,_»
       "Σ'"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l₁)] [":" (Term.app `Lists' [`α `tt])]))
       ", "
       (Term.app `Lists' [`α `tt]))
      (Init.Data.Sigma.Basic.«termΣ'_,_»
       "Σ'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Lists [`α])]))
       ", "
       (Term.app `Lists' [`α `tt]))]))
   "→"
   (termℕ "ℕ"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  («term_$__»
   (Term.app
    `Psum
    [(Init.Data.Sigma.Basic.«termΣ'_,_»
      "Σ'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l₁)] [":" (Term.app `Lists [`α])]))
      ", "
      (Term.app `Lists [`α]))])
   "$"
   (Term.app
    `Psum
    [(Init.Data.Sigma.Basic.«termΣ'_,_»
      "Σ'"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l₁)] [":" (Term.app `Lists' [`α `tt])]))
      ", "
      (Term.app `Lists' [`α `tt]))
     (Init.Data.Sigma.Basic.«termΣ'_,_»
      "Σ'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Lists [`α])]))
      ", "
      (Term.app `Lists' [`α `tt]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Psum
   [(Init.Data.Sigma.Basic.«termΣ'_,_»
     "Σ'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l₁)] [":" (Term.app `Lists' [`α `tt])]))
     ", "
     (Term.app `Lists' [`α `tt]))
    (Init.Data.Sigma.Basic.«termΣ'_,_»
     "Σ'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Lists [`α])]))
     ", "
     (Term.app `Lists' [`α `tt]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Lists [`α])]))
   ", "
   (Term.app `Lists' [`α `tt]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Lists' [`α `tt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  `Lists'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
@[ simp ]
  def
    equiv.decidable_meas
    : Psum Σ' l₁ : Lists α , Lists α $ Psum Σ' l₁ : Lists' α tt , Lists' α tt Σ' a : Lists α , Lists' α tt → ℕ
    | Psum.inl ⟨ l₁ , l₂ ⟩ => sizeof l₁ + sizeof l₂
      | Psum.inr $ Psum.inl ⟨ l₁ , l₂ ⟩ => sizeof l₁ + sizeof l₂
      | Psum.inr $ Psum.inr ⟨ l₁ , l₂ ⟩ => sizeof l₁ + sizeof l₂

open WellFoundedTactics

theorem sizeof_pos {b} (l : Lists' α b) : 0 < sizeof l := by
  cases l <;>
    run_tac
      unfold_sizeof; trivial_nat_lt

theorem lt_sizeof_cons' {b} (a : Lists' α b) l : sizeof (⟨b, a⟩ : Lists α) < sizeof (Lists'.cons' a l) := by
  run_tac
    unfold_sizeof
  apply sizeof_pos

mutual
  @[instance]
  def equiv.decidable [DecidableEq α] : ∀ l₁ l₂ : Lists α, Decidable (l₁ ~ l₂)
    | ⟨ff, l₁⟩, ⟨ff, l₂⟩ =>
      decidableOfIff' (l₁ = l₂) $ by
        cases l₁ <;>
          refine'
            equiv_atom.trans
              (by
                simp [atom])
    | ⟨ff, l₁⟩, ⟨tt, l₂⟩ =>
      is_false $ by
        rintro ⟨⟩
    | ⟨tt, l₁⟩, ⟨ff, l₂⟩ =>
      is_false $ by
        rintro ⟨⟩
    | ⟨tt, l₁⟩, ⟨tt, l₂⟩ => by
      have :=
        have : (sizeof l₁+sizeof l₂) < sizeof (⟨tt, l₁⟩ : Lists α)+sizeof (⟨tt, l₂⟩ : Lists α) := by
          run_tac
            default_dec_tac
        subset.decidable l₁ l₂
      have :=
        have : (sizeof l₂+sizeof l₁) < sizeof (⟨tt, l₁⟩ : Lists α)+sizeof (⟨tt, l₂⟩ : Lists α) := by
          run_tac
            default_dec_tac
        subset.decidable l₂ l₁
      exact decidableOfIff' _ equiv.antisymm_iff
  @[instance]
  def subset.decidable [DecidableEq α] : ∀ l₁ l₂ : Lists' α tt, Decidable (l₁ ⊆ l₂)
    | Lists'.nil, l₂ => is_true subset.nil
    | @Lists'.cons' _ b a l₁, l₂ => by
      have :=
        have : (sizeof (⟨b, a⟩ : Lists α)+sizeof l₂) < sizeof (Lists'.cons' a l₁)+sizeof l₂ :=
          add_lt_add_right (lt_sizeof_cons' _ _) _
        mem.decidable ⟨b, a⟩ l₂
      have :=
        have : (sizeof l₁+sizeof l₂) < sizeof (Lists'.cons' a l₁)+sizeof l₂ := by
          run_tac
            default_dec_tac
        subset.decidable l₁ l₂
      exact decidableOfIff' _ (@Lists'.cons_subset _ ⟨_, _⟩ _ _)
  @[instance]
  def mem.decidable [DecidableEq α] : ∀ a : Lists α l : Lists' α tt, Decidable (a ∈ l)
    | a, Lists'.nil =>
      is_false $ by
        rintro ⟨_, ⟨⟩, _⟩
    | a, Lists'.cons' b l₂ => by
      have :=
        have : (sizeof a+sizeof (⟨_, b⟩ : Lists α)) < sizeof a+sizeof (Lists'.cons' b l₂) :=
          add_lt_add_left (lt_sizeof_cons' _ _) _
        equiv.decidable a ⟨_, b⟩
      have :=
        have : (sizeof a+sizeof l₂) < sizeof a+sizeof (Lists'.cons' b l₂) := by
          run_tac
            default_dec_tac
        mem.decidable a l₂
      refine' decidableOfIff' (a ~ ⟨_, b⟩ ∨ a ∈ l₂) _
      rw [← Lists'.mem_cons]
      rfl
end

end Decidable

end Lists

namespace Lists'

theorem mem_equiv_left {l : Lists' α tt} : ∀ {a a'}, a ~ a' → (a ∈ l ↔ a' ∈ l) :=
  suffices ∀ {a a'}, a ~ a' → a ∈ l → a' ∈ l from fun a a' e => ⟨this e, this e.symm⟩
  fun a₁ a₂ e₁ ⟨a₃, m₃, e₂⟩ => ⟨_, m₃, e₁.symm.trans e₂⟩

theorem mem_of_subset {a} {l₁ l₂ : Lists' α tt} (s : l₁ ⊆ l₂) : a ∈ l₁ → a ∈ l₂
  | ⟨a', m, e⟩ => (mem_equiv_left e).2 (mem_of_subset' s m)

theorem subset.trans {l₁ l₂ l₃ : Lists' α tt} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  subset_def.2 $ fun a₁ m₁ => mem_of_subset h₂ $ mem_of_subset' h₁ m₁

end Lists'

def Finsets (α : Type _) :=
  Quotientₓ (@Lists.setoid α)

namespace Finsets

instance : HasEmptyc (Finsets α) :=
  ⟨⟦Lists.of' Lists'.nil⟧⟩

instance : Inhabited (Finsets α) :=
  ⟨∅⟩

instance [DecidableEq α] : DecidableEq (Finsets α) := by
  unfold Finsets <;> infer_instance

end Finsets

