import Mathbin.Control.Monad.Basic
import Mathbin.Data.Part
import Mathbin.Order.Hom.Lattice
import Mathbin.Tactic.Monotonicity.Default
import Mathbin.Tactic.Wlog

/-!
# Omega Complete Partial Orders

An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

The concept of an omega-complete partial order (ωCPO) is useful for the
formalization of the semantics of programming languages. Its notion of
supremum helps define the meaning of recursive procedures.

## Main definitions

 * class `omega_complete_partial_order`
 * `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `omega_complete_partial_order`

 * `part`
 * every `complete_lattice`
 * pi-types
 * product types
 * `monotone_hom`
 * `continuous_hom` (with notation →𝒄)
   * an instance of `omega_complete_partial_order (α →𝒄 β)`
 * `continuous_hom.of_fun`
 * `continuous_hom.of_mono`
 * continuous functions:
   * `id`
   * `ite`
   * `const`
   * `part.bind`
   * `part.map`
   * `part.seq`

## References

 * [Chain-complete posets and directed sets with applications][markowsky1976]
 * [Recursive definitions of partial functions and their computations][cadiou1972]
 * [Semantics of Programming Languages: Structures and Techniques][gunter1992]
-/


universe u v

attribute [-simp] Part.bind_eq_bind Part.map_eq_map

open_locale Classical

namespace OrderHom

variable (α : Type _) (β : Type _) {γ : Type _} {φ : Type _}

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] [Preorderₓ φ]

variable {β γ}

variable {α} {α' : Type _} {β' : Type _} [Preorderₓ α'] [Preorderₓ β']

/--  `part.bind` as a monotone function -/
@[simps]
def bind {β γ} (f : α →ₘ Part β) (g : α →ₘ β → Part γ) : α →ₘ Part γ :=
  { toFun := fun x => f x >>= g x,
    monotone' := by
      intro x y h a
      simp only [and_imp, exists_prop, Part.bind_eq_bind, Part.mem_bind_iff, exists_imp_distrib]
      intro b hb ha
      refine' ⟨b, f.monotone h _ hb, g.monotone h _ _ ha⟩ }

end OrderHom

namespace OmegaCompletePartialOrder

/--  A chain is a monotone sequence.

See the definition on page 114 of [gunter1992]. -/
def chain (α : Type u) [Preorderₓ α] :=
  ℕ →ₘ α

namespace Chain

variable {α : Type u} {β : Type v} {γ : Type _}

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ]

instance : CoeFun (chain α) fun _ => ℕ → α :=
  OrderHom.hasCoeToFun

instance [Inhabited α] : Inhabited (chain α) :=
  ⟨⟨fun _ => default _, fun _ _ _ => le_reflₓ _⟩⟩

instance : HasMem α (chain α) :=
  ⟨fun a c : ℕ →ₘ α => ∃ i, a = c i⟩

variable (c c' : chain α)

variable (f : α →ₘ β)

variable (g : β →ₘ γ)

-- failed to format: format: uncaught backtrack exception
instance : LE ( chain α ) where le x y := ∀ i , ∃ j , x i ≤ y j

/--  `map` function for `chain` -/
@[simps (config := { fullyApplied := ff })]
def map : chain β :=
  f.comp c

variable {f}

theorem mem_map (x : α) : x ∈ c → f x ∈ chain.map c f := fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩

theorem exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b := fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩

theorem mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
  ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    subst b
    apply mem_map c _ h⟩

@[simp]
theorem map_id : c.map OrderHom.id = c :=
  OrderHom.comp_id _

theorem map_comp : (c.map f).map g = c.map (g.comp f) :=
  rfl

@[mono]
theorem map_le_map {g : α →ₘ β} (h : f ≤ g) : c.map f ≤ c.map g := fun i => by
  simp [mem_map_iff] <;> intros <;> exists i <;> apply h

/--  `chain.zip` pairs up the elements of two chains that have the same index -/
@[simps]
def zip (c₀ : chain α) (c₁ : chain β) : chain (α × β) :=
  OrderHom.prod c₀ c₁

end Chain

end OmegaCompletePartialOrder

open OmegaCompletePartialOrder

section Prio

-- ././Mathport/Syntax/Translate/Basic.lean:169:9: warning: unsupported option extends_priority
set_option extends_priority 50

/--  An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

See the definition on page 114 of [gunter1992]. -/
class OmegaCompletePartialOrder (α : Type _) extends PartialOrderₓ α where
  ωSup : chain α → α
  le_ωSup : ∀ c : chain α, ∀ i, c i ≤ ωSup c
  ωSup_le : ∀ c : chain α x, (∀ i, c i ≤ x) → ωSup c ≤ x

end Prio

namespace OmegaCompletePartialOrder

variable {α : Type u} {β : Type v} {γ : Type _}

variable [OmegaCompletePartialOrder α]

/--  Transfer a `omega_complete_partial_order` on `β` to a `omega_complete_partial_order` on `α`
using a strictly monotone function `f : β →ₘ α`, a definition of ωSup and a proof that `f` is
continuous with regard to the provided `ωSup` and the ωCPO on `α`. -/
@[reducible]
protected def lift [PartialOrderₓ β] (f : β →ₘ α) (ωSup₀ : chain β → β) (h : ∀ x y, f x ≤ f y → x ≤ y)
    (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) : OmegaCompletePartialOrder β :=
  { ωSup := ωSup₀,
    ωSup_le := fun c x hx =>
      h _ _
        (by
          rw [h'] <;> apply ωSup_le <;> intro <;> apply f.monotone (hx i)),
    le_ωSup := fun c i =>
      h _ _
        (by
          rw [h'] <;> apply le_ωSup (c.map f)) }

theorem le_ωSup_of_le {c : chain α} {x : α} (i : ℕ) (h : x ≤ c i) : x ≤ ωSup c :=
  le_transₓ h (le_ωSup c _)

theorem ωSup_total {c : chain α} {x : α} (h : ∀ i, c i ≤ x ∨ x ≤ c i) : ωSup c ≤ x ∨ x ≤ ωSup c :=
  Classical.by_cases (fun this : ∀ i, c i ≤ x => Or.inl (ωSup_le _ _ this)) fun this : ¬∀ i, c i ≤ x =>
    have : ∃ i, ¬c i ≤ x := by
      simp only [not_forall] at this⊢ <;> assumption
    let ⟨i, hx⟩ := this
    have : x ≤ c i := (h i).resolve_left hx
    Or.inr $ le_ωSup_of_le _ this

@[mono]
theorem ωSup_le_ωSup_of_le {c₀ c₁ : chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
  ωSup_le _ _ $ fun i => Exists.rec_on (h i) $ fun j h => le_transₓ h (le_ωSup _ _)

theorem ωSup_le_iff (c : chain α) (x : α) : ωSup c ≤ x ↔ ∀ i, c i ≤ x := by
  constructor <;> intros
  ·
    trans ωSup c
    exact le_ωSup _ _
    assumption
  exact ωSup_le _ _ ‹_›

/--  A subset `p : α → Prop` of the type closed under `ωSup` induces an
`omega_complete_partial_order` on the subtype `{a : α // p a}`. -/
def Subtype {α : Type _} [OmegaCompletePartialOrder α] (p : α → Prop)
    (hp : ∀ c : chain α, (∀, ∀ i ∈ c, ∀, p i) → p (ωSup c)) : OmegaCompletePartialOrder (Subtype p) :=
  OmegaCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨ωSup _, hp (c.map (OrderHom.Subtype.val p)) fun i ⟨n, q⟩ => q.symm ▸ (c n).2⟩) (fun x y h => h) fun c =>
    rfl

section Continuity

open Chain

variable [OmegaCompletePartialOrder β]

variable [OmegaCompletePartialOrder γ]

/--  A monotone function `f : α →ₘ β` is continuous if it distributes over ωSup.

In order to distinguish it from the (more commonly used) continuity from topology
(see topology/basic.lean), the present definition is often referred to as
"Scott-continuity" (referring to Dana Scott). It corresponds to continuity
in Scott topological spaces (not defined here). -/
def continuous (f : α →ₘ β) : Prop :=
  ∀ c : chain α, f (ωSup c) = ωSup (c.map f)

/--  `continuous' f` asserts that `f` is both monotone and continuous. -/
def continuous' (f : α → β) : Prop :=
  ∃ hf : Monotone f, continuous ⟨f, hf⟩

theorem continuous'.to_monotone {f : α → β} (hf : continuous' f) : Monotone f :=
  hf.fst

theorem continuous.of_bundled (f : α → β) (hf : Monotone f) (hf' : continuous ⟨f, hf⟩) : continuous' f :=
  ⟨hf, hf'⟩

theorem continuous.of_bundled' (f : α →ₘ β) (hf' : continuous f) : continuous' f :=
  ⟨f.mono, hf'⟩

theorem continuous'.to_bundled (f : α → β) (hf : continuous' f) : continuous ⟨f, hf.to_monotone⟩ :=
  hf.snd

@[simp, norm_cast]
theorem continuous'_coe : ∀ {f : α →ₘ β}, continuous' f ↔ continuous f
  | ⟨f, hf⟩ => ⟨fun ⟨hf', hc⟩ => hc, fun hc => ⟨hf, hc⟩⟩

variable (f : α →ₘ β) (g : β →ₘ γ)

theorem continuous_id : continuous (@OrderHom.id α _) := by
  intro <;> rw [c.map_id] <;> rfl

theorem continuous_comp (hfc : continuous f) (hgc : continuous g) : continuous (g.comp f) := by
  dsimp [continuous]  at *
  intro
  rw [hfc, hgc, chain.map_comp]

theorem id_continuous' : continuous' (@id α) :=
  continuous_id.of_bundled' _

theorem continuous_const (x : β) : continuous (OrderHom.const α x) := fun c =>
  eq_of_forall_ge_iff $ fun z => by
    simp [ωSup_le_iff]

theorem const_continuous' (x : β) : continuous' (Function.const α x) :=
  continuous.of_bundled' (OrderHom.const α x) (continuous_const x)

end Continuity

end OmegaCompletePartialOrder

namespace Part

variable {α : Type u} {β : Type v} {γ : Type _}

open OmegaCompletePartialOrder

theorem eq_of_chain {c : chain (Part α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b := by
  cases' ha with i ha
  replace ha := ha.symm
  cases' hb with j hb
  replace hb := hb.symm
  wlog h : i ≤ j := le_totalₓ i j using a b i j, b a j i
  rw [eq_some_iff] at ha hb
  have := c.monotone h _ ha
  apply mem_unique this hb

/--  The (noncomputable) `ωSup` definition for the `ω`-CPO structure on `part α`. -/
protected noncomputable def ωSup (c : chain (Part α)) : Part α :=
  if h : ∃ a, some a ∈ c then some (Classical.some h) else none

theorem ωSup_eq_some {c : chain (Part α)} {a : α} (h : some a ∈ c) : Part.ωSup c = some a :=
  have : ∃ a, some a ∈ c := ⟨a, h⟩
  have a' : some (Classical.some this) ∈ c := Classical.some_spec this
  calc Part.ωSup c = some (Classical.some this) := dif_pos this
    _ = some a := congr_argₓ _ (eq_of_chain a' h)
    

theorem ωSup_eq_none {c : chain (Part α)} (h : ¬∃ a, some a ∈ c) : Part.ωSup c = none :=
  dif_neg h

theorem mem_chain_of_mem_ωSup {c : chain (Part α)} {a : α} (h : a ∈ Part.ωSup c) : some a ∈ c := by
  simp [Part.ωSup] at h
  split_ifs  at h
  ·
    have h' := Classical.some_spec h_1
    rw [← eq_some_iff] at h
    rw [← h]
    exact h'
  ·
    rcases h with ⟨⟨⟩⟩

-- failed to format: format: uncaught backtrack exception
noncomputable
  instance
    OmegaCompletePartialOrder
    : OmegaCompletePartialOrder ( Part α )
    where
      ωSup := Part.ωSup
        le_ωSup
          c i
          :=
          by intro x hx rw [ ← eq_some_iff ] at hx ⊢ rw [ ωSup_eq_some , ← hx ] rw [ ← hx ] exact ⟨ i , rfl ⟩
        ωSup_le
          :=
          by
            rintro c x hx a ha
              replace ha := mem_chain_of_mem_ωSup ha
              cases' ha with i ha
              apply hx i
              rw [ ← ha ]
              apply mem_some

section Inst

theorem mem_ωSup (x : α) (c : chain (Part α)) : x ∈ ωSup c ↔ some x ∈ c := by
  simp [OmegaCompletePartialOrder.ωSup, Part.ωSup]
  constructor
  ·
    split_ifs
    swap
    rintro ⟨⟨⟩⟩
    intro h'
    have hh := Classical.some_spec h
    simp at h'
    subst x
    exact hh
  ·
    intro h
    have h' : ∃ a : α, some a ∈ c := ⟨_, h⟩
    rw [dif_pos h']
    have hh := Classical.some_spec h'
    rw [eq_of_chain hh h]
    simp

end Inst

end Part

namespace Pi

variable {α : Type _} {β : α → Type _} {γ : Type _}

open OmegaCompletePartialOrder OmegaCompletePartialOrder.Chain

-- failed to format: format: uncaught backtrack exception
instance
  [ ∀ a , OmegaCompletePartialOrder ( β a ) ] : OmegaCompletePartialOrder ( ∀ a , β a )
  where
    ωSup c a := ωSup ( c.map ( Pi.evalOrderHom a ) )
      ωSup_le c f hf a := ωSup_le _ _ $ by rintro i apply hf
      le_ωSup c i x := le_ωSup_of_le _ $ le_reflₓ _

namespace OmegaCompletePartialOrder

variable [∀ x, OmegaCompletePartialOrder $ β x]

variable [OmegaCompletePartialOrder γ]

theorem flip₁_continuous' (f : ∀ x : α, γ → β x) (a : α) (hf : continuous' fun x y => f y x) : continuous' (f a) :=
  continuous.of_bundled _ (fun x y h => hf.to_monotone h a) fun c => congr_funₓ (hf.to_bundled _ c) a

theorem flip₂_continuous' (f : γ → ∀ x, β x) (hf : ∀ x, continuous' fun g => f g x) : continuous' f :=
  continuous.of_bundled _ (fun x y h a => (hf a).to_monotone h)
    (by
      intro c <;> ext a <;> apply (hf a).to_bundled _ c)

end OmegaCompletePartialOrder

end Pi

namespace Prod

open OmegaCompletePartialOrder

variable {α : Type _} {β : Type _} {γ : Type _}

variable [OmegaCompletePartialOrder α]

variable [OmegaCompletePartialOrder β]

variable [OmegaCompletePartialOrder γ]

/--  The supremum of a chain in the product `ω`-CPO. -/
@[simps]
protected def ωSup (c : chain (α × β)) : α × β :=
  (ωSup (c.map OrderHom.fst), ωSup (c.map OrderHom.snd))

-- failed to format: format: uncaught backtrack exception
@[ simps ωSup_fst ωSup_snd ]
  instance
    : OmegaCompletePartialOrder ( α × β )
    where
      ωSup := Prod.ωSup
        ωSup_le c ⟨ x , x' ⟩ h := ⟨ ωSup_le _ _ $ fun i => ( h i ) . 1 , ωSup_le _ _ $ fun i => ( h i ) . 2 ⟩
        le_ωSup c i := ⟨ le_ωSup ( c.map OrderHom.fst ) i , le_ωSup ( c.map OrderHom.snd ) i ⟩

end Prod

namespace CompleteLattice

variable (α : Type u)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Any complete lattice has an `ω`-CPO structure where the countable supremum is a special case\nof arbitrary suprema. -/")]
  []
  []
  []
  []
  [])
 (Command.instance
  (Term.attrKind [])
  "instance"
  [(Command.namedPrio "(" "priority" ":=" (numLit "100") ")")]
  []
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `CompleteLattice [`α]) "]")]
   (Term.typeSpec ":" (Term.app `OmegaCompletePartialOrder [`α])))
  (Command.whereStructInst
   "where"
   [(group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `ωSup
        [(Term.simpleBinder [(Term.simpleBinder [`c] [])] [])]
        []
        ":="
        (Order.CompleteLattice.«term⨆_,_»
         "⨆"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ", "
         (Term.app `c [`i])))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `ωSup_le
        [(Term.simpleBinder [(Term.anonymousCtor "⟨" [`c "," (Term.hole "_")] "⟩") (Term.simpleBinder [`s `hs] [])] [])]
        []
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic_<;>_»
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `supr_le_iff) "," (Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`hs] ["⊢"]))])
              "<;>"
              (Tactic.«tactic_<;>_» (Tactic.intro "intro" [`i]) "<;>" (Tactic.apply "apply" (Term.app `hs [`i]))))
             [])]))))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `le_ωSup
        [(Term.simpleBinder [(Term.anonymousCtor "⟨" [`c "," (Term.hole "_")] "⟩") (Term.simpleBinder [`i] [])] [])]
        []
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic_<;>_»
              (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"] [])
              "<;>"
              (Tactic.«tactic_<;>_»
               (Tactic.apply "apply" (Term.app `le_supr_of_le [`i]))
               "<;>"
               (Tactic.tacticRfl "rfl")))
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
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"] [])
        "<;>"
        (Tactic.«tactic_<;>_» (Tactic.apply "apply" (Term.app `le_supr_of_le [`i])) "<;>" (Tactic.tacticRfl "rfl")))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"] [])
   "<;>"
   (Tactic.«tactic_<;>_» (Tactic.apply "apply" (Term.app `le_supr_of_le [`i])) "<;>" (Tactic.tacticRfl "rfl")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.apply "apply" (Term.app `le_supr_of_le [`i])) "<;>" (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.apply "apply" (Term.app `le_supr_of_le [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_supr_of_le [`i])
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
  `le_supr_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `OrderHom.coe_fun_mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructField', expected 'Lean.Parser.Command.whereStructField.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `supr_le_iff) "," (Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hs] ["⊢"]))])
        "<;>"
        (Tactic.«tactic_<;>_» (Tactic.intro "intro" [`i]) "<;>" (Tactic.apply "apply" (Term.app `hs [`i]))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.simp
    "simp"
    []
    ["only"]
    ["[" [(Tactic.simpLemma [] [] `supr_le_iff) "," (Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"]
    [(Tactic.location "at" (Tactic.locationHyp [`hs] ["⊢"]))])
   "<;>"
   (Tactic.«tactic_<;>_» (Tactic.intro "intro" [`i]) "<;>" (Tactic.apply "apply" (Term.app `hs [`i]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.intro "intro" [`i]) "<;>" (Tactic.apply "apply" (Term.app `hs [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" (Term.app `hs [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hs [`i])
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
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `supr_le_iff) "," (Tactic.simpLemma [] [] `OrderHom.coe_fun_mk)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`hs] ["⊢"]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⊢»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `OrderHom.coe_fun_mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr_le_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructField', expected 'Lean.Parser.Command.whereStructField.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Term.app `c [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `c [`i])
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
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    Any complete lattice has an `ω`-CPO structure where the countable supremum is a special case
    of arbitrary suprema. -/
  instance
    ( priority := 100 )
    [ CompleteLattice α ] : OmegaCompletePartialOrder α
    where
      ωSup c := ⨆ i , c i
        ωSup_le ⟨ c , _ ⟩ s hs := by simp only [ supr_le_iff , OrderHom.coe_fun_mk ] at hs ⊢ <;> intro i <;> apply hs i
        le_ωSup ⟨ c , _ ⟩ i := by simp only [ OrderHom.coe_fun_mk ] <;> apply le_supr_of_le i <;> rfl

variable {α} {β : Type v} [OmegaCompletePartialOrder α] [CompleteLattice β]

open OmegaCompletePartialOrder

-- failed to format: format: uncaught backtrack exception
theorem
  inf_continuous
  [ IsTotal β ( · ≤ · ) ] ( f g : α →ₘ β ) ( hf : continuous f ) ( hg : continuous g ) : continuous ( f ⊓ g )
  :=
    by
      intro c
        apply eq_of_forall_ge_iff
        intro z
        simp
          only
          [
            inf_le_iff
              ,
              hf c
              ,
              hg c
              ,
              ωSup_le_iff
              ,
              ← forall_or_distrib_left
              ,
              ← forall_or_distrib_right
              ,
              Function.comp_app
              ,
              chain.map_coe
              ,
              OrderHom.has_inf_inf_coe
            ]
        constructor
        · introv h apply h
        ·
          intro h i j
            apply Or.imp _ _ ( h ( max i j ) ) <;> apply le_transₓ <;> mono * <;> try exact le_rfl
            · apply le_max_leftₓ
            · apply le_max_rightₓ

theorem Sup_continuous (s : Set $ α →ₘ β) (hs : ∀, ∀ f ∈ s, ∀, continuous f) : continuous (Sup s) := by
  intro c
  apply eq_of_forall_ge_iff
  intro z
  suffices (∀, ∀ f ∈ s, ∀ n, (f : _) (c n) ≤ z) ↔ ∀ n, ∀ f ∈ s, ∀, (f : _) (c n) ≤ z by
    simpa (config := { contextual := Bool.true.0 }) [ωSup_le_iff, hs _ _ _]
  exact ⟨fun H n f hf => H f hf n, fun H f hf n => H n f hf⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `supr_continuous [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.sort "Sort" [(Level.hole "_")])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" (Order.Hom.Basic.«term_→ₘ_» `α " →ₘ " `β))] "}")
    (Term.explicitBinder
     "("
     [`h]
     [":" (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `continuous [(Term.app `f [`i])]))]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `continuous
     [(Order.CompleteLattice.«term⨆_,_»
       "⨆"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Term.app `f [`i]))])))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app `Sup_continuous [(Term.hole "_")])
    "$"
    (Term.app (Term.proj `Set.forall_range_iff "." (fieldIdx "2")) [`h]))
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
   (Term.app `Sup_continuous [(Term.hole "_")])
   "$"
   (Term.app (Term.proj `Set.forall_range_iff "." (fieldIdx "2")) [`h]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `Set.forall_range_iff "." (fieldIdx "2")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Set.forall_range_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Set.forall_range_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `Sup_continuous [(Term.hole "_")])
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
  `Sup_continuous
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `continuous
   [(Order.CompleteLattice.«term⨆_,_»
     "⨆"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     ", "
     (Term.app `f [`i]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Term.app `f [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
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
  supr_continuous
  { ι : Sort _ } { f : ι → α →ₘ β } ( h : ∀ i , continuous f i ) : continuous ⨆ i , f i
  := Sup_continuous _ $ Set.forall_range_iff . 2 h

theorem Sup_continuous' (s : Set (α → β)) (hc : ∀, ∀ f ∈ s, ∀, continuous' f) : continuous' (Sup s) := by
  lift s to Set (α →ₘ β) using fun f hf => (hc f hf).to_monotone
  simp only [Set.ball_image_iff, continuous'_coe] at hc
  rw [Sup_image]
  norm_cast
  exact supr_continuous fun f => supr_continuous fun hf => hc f hf

theorem sup_continuous {f g : α →ₘ β} (hf : continuous f) (hg : continuous g) : continuous (f⊔g) := by
  rw [← Sup_pair]
  apply Sup_continuous
  rintro f (rfl | rfl | _) <;> assumption

theorem top_continuous : continuous (⊤ : α →ₘ β) := by
  intro c
  apply eq_of_forall_ge_iff
  intro z
  simp only [ωSup_le_iff, forall_const, chain.map_coe, · ∘ ·, Function.const, OrderHom.has_top_top,
    OrderHom.const_coe_coe]

theorem bot_continuous : continuous (⊥ : α →ₘ β) := by
  rw [← Sup_empty]
  exact Sup_continuous _ fun f hf => hf.elim

end CompleteLattice

namespace OmegaCompletePartialOrder

variable {α : Type u} {α' : Type _} {β : Type v} {β' : Type _} {γ : Type _} {φ : Type _}

variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

variable [OmegaCompletePartialOrder γ] [OmegaCompletePartialOrder φ]

variable [OmegaCompletePartialOrder α'] [OmegaCompletePartialOrder β']

namespace OrderHom

/--  The `ωSup` operator for monotone functions. -/
@[simps]
protected def ωSup (c : chain (α →ₘ β)) : α →ₘ β :=
  { toFun := fun a => ωSup (c.map (OrderHom.apply a)),
    monotone' := fun x y h => ωSup_le_ωSup_of_le (chain.map_le_map _ $ fun a => a.monotone h) }

@[simps ωSup_coe]
instance OmegaCompletePartialOrder : OmegaCompletePartialOrder (α →ₘ β) :=
  OmegaCompletePartialOrder.lift OrderHom.coeFnHom order_hom.ωSup (fun x y h => h) fun c => rfl

end OrderHom

section

variable (α β)

/--  A monotone function on `ω`-continuous partial orders is said to be continuous
if for every chain `c : chain α`, `f (⊔ i, c i) = ⊔ i, f (c i)`.
This is just the bundled version of `order_hom.continuous`. -/
structure continuous_hom extends OrderHom α β where
  cont : continuous (OrderHom.mk to_fun monotone')

attribute [nolint doc_blame] continuous_hom.to_order_hom

infixr:25 " →𝒄 " => continuous_hom

instance : CoeFun (α →𝒄 β) fun _ => α → β :=
  ⟨fun f => f.to_order_hom.to_fun⟩

instance : Coe (α →𝒄 β) (α →ₘ β) where
  coe := continuous_hom.to_order_hom

instance : PartialOrderₓ (α →𝒄 β) :=
  (PartialOrderₓ.lift fun f => f.to_order_hom.to_fun) $ by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h <;> congr <;> exact h

/--  See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def continuous_hom.simps.apply (h : α →𝒄 β) : α → β :=
  h

initialize_simps_projections ContinuousHom (to_order_hom_to_fun → apply, -toOrderHom)

end

namespace ContinuousHom

theorem congr_funₓ {f g : α →𝒄 β} (h : f = g) (x : α) : f x = g x :=
  congr_argₓ (fun h : α →𝒄 β => h x) h

theorem congr_argₓ (f : α →𝒄 β) {x y : α} (h : x = y) : f x = f y :=
  congr_argₓ (fun x : α => f x) h

protected theorem Monotone (f : α →𝒄 β) : Monotone f :=
  f.monotone'

@[mono]
theorem apply_mono {f g : α →𝒄 β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  OrderHom.apply_mono (show (f : α →ₘ β) ≤ g from h₁) h₂

theorem ite_continuous' {p : Prop} [hp : Decidable p] (f g : α → β) (hf : continuous' f) (hg : continuous' g) :
    continuous' fun x => if p then f x else g x := by
  split_ifs <;> simp

theorem ωSup_bind {β γ : Type v} (c : chain α) (f : α →ₘ Part β) (g : α →ₘ β → Part γ) :
    ωSup (c.map (f.bind g)) = ωSup (c.map f) >>= ωSup (c.map g) := by
  apply eq_of_forall_ge_iff
  intro x
  simp only [ωSup_le_iff, Part.bind_le, chain.mem_map_iff, and_imp, OrderHom.bind_coe, exists_imp_distrib]
  constructor <;> intro h'''
  ·
    intro b hb
    apply ωSup_le _ _ _
    rintro i y hy
    simp only [Part.mem_ωSup] at hb
    rcases hb with ⟨j, hb⟩
    replace hb := hb.symm
    simp only [Part.eq_some_iff, chain.map_coe, Function.comp_app, OrderHom.apply_coe] at hy hb
    replace hb : b ∈ f (c (max i j)) := f.mono (c.mono (le_max_rightₓ i j)) _ hb
    replace hy : y ∈ g (c (max i j)) b := g.mono (c.mono (le_max_leftₓ i j)) _ _ hy
    apply h''' (max i j)
    simp only [exists_prop, Part.bind_eq_bind, Part.mem_bind_iff, chain.map_coe, Function.comp_app, OrderHom.bind_coe]
    exact ⟨_, hb, hy⟩
  ·
    intro i
    intro y hy
    simp only [exists_prop, Part.bind_eq_bind, Part.mem_bind_iff, chain.map_coe, Function.comp_app,
      OrderHom.bind_coe] at hy
    rcases hy with ⟨b, hb₀, hb₁⟩
    apply h''' b _
    ·
      apply le_ωSup (c.map g) _ _ _ hb₁
    ·
      apply le_ωSup (c.map f) i _ hb₀

theorem bind_continuous' {β γ : Type v} (f : α → Part β) (g : α → β → Part γ) :
    continuous' f → continuous' g → continuous' fun x => f x >>= g x
  | ⟨hf, hf'⟩, ⟨hg, hg'⟩ =>
    continuous.of_bundled' (OrderHom.bind ⟨f, hf⟩ ⟨g, hg⟩)
      (by
        intro c <;> rw [ωSup_bind, ← hf', ← hg'] <;> rfl)

theorem map_continuous' {β γ : Type v} (f : β → γ) (g : α → Part β) (hg : continuous' g) :
    continuous' fun x => f <$> g x := by
  simp only [map_eq_bind_pure_comp] <;> apply bind_continuous' _ _ hg <;> apply const_continuous'

theorem seq_continuous' {β γ : Type v} (f : α → Part (β → γ)) (g : α → Part β) (hf : continuous' f)
    (hg : continuous' g) : continuous' fun x => f x<*>g x := by
  simp only [seq_eq_bind_mapₓ] <;>
    apply bind_continuous' _ _ hf <;>
      apply Pi.omegaCompletePartialOrder.flip₂_continuous' <;> intro <;> apply map_continuous' _ _ hg

theorem continuous (F : α →𝒄 β) (C : chain α) : F (ωSup C) = ωSup (C.map F) :=
  continuous_hom.cont _ _

/--  Construct a continuous function from a bare function, a continuous function, and a proof that
they are equal. -/
@[simps, reducible]
def of_fun (f : α → β) (g : α →𝒄 β) (h : f = g) : α →𝒄 β := by
  refine' { toOrderHom := { toFun := f, .. }, .. } <;> subst h <;> rcases g with ⟨⟨⟩⟩ <;> assumption

/--  Construct a continuous function from a monotone function with a proof of continuity. -/
@[simps, reducible]
def of_mono (f : α →ₘ β) (h : ∀ c : chain α, f (ωSup c) = ωSup (c.map f)) : α →𝒄 β :=
  { toFun := f, monotone' := f.monotone, cont := h }

/--  The identity as a continuous function. -/
@[simps]
def id : α →𝒄 α :=
  of_mono OrderHom.id continuous_id

/--  The composition of continuous functions. -/
@[simps]
def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
  of_mono (OrderHom.comp (↑f) (↑g)) (continuous_comp _ _ g.cont f.cont)

@[ext]
protected theorem ext (f g : α →𝒄 β) (h : ∀ x, f x = g x) : f = g := by
  cases f <;> cases g <;> congr <;> ext <;> apply h

protected theorem coe_inj (f g : α →𝒄 β) (h : (f : α → β) = g) : f = g :=
  continuous_hom.ext _ _ $ _root_.congr_fun h

@[simp]
theorem comp_id (f : β →𝒄 γ) : f.comp id = f := by
  ext <;> rfl

@[simp]
theorem id_comp (f : β →𝒄 γ) : id.comp f = f := by
  ext <;> rfl

@[simp]
theorem comp_assoc (f : γ →𝒄 φ) (g : β →𝒄 γ) (h : α →𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h := by
  ext <;> rfl

@[simp]
theorem coe_apply (a : α) (f : α →𝒄 β) : (f : α →ₘ β) a = f a :=
  rfl

/--  `function.const` is a continuous function. -/
def const (x : β) : α →𝒄 β :=
  of_mono (OrderHom.const _ x) (continuous_const x)

@[simp]
theorem const_apply (f : β) (a : α) : const f a = f :=
  rfl

instance [Inhabited β] : Inhabited (α →𝒄 β) :=
  ⟨const (default β)⟩

namespace Prod

/--  The application of continuous functions as a monotone function.

(It would make sense to make it a continuous function, but we are currently constructing a
`omega_complete_partial_order` instance for `α →𝒄 β`, and we cannot use it as the domain or image
of a continuous function before we do.) -/
@[simps]
def apply : (α →𝒄 β) × α →ₘ β :=
  { toFun := fun f => f.1 f.2,
    monotone' := fun x y h => by
      dsimp <;> trans y.fst x.snd <;> [apply h.1, apply y.1.Monotone h.2] }

end Prod

/--  The map from continuous functions to monotone functions is itself a monotone function. -/
@[simps]
def to_mono : (α →𝒄 β) →ₘ α →ₘ β :=
  { toFun := fun f => f, monotone' := fun x y h => h }

-- failed to format: format: uncaught backtrack exception
/--
      When proving that a chain of applications is below a bound `z`, it suffices to consider the
      functions and values being selected from the same index in the chains.
      
      This lemma is more specific than necessary, i.e. `c₀` only needs to be a
      chain of monotone functions, but it is only used with continuous functions. -/
    @[ simp ]
  theorem
    forall_forall_merge
    ( c₀ : chain ( α →𝒄 β ) ) ( c₁ : chain α ) ( z : β )
      : ( ∀ i j : ℕ , ( c₀ i ) ( c₁ j ) ≤ z ) ↔ ∀ i : ℕ , ( c₀ i ) ( c₁ i ) ≤ z
    :=
      by
        constructor <;> introv h
          · apply h
          ·
            apply le_transₓ _ ( h ( max i j ) )
              trans c₀ i ( c₁ ( max i j ) )
              · apply ( c₀ i ) . Monotone apply c₁.monotone apply le_max_rightₓ
              · apply c₀.monotone apply le_max_leftₓ

@[simp]
theorem forall_forall_merge' (c₀ : chain (α →𝒄 β)) (c₁ : chain α) (z : β) :
    (∀ j i : ℕ, (c₀ i) (c₁ j) ≤ z) ↔ ∀ i : ℕ, (c₀ i) (c₁ i) ≤ z := by
  rw [forall_swap, forall_forall_merge]

/--  The `ωSup` operator for continuous functions, which takes the pointwise countable supremum
of the functions in the `ω`-chain. -/
@[simps]
protected def ωSup (c : chain (α →𝒄 β)) : α →𝒄 β :=
  continuous_hom.of_mono (ωSup $ c.map to_mono)
    (by
      intro c'
      apply eq_of_forall_ge_iff
      intro z
      simp only [ωSup_le_iff, (c _).Continuous, chain.map_coe, OrderHom.apply_coe, to_mono_coe, coe_apply,
        order_hom.omega_complete_partial_order_ωSup_coe, forall_forall_merge, forall_forall_merge', · ∘ ·,
        Function.eval])

@[simps ωSup]
instance : OmegaCompletePartialOrder (α →𝒄 β) :=
  OmegaCompletePartialOrder.lift continuous_hom.to_mono continuous_hom.ωSup (fun x y h => h) fun c => rfl

theorem ωSup_def (c : chain (α →𝒄 β)) (x : α) : ωSup c x = continuous_hom.ωSup c x :=
  rfl

theorem ωSup_ωSup (c₀ : chain (α →𝒄 β)) (c₁ : chain α) :
    ωSup c₀ (ωSup c₁) = ωSup (continuous_hom.prod.apply.comp $ c₀.zip c₁) := by
  apply eq_of_forall_ge_iff
  intro z
  simp only [ωSup_le_iff, (c₀ _).Continuous, chain.map_coe, to_mono_coe, coe_apply,
    order_hom.omega_complete_partial_order_ωSup_coe, ωSup_def, forall_forall_merge, chain.zip_coe,
    OrderHom.prod_map_coe, OrderHom.diag_coe, Prod.map_mkₓ, OrderHom.apply_coe, Function.comp_app, prod.apply_coe,
    OrderHom.comp_coe, ωSup_apply, Function.eval]

/--  A family of continuous functions yields a continuous family of functions. -/
@[simps]
def flip {α : Type _} (f : α → β →𝒄 γ) : β →𝒄 α → γ :=
  { toFun := fun x y => f y x, monotone' := fun x y h a => (f a).Monotone h,
    cont := by
      intro <;> ext <;> change f x _ = _ <;> rw [(f x).Continuous] <;> rfl }

/--  `part.bind` as a continuous function. -/
@[simps (config := { rhsMd := reducible })]
noncomputable def bind {β γ : Type v} (f : α →𝒄 Part β) (g : α →𝒄 β → Part γ) : α →𝒄 Part γ :=
  of_mono (OrderHom.bind (↑f) (↑g)) $ fun c => by
    rw [OrderHom.bind, ← OrderHom.bind, ωSup_bind, ← f.continuous, ← g.continuous]
    rfl

/--  `part.map` as a continuous function. -/
@[simps (config := { rhsMd := reducible })]
noncomputable def map {β γ : Type v} (f : β → γ) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  of_fun (fun x => f <$> g x) (bind g (const (pure ∘ f))) $ by
    ext <;>
      simp only [map_eq_bind_pure_comp, bind_apply, OrderHom.bind_coe, const_apply, OrderHom.const_coe_coe, coe_apply]

/--  `part.seq` as a continuous function. -/
@[simps (config := { rhsMd := reducible })]
noncomputable def seq {β γ : Type v} (f : α →𝒄 Part (β → γ)) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  of_fun (fun x => f x<*>g x) (bind f $ flip $ _root_.flip map g)
    (by
      ext <;>
        simp only [seq_eq_bind_mapₓ, flip, Part.bind_eq_bind, map_apply, Part.mem_bind_iff, bind_apply,
            OrderHom.bind_coe, coe_apply, flip_apply] <;>
          rfl)

end ContinuousHom

end OmegaCompletePartialOrder

