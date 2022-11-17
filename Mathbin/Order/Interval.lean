/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Lattice
import Mathbin.Data.SetLike.Basic

/-!
# Order intervals

This file defines (nonempty) closed intervals in an order (see `set.Icc`). This is a prototype for
interval arithmetic.

## Main declarations

* `nonempty_interval`: Nonempty intervals. Pairs where the second element is greater than the first.
* `interval`: Intervals. Either `∅` or a nonempty interval.
-/


open Function OrderDual Set

variable {α β γ : Type _} {ι : Sort _} {κ : ι → Sort _}

/-- The nonempty closed intervals in an order.

We define intervals by the pair of endpoints `fst`, `snd`. To convert intervals to the set of
elements between these endpoints, use the coercion `nonempty_interval α → set α`. -/
@[ext.1]
structure NonemptyInterval (α : Type _) [LE α] extends α × α where
  fst_le_snd : fst ≤ snd
#align nonempty_interval NonemptyInterval

namespace NonemptyInterval

section LE

variable [LE α] {s t : NonemptyInterval α}

/-- The injection that induces the order on intervals. -/
def toDualProd : NonemptyInterval α → αᵒᵈ × α :=
  to_prod
#align nonempty_interval.to_dual_prod NonemptyInterval.toDualProd

@[simp]
theorem to_dual_prod_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, s.snd) :=
  Prod.mk.eta.symm
#align nonempty_interval.to_dual_prod_apply NonemptyInterval.to_dual_prod_apply

theorem to_dual_prod_injective : Injective (toDualProd : NonemptyInterval α → αᵒᵈ × α) := fun s t => (ext_iff _ _).2
#align nonempty_interval.to_dual_prod_injective NonemptyInterval.to_dual_prod_injective

instance [IsEmpty α] : IsEmpty (NonemptyInterval α) :=
  ⟨fun s => isEmptyElim s.fst⟩

instance [Subsingleton α] : Subsingleton (NonemptyInterval α) :=
  to_dual_prod_injective.Subsingleton

instance : LE (NonemptyInterval α) :=
  ⟨fun s t => t.fst ≤ s.fst ∧ s.snd ≤ t.snd⟩

theorem le_def : s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd :=
  Iff.rfl
#align nonempty_interval.le_def NonemptyInterval.le_def

/-- `to_dual_prod` as an order embedding. -/
@[simps]
def toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α where
  toFun := toDualProd
  inj' := to_dual_prod_injective
  map_rel_iff' _ _ := Iff.rfl
#align nonempty_interval.to_dual_prod_hom NonemptyInterval.toDualProdHom

/-- Turn an interval into an interval in the dual order. -/
def dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ where
  toFun s := ⟨s.toProd.swap, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.swap, s.fst_le_snd⟩
  left_inv s := ext _ _ $ Prod.swap_swap _
  right_inv s := ext _ _ $ Prod.swap_swap _
#align nonempty_interval.dual NonemptyInterval.dual

@[simp]
theorem fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd :=
  rfl
#align nonempty_interval.fst_dual NonemptyInterval.fst_dual

@[simp]
theorem snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst :=
  rfl
#align nonempty_interval.snd_dual NonemptyInterval.snd_dual

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ]

instance : Preorder (NonemptyInterval α) :=
  Preorder.lift toDualProd

/-- `{a}` as an interval. -/
@[simps]
def pure (a : α) : NonemptyInterval α :=
  ⟨⟨a, a⟩, le_rfl⟩
#align nonempty_interval.pure NonemptyInterval.pure

theorem pure_injective : Injective (pure : α → NonemptyInterval α) := fun s t => congr_arg $ Prod.fst ∘ to_prod
#align nonempty_interval.pure_injective NonemptyInterval.pure_injective

@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl
#align nonempty_interval.dual_pure NonemptyInterval.dual_pure

instance [Inhabited α] : Inhabited (NonemptyInterval α) :=
  ⟨pure default⟩

instance : ∀ [Nonempty α], Nonempty (NonemptyInterval α) :=
  Nonempty.map pure

instance [Nontrivial α] : Nontrivial (NonemptyInterval α) :=
  pure_injective.Nontrivial

/-- Pushforward of nonempty intervals. -/
@[simps]
def map (f : α →o β) (a : NonemptyInterval α) : NonemptyInterval β :=
  ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩
#align nonempty_interval.map NonemptyInterval.map

@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
#align nonempty_interval.map_pure NonemptyInterval.map_pure

@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (a : NonemptyInterval α) : (a.map f).map g = a.map (g.comp f) :=
  rfl
#align nonempty_interval.map_map NonemptyInterval.map_map

@[simp]
theorem dual_map (f : α →o β) (a : NonemptyInterval α) : (a.map f).dual = a.dual.map f.dual :=
  rfl
#align nonempty_interval.dual_map NonemptyInterval.dual_map

variable [BoundedOrder α]

instance : OrderTop (NonemptyInterval α) where
  top := ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top a := ⟨bot_le, le_top⟩

@[simp]
theorem dual_top : (⊤ : NonemptyInterval α).dual = ⊤ :=
  rfl
#align nonempty_interval.dual_top NonemptyInterval.dual_top

end Preorder

section PartialOrder

variable [PartialOrder α] {s t : NonemptyInterval α} {x : α × α} {a : α}

instance : PartialOrder (NonemptyInterval α) :=
  PartialOrder.lift _ to_dual_prod_injective

/-- Consider a nonempty interval `[a, b]` as the set `[a, b]`. -/
def coeHom : NonemptyInterval α ↪o Set α :=
  OrderEmbedding.ofMapLeIff (fun s => icc s.fst s.snd) fun s t => Icc_subset_Icc_iff s.fst_le_snd
#align nonempty_interval.coe_hom NonemptyInterval.coeHom

instance : SetLike (NonemptyInterval α) α where
  coe s := icc s.fst s.snd
  coe_injective' := coeHom.Injective

@[simp]
theorem mem_mk {hx : x.1 ≤ x.2} : a ∈ mk x hx ↔ x.1 ≤ a ∧ a ≤ x.2 :=
  Iff.rfl
#align nonempty_interval.mem_mk NonemptyInterval.mem_mk

theorem mem_def : a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd :=
  Iff.rfl
#align nonempty_interval.mem_def NonemptyInterval.mem_def

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le
#align nonempty_interval.coe_subset_coe NonemptyInterval.coe_subset_coe

@[simp, norm_cast]
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
#align nonempty_interval.coe_ssubset_coe NonemptyInterval.coe_ssubset_coe

@[simp]
theorem coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty :=
  nonempty_Icc.2 s.fst_le_snd
#align nonempty_interval.coe_nonempty NonemptyInterval.coe_nonempty

@[simp]
theorem coe_coe_hom : (coeHom : NonemptyInterval α → Set α) = coe :=
  rfl
#align nonempty_interval.coe_coe_hom NonemptyInterval.coe_coe_hom

@[simp, norm_cast]
theorem coe_pure (s : α) : (pure s : Set α) = {s} :=
  Icc_self _
#align nonempty_interval.coe_pure NonemptyInterval.coe_pure

@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ :=
  Icc_bot_top
#align nonempty_interval.coe_top NonemptyInterval.coe_top

@[simp, norm_cast]
theorem coe_dual (s : NonemptyInterval α) : (s.dual : Set αᵒᵈ) = of_dual ⁻¹' s :=
  dual_Icc
#align nonempty_interval.coe_dual NonemptyInterval.coe_dual

end PartialOrder

section Lattice

variable [Lattice α]

instance : HasSup (NonemptyInterval α) :=
  ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans $ s.fst_le_snd.trans le_sup_left⟩⟩

instance : SemilatticeSup (NonemptyInterval α) :=
  to_dual_prod_injective.SemilatticeSup _ $ fun _ _ => rfl

@[simp]
theorem fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst :=
  rfl
#align nonempty_interval.fst_sup NonemptyInterval.fst_sup

@[simp]
theorem snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd :=
  rfl
#align nonempty_interval.snd_sup NonemptyInterval.snd_sup

end Lattice

end NonemptyInterval

/-- The closed intervals in an order.

We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`.
To convert intervals to the set of elements between these endpoints, use the coercion
`interval α → set α`. -/
def Interval (α : Type _) [LE α] :=
  WithBot (NonemptyInterval α)deriving Inhabited, LE, OrderBot
#align interval Interval

namespace Interval

section LE

variable [LE α] {s t : Interval α}

instance : CoeTC (NonemptyInterval α) (Interval α) :=
  WithBot.hasCoeT

instance canLift : CanLift (Interval α) (NonemptyInterval α) coe fun r => r ≠ ⊥ :=
  WithBot.canLift
#align interval.can_lift Interval.canLift

theorem coe_injective : Injective (coe : NonemptyInterval α → Interval α) :=
  WithBot.coe_injective
#align interval.coe_injective Interval.coe_injective

@[simp, norm_cast]
theorem coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t :=
  WithBot.coe_inj
#align interval.coe_inj Interval.coe_inj

@[protected]
theorem forall {p : Interval α → Prop} : (∀ s, p s) ↔ p ⊥ ∧ ∀ s : NonemptyInterval α, p s :=
  Option.forall
#align interval.forall Interval.forall

@[protected]
theorem exists {p : Interval α → Prop} : (∃ s, p s) ↔ p ⊥ ∨ ∃ s : NonemptyInterval α, p s :=
  Option.exists
#align interval.exists Interval.exists

instance [IsEmpty α] : Unique (Interval α) :=
  Option.unique

/-- Turn an interval into an interval in the dual order. -/
def dual : Interval α ≃ Interval αᵒᵈ :=
  NonemptyInterval.dual.optionCongr
#align interval.dual Interval.dual

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ]

instance : Preorder (Interval α) :=
  WithBot.preorder

/-- `{a}` as an interval. -/
def pure (a : α) : Interval α :=
  NonemptyInterval.pure a
#align interval.pure Interval.pure

theorem pure_injective : Injective (pure : α → Interval α) :=
  coe_injective.comp NonemptyInterval.pure_injective
#align interval.pure_injective Interval.pure_injective

@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl
#align interval.dual_pure Interval.dual_pure

@[simp]
theorem dual_bot : (⊥ : Interval α).dual = ⊥ :=
  rfl
#align interval.dual_bot Interval.dual_bot

instance [Nonempty α] : Nontrivial (Interval α) :=
  Option.nontrivial

/-- Pushforward of intervals. -/
def map (f : α →o β) : Interval α → Interval β :=
  WithBot.map (NonemptyInterval.map f)
#align interval.map Interval.map

@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
#align interval.map_pure Interval.map_pure

@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (s : Interval α) : (s.map f).map g = s.map (g.comp f) :=
  Option.map_map _ _ _
#align interval.map_map Interval.map_map

@[simp]
theorem dual_map (f : α →o β) (s : Interval α) : (s.map f).dual = s.dual.map f.dual := by
  cases s
  · rfl
    
  · exact WithBot.map_comm rfl _
    
#align interval.dual_map Interval.dual_map

variable [BoundedOrder α]

instance : BoundedOrder (Interval α) :=
  WithBot.boundedOrder

@[simp]
theorem dual_top : (⊤ : Interval α).dual = ⊤ :=
  rfl
#align interval.dual_top Interval.dual_top

end Preorder

section PartialOrder

variable [PartialOrder α] {s t : Interval α}

instance : PartialOrder (Interval α) :=
  WithBot.partialOrder

/-- Consider a interval `[a, b]` as the set `[a, b]`. -/
def coeHom : Interval α ↪o Set α :=
  OrderEmbedding.ofMapLeIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, t => iff_of_true bot_le bot_le
    | some s, ⊥ => iff_of_false (fun h => s.coe_nonempty.ne_empty $ le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some s, some t => (@NonemptyInterval.coeHom α _).le_iff_le.trans WithBot.some_le_some.symm
#align interval.coe_hom Interval.coeHom

instance : SetLike (Interval α) α where
  coe := coeHom
  coe_injective' := coeHom.Injective

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le
#align interval.coe_subset_coe Interval.coe_subset_coe

@[simp, norm_cast]
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
#align interval.coe_ssubset_coe Interval.coe_ssubset_coe

@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _
#align interval.coe_pure Interval.coe_pure

@[simp, norm_cast]
theorem coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s :=
  rfl
#align interval.coe_coe Interval.coe_coe

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Interval α) : Set α) = ∅ :=
  rfl
#align interval.coe_bot Interval.coe_bot

@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ :=
  Icc_bot_top
#align interval.coe_top Interval.coe_top

@[simp, norm_cast]
theorem coe_dual (s : Interval α) : (s.dual : Set αᵒᵈ) = of_dual ⁻¹' s := by
  cases s
  · rfl
    
  exact s.coe_dual
#align interval.coe_dual Interval.coe_dual

end PartialOrder

section Lattice

variable [Lattice α]

instance : SemilatticeSup (Interval α) :=
  WithBot.semilatticeSup

section Decidable

variable [@DecidableRel α (· ≤ ·)]

instance : Lattice (Interval α) :=
  { Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, t => ⊥
      | s, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then
          some ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩, sup_le (le_inf s.fst_le_snd h.1) $ le_inf h.2 t.fst_le_snd⟩
        else ⊥,
    inf_le_left := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some t => bot_le
      | some s, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.some_le_some.2 ⟨le_sup_left, inf_le_left⟩
          
        · exact bot_le
          ,
    inf_le_right := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some t => bot_le
      | some s, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.some_le_some.2 ⟨le_sup_right, inf_le_right⟩
          
        · exact bot_le
          ,
    le_inf := fun s t c =>
      match s, t, c with
      | ⊥, t, c => fun _ _ => bot_le
      | some s, t, c => fun hb hc => by
        lift t to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hb
        lift c to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hc
        change _ ≤ dite _ _ _
        simp only [WithBot.some_eq_coe, WithBot.coe_le_coe] at hb hc⊢
        rw [dif_pos, WithBot.coe_le_coe]
        exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩
        exact ⟨hb.1.trans $ s.fst_le_snd.trans hc.2, hc.1.trans $ s.fst_le_snd.trans hb.2⟩ }

@[simp, norm_cast]
theorem coe_inf (s t : Interval α) : (↑(s ⊓ t) : Set α) = s ∩ t := by
  cases s
  · rw [WithBot.none_eq_bot, bot_inf_eq]
    exact (empty_inter _).symm
    
  cases t
  · rw [WithBot.none_eq_bot, inf_bot_eq]
    exact (inter_empty _).symm
    
  refine' (_ : coe (dite _ _ _) = _).trans Icc_inter_Icc.symm
  split_ifs
  · rfl
    
  · exact
      (Icc_eq_empty $ fun H =>
          h ⟨le_sup_left.trans $ H.trans inf_le_right, le_sup_right.trans $ H.trans inf_le_left⟩).symm
    
#align interval.coe_inf Interval.coe_inf

end Decidable

@[simp, norm_cast]
theorem disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t := by classical
  rw [disjoint_iff_inf_le, disjoint_iff_inf_le, le_eq_subset, ← coe_subset_coe, coe_inf]
  rfl
#align interval.disjoint_coe Interval.disjoint_coe

end Lattice

end Interval

namespace NonemptyInterval

section Preorder

variable [Preorder α]

@[simp, norm_cast]
theorem coe_pure_interval (s : α) : (pure s : Interval α) = Interval.pure s :=
  rfl
#align nonempty_interval.coe_pure_interval NonemptyInterval.coe_pure_interval

@[simp, norm_cast]
theorem coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α) = ⊤ :=
  rfl
#align nonempty_interval.coe_top_interval NonemptyInterval.coe_top_interval

end Preorder

@[simp, norm_cast]
theorem mem_coe_interval [PartialOrder α] {s : NonemptyInterval α} {x : α} : x ∈ (s : Interval α) ↔ x ∈ s :=
  Iff.rfl
#align nonempty_interval.mem_coe_interval NonemptyInterval.mem_coe_interval

@[simp, norm_cast]
theorem coe_sup_interval [Lattice α] (s t : NonemptyInterval α) : (↑(s ⊔ t) : Interval α) = s ⊔ t :=
  rfl
#align nonempty_interval.coe_sup_interval NonemptyInterval.coe_sup_interval

end NonemptyInterval

namespace Interval

section CompleteLattice

variable [CompleteLattice α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [(Command.noncomputable "noncomputable")] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder
         "["
         []
         (Term.app
          (Term.explicit "@" `DecidableRel)
          [`α (Term.paren "(" (Init.Core.«term_≤_» (Term.cdot "·") " ≤ " (Term.cdot "·")) ")")])
         "]")]
       (Term.typeSpec ":" (Term.app `CompleteLattice [(Term.app `Interval [`α])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.structInst
              "{"
              [[`Interval.lattice "," `Interval.boundedOrder] "with"]
              [(Term.structInstField
                (Term.structInstLVal `sup [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`S]
                  []
                  "=>"
                  (termDepIfThenElse
                   "if"
                   (Lean.binderIdent `h)
                   ":"
                   (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
                   "then"
                   (Order.BoundedOrder.«term⊥» "⊥")
                   "else"
                   (Term.app
                    `some
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor
                        "⟨"
                        [(Order.CompleteLattice.«term⨅_,_»
                          "⨅"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinderCollection
                            [(Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `s)
                               [(group ":" (Term.app `NonemptyInterval [`α]))])
                              ")")
                             (Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `h)
                               [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                              ")")]))
                          ", "
                          (Term.proj `s "." `fst))
                         ","
                         (Order.CompleteLattice.«term⨆_,_»
                          "⨆"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinderCollection
                            [(Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `s)
                               [(group ":" (Term.app `NonemptyInterval [`α]))])
                              ")")
                             (Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `h)
                               [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                              ")")]))
                          ", "
                          (Term.proj `s "." `snd))]
                        "⟩")
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Std.Tactic.obtain
                            "obtain"
                            [(Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                                  [])]
                                "⟩")])]
                            []
                            [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                           []
                           (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
                           []
                           (Tactic.exact
                            "exact"
                            (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
                      "⟩")])))))
               ","
               (Term.structInstField
                (Term.structInstLVal `le_Sup [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`s `s `ha]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
                      []
                      (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group (Tactic.exact "exact" `bot_le) [])])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group
                         (Tactic.exact
                          "exact"
                          (Term.app
                           (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                           [(Term.anonymousCtor
                             "⟨"
                             [(Term.app `infi₂_le [(Term.hole "_") `ha])
                              ","
                              (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
                             "⟩")]))
                         [])])]))))))
               ","
               (Term.structInstField
                (Term.structInstLVal `Sup_le [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`s `s `ha]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group (Tactic.exact "exact" `bot_le) [])])
                      []
                      (Std.Tactic.obtain
                       "obtain"
                       [(Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                             [])]
                           "⟩")])]
                       []
                       [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                      []
                      (Tactic.lift
                       "lift"
                       `s
                       "to"
                       (Term.app `NonemptyInterval [`α])
                       ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
                       [])
                      []
                      (Tactic.exact
                       "exact"
                       (Term.app
                        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                        [(Term.anonymousCtor
                          "⟨"
                          [(Init.Core.«term_$_»
                            `le_infi₂
                            " $ "
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`c `hc]
                              []
                              "=>"
                              (Term.proj
                               (Init.Core.«term_$_»
                                (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                " $ "
                                (Term.app `ha [(Term.hole "_") `hc]))
                               "."
                               (fieldIdx "1")))))
                           ","
                           (Init.Core.«term_$_»
                            `supr₂_le
                            " $ "
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [`c `hc]
                              []
                              "=>"
                              (Term.proj
                               (Init.Core.«term_$_»
                                (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                " $ "
                                (Term.app `ha [(Term.hole "_") `hc]))
                               "."
                               (fieldIdx "2")))))]
                          "⟩")]))]))))))
               ","
               (Term.structInstField
                (Term.structInstLVal `inf [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`S]
                  []
                  "=>"
                  (termDepIfThenElse
                   "if"
                   (Lean.binderIdent `h)
                   ":"
                   (Init.Logic.«term_∧_»
                    (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
                    " ∧ "
                    (Term.forall
                     "∀"
                     [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                     []
                     ","
                     (Term.arrow
                      (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
                      "→"
                      (Term.forall
                       "∀"
                       [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                       []
                       ","
                       (Term.arrow
                        (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
                        "→"
                        (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
                   "then"
                   (Term.app
                    `some
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor
                        "⟨"
                        [(Order.CompleteLattice.«term⨆_,_»
                          "⨆"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinderCollection
                            [(Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `s)
                               [(group ":" (Term.app `NonemptyInterval [`α]))])
                              ")")
                             (Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `h)
                               [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                              ")")]))
                          ", "
                          (Term.proj `s "." `fst))
                         ","
                         (Order.CompleteLattice.«term⨅_,_»
                          "⨅"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinderCollection
                            [(Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `s)
                               [(group ":" (Term.app `NonemptyInterval [`α]))])
                              ")")
                             (Std.ExtendedBinder.extBinderParenthesized
                              "("
                              (Std.ExtendedBinder.extBinder
                               (Lean.binderIdent `h)
                               [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                              ")")]))
                          ", "
                          (Term.proj `s "." `snd))]
                        "⟩")
                       ","
                       (Init.Core.«term_$_»
                        `supr₂_le
                        " $ "
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`s `hs]
                          []
                          "=>"
                          (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
                      "⟩")])
                   "else"
                   (Order.BoundedOrder.«term⊥» "⊥")))))
               ","
               (Term.structInstField
                (Term.structInstLVal `Inf_le [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`s `s `ha]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group
                         (Tactic.lift
                          "lift"
                          `s
                          "to"
                          (Term.app `NonemptyInterval [`α])
                          ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
                          [])
                         [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.app
                           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                           [(Term.anonymousCtor
                             "⟨"
                             [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])]
                             "⟩")]))
                         [])])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group (Tactic.exact "exact" `bot_le) [])])]))))))
               ","
               (Term.structInstField
                (Term.structInstLVal `le_Inf [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`S `s `ha]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group (Tactic.exact "exact" `bot_le) [])])
                      []
                      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group
                         (Tactic.exact
                          "exact"
                          (Term.app
                           (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                           [(Term.anonymousCtor
                             "⟨"
                             [(Init.Core.«term_$_»
                               `supr₂_le
                               " $ "
                               (Term.fun
                                "fun"
                                (Term.basicFun
                                 [`t `hb]
                                 []
                                 "=>"
                                 (Term.proj
                                  (Init.Core.«term_$_»
                                   (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                   " $ "
                                   (Term.app `ha [(Term.hole "_") `hb]))
                                  "."
                                  (fieldIdx "1")))))
                              ","
                              (Init.Core.«term_$_»
                               `le_infi₂
                               " $ "
                               (Term.fun
                                "fun"
                                (Term.basicFun
                                 [`t `hb]
                                 []
                                 "=>"
                                 (Term.proj
                                  (Init.Core.«term_$_»
                                   (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                   " $ "
                                   (Term.app `ha [(Term.hole "_") `hb]))
                                  "."
                                  (fieldIdx "2")))))]
                             "⟩")]))
                         [])])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                      []
                      (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
                      []
                      («tactic___;_»
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
                      []
                      (Tactic.cases
                       "cases"
                       [(Tactic.casesTarget
                         []
                         (Term.app
                          `h
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`t `hb `c `hc]
                             []
                             "=>"
                             (Init.Core.«term_$_»
                              (Term.proj
                               (Term.proj
                                (Init.Core.«term_$_»
                                 (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                 " $ "
                                 (Term.app `ha [(Term.hole "_") `hb]))
                                "."
                                (fieldIdx "1"))
                               "."
                               `trans)
                              " $ "
                              (Term.app
                               `s.fst_le_snd.trans
                               [(Term.proj
                                 (Init.Core.«term_$_»
                                  (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                  " $ "
                                  (Term.app `ha [(Term.hole "_") `hc]))
                                 "."
                                 (fieldIdx "2"))]))))]))]
                       []
                       [])]))))))]
              (Term.optEllipsis [])
              []
              "}")))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.structInst
             "{"
             [[`Interval.lattice "," `Interval.boundedOrder] "with"]
             [(Term.structInstField
               (Term.structInstLVal `sup [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`S]
                 []
                 "=>"
                 (termDepIfThenElse
                  "if"
                  (Lean.binderIdent `h)
                  ":"
                  (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
                  "then"
                  (Order.BoundedOrder.«term⊥» "⊥")
                  "else"
                  (Term.app
                   `some
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor
                       "⟨"
                       [(Order.CompleteLattice.«term⨅_,_»
                         "⨅"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinderCollection
                           [(Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `s)
                              [(group ":" (Term.app `NonemptyInterval [`α]))])
                             ")")
                            (Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `h)
                              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                             ")")]))
                         ", "
                         (Term.proj `s "." `fst))
                        ","
                        (Order.CompleteLattice.«term⨆_,_»
                         "⨆"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinderCollection
                           [(Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `s)
                              [(group ":" (Term.app `NonemptyInterval [`α]))])
                             ")")
                            (Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `h)
                              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                             ")")]))
                         ", "
                         (Term.proj `s "." `snd))]
                       "⟩")
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Std.Tactic.obtain
                           "obtain"
                           [(Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                                 [])]
                               "⟩")])]
                           []
                           [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                          []
                          (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
                          []
                          (Tactic.exact
                           "exact"
                           (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
                     "⟩")])))))
              ","
              (Term.structInstField
               (Term.structInstLVal `le_Sup [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`s `s `ha]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
                     []
                     (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group (Tactic.exact "exact" `bot_le) [])])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group
                        (Tactic.exact
                         "exact"
                         (Term.app
                          (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                          [(Term.anonymousCtor
                            "⟨"
                            [(Term.app `infi₂_le [(Term.hole "_") `ha])
                             ","
                             (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
                            "⟩")]))
                        [])])]))))))
              ","
              (Term.structInstField
               (Term.structInstLVal `Sup_le [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`s `s `ha]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group (Tactic.exact "exact" `bot_le) [])])
                     []
                     (Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                     []
                     (Tactic.lift
                      "lift"
                      `s
                      "to"
                      (Term.app `NonemptyInterval [`α])
                      ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                       [(Term.anonymousCtor
                         "⟨"
                         [(Init.Core.«term_$_»
                           `le_infi₂
                           " $ "
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`c `hc]
                             []
                             "=>"
                             (Term.proj
                              (Init.Core.«term_$_»
                               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                               " $ "
                               (Term.app `ha [(Term.hole "_") `hc]))
                              "."
                              (fieldIdx "1")))))
                          ","
                          (Init.Core.«term_$_»
                           `supr₂_le
                           " $ "
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`c `hc]
                             []
                             "=>"
                             (Term.proj
                              (Init.Core.«term_$_»
                               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                               " $ "
                               (Term.app `ha [(Term.hole "_") `hc]))
                              "."
                              (fieldIdx "2")))))]
                         "⟩")]))]))))))
              ","
              (Term.structInstField
               (Term.structInstLVal `inf [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`S]
                 []
                 "=>"
                 (termDepIfThenElse
                  "if"
                  (Lean.binderIdent `h)
                  ":"
                  (Init.Logic.«term_∧_»
                   (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
                   " ∧ "
                   (Term.forall
                    "∀"
                    [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                    []
                    ","
                    (Term.arrow
                     (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
                     "→"
                     (Term.forall
                      "∀"
                      [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                      []
                      ","
                      (Term.arrow
                       (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
                       "→"
                       (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
                  "then"
                  (Term.app
                   `some
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor
                       "⟨"
                       [(Order.CompleteLattice.«term⨆_,_»
                         "⨆"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinderCollection
                           [(Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `s)
                              [(group ":" (Term.app `NonemptyInterval [`α]))])
                             ")")
                            (Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `h)
                              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                             ")")]))
                         ", "
                         (Term.proj `s "." `fst))
                        ","
                        (Order.CompleteLattice.«term⨅_,_»
                         "⨅"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinderCollection
                           [(Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `s)
                              [(group ":" (Term.app `NonemptyInterval [`α]))])
                             ")")
                            (Std.ExtendedBinder.extBinderParenthesized
                             "("
                             (Std.ExtendedBinder.extBinder
                              (Lean.binderIdent `h)
                              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                             ")")]))
                         ", "
                         (Term.proj `s "." `snd))]
                       "⟩")
                      ","
                      (Init.Core.«term_$_»
                       `supr₂_le
                       " $ "
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`s `hs]
                         []
                         "=>"
                         (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
                     "⟩")])
                  "else"
                  (Order.BoundedOrder.«term⊥» "⊥")))))
              ","
              (Term.structInstField
               (Term.structInstLVal `Inf_le [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`s `s `ha]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group
                        (Tactic.lift
                         "lift"
                         `s
                         "to"
                         (Term.app `NonemptyInterval [`α])
                         ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
                         [])
                        [])
                       (group
                        (Tactic.exact
                         "exact"
                         (Term.app
                          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                          [(Term.anonymousCtor
                            "⟨"
                            [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])]
                            "⟩")]))
                        [])])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group (Tactic.exact "exact" `bot_le) [])])]))))))
              ","
              (Term.structInstField
               (Term.structInstLVal `le_Inf [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`S `s `ha]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group (Tactic.exact "exact" `bot_le) [])])
                     []
                     (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group
                        (Tactic.exact
                         "exact"
                         (Term.app
                          (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                          [(Term.anonymousCtor
                            "⟨"
                            [(Init.Core.«term_$_»
                              `supr₂_le
                              " $ "
                              (Term.fun
                               "fun"
                               (Term.basicFun
                                [`t `hb]
                                []
                                "=>"
                                (Term.proj
                                 (Init.Core.«term_$_»
                                  (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                  " $ "
                                  (Term.app `ha [(Term.hole "_") `hb]))
                                 "."
                                 (fieldIdx "1")))))
                             ","
                             (Init.Core.«term_$_»
                              `le_infi₂
                              " $ "
                              (Term.fun
                               "fun"
                               (Term.basicFun
                                [`t `hb]
                                []
                                "=>"
                                (Term.proj
                                 (Init.Core.«term_$_»
                                  (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                  " $ "
                                  (Term.app `ha [(Term.hole "_") `hb]))
                                 "."
                                 (fieldIdx "2")))))]
                            "⟩")]))
                        [])])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                     []
                     (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
                     []
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
                     []
                     (Tactic.cases
                      "cases"
                      [(Tactic.casesTarget
                        []
                        (Term.app
                         `h
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`t `hb `c `hc]
                            []
                            "=>"
                            (Init.Core.«term_$_»
                             (Term.proj
                              (Term.proj
                               (Init.Core.«term_$_»
                                (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                " $ "
                                (Term.app `ha [(Term.hole "_") `hb]))
                               "."
                               (fieldIdx "1"))
                              "."
                              `trans)
                             " $ "
                             (Term.app
                              `s.fst_le_snd.trans
                              [(Term.proj
                                (Init.Core.«term_$_»
                                 (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                                 " $ "
                                 (Term.app `ha [(Term.hole "_") `hc]))
                                "."
                                (fieldIdx "2"))]))))]))]
                      []
                      [])]))))))]
             (Term.optEllipsis [])
             []
             "}")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.structInst
         "{"
         [[`Interval.lattice "," `Interval.boundedOrder] "with"]
         [(Term.structInstField
           (Term.structInstLVal `sup [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`S]
             []
             "=>"
             (termDepIfThenElse
              "if"
              (Lean.binderIdent `h)
              ":"
              (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
              "then"
              (Order.BoundedOrder.«term⊥» "⊥")
              "else"
              (Term.app
               `some
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor
                   "⟨"
                   [(Order.CompleteLattice.«term⨅_,_»
                     "⨅"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinderCollection
                       [(Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `s)
                          [(group ":" (Term.app `NonemptyInterval [`α]))])
                         ")")
                        (Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `h)
                          [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                         ")")]))
                     ", "
                     (Term.proj `s "." `fst))
                    ","
                    (Order.CompleteLattice.«term⨆_,_»
                     "⨆"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinderCollection
                       [(Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `s)
                          [(group ":" (Term.app `NonemptyInterval [`α]))])
                         ")")
                        (Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `h)
                          [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                         ")")]))
                     ", "
                     (Term.proj `s "." `snd))]
                   "⟩")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Std.Tactic.obtain
                       "obtain"
                       [(Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                             [])]
                           "⟩")])]
                       []
                       [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                      []
                      (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
                      []
                      (Tactic.exact
                       "exact"
                       (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
                 "⟩")])))))
          ","
          (Term.structInstField
           (Term.structInstLVal `le_Sup [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`s `s `ha]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
                 []
                 (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                 []
                 («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                      [(Term.anonymousCtor
                        "⟨"
                        [(Term.app `infi₂_le [(Term.hole "_") `ha])
                         ","
                         (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
                        "⟩")]))
                    [])])]))))))
          ","
          (Term.structInstField
           (Term.structInstLVal `Sup_le [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`s `s `ha]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                 []
                 («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                 []
                 (Tactic.lift
                  "lift"
                  `s
                  "to"
                  (Term.app `NonemptyInterval [`α])
                  ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                   [(Term.anonymousCtor
                     "⟨"
                     [(Init.Core.«term_$_»
                       `le_infi₂
                       " $ "
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`c `hc]
                         []
                         "=>"
                         (Term.proj
                          (Init.Core.«term_$_»
                           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                           " $ "
                           (Term.app `ha [(Term.hole "_") `hc]))
                          "."
                          (fieldIdx "1")))))
                      ","
                      (Init.Core.«term_$_»
                       `supr₂_le
                       " $ "
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`c `hc]
                         []
                         "=>"
                         (Term.proj
                          (Init.Core.«term_$_»
                           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                           " $ "
                           (Term.app `ha [(Term.hole "_") `hc]))
                          "."
                          (fieldIdx "2")))))]
                     "⟩")]))]))))))
          ","
          (Term.structInstField
           (Term.structInstLVal `inf [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`S]
             []
             "=>"
             (termDepIfThenElse
              "if"
              (Lean.binderIdent `h)
              ":"
              (Init.Logic.«term_∧_»
               (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
               " ∧ "
               (Term.forall
                "∀"
                [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                []
                ","
                (Term.arrow
                 (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
                 "→"
                 (Term.forall
                  "∀"
                  [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                  []
                  ","
                  (Term.arrow
                   (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
                   "→"
                   (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
              "then"
              (Term.app
               `some
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor
                   "⟨"
                   [(Order.CompleteLattice.«term⨆_,_»
                     "⨆"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinderCollection
                       [(Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `s)
                          [(group ":" (Term.app `NonemptyInterval [`α]))])
                         ")")
                        (Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `h)
                          [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                         ")")]))
                     ", "
                     (Term.proj `s "." `fst))
                    ","
                    (Order.CompleteLattice.«term⨅_,_»
                     "⨅"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinderCollection
                       [(Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `s)
                          [(group ":" (Term.app `NonemptyInterval [`α]))])
                         ")")
                        (Std.ExtendedBinder.extBinderParenthesized
                         "("
                         (Std.ExtendedBinder.extBinder
                          (Lean.binderIdent `h)
                          [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                         ")")]))
                     ", "
                     (Term.proj `s "." `snd))]
                   "⟩")
                  ","
                  (Init.Core.«term_$_»
                   `supr₂_le
                   " $ "
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`s `hs]
                     []
                     "=>"
                     (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
                 "⟩")])
              "else"
              (Order.BoundedOrder.«term⊥» "⊥")))))
          ","
          (Term.structInstField
           (Term.structInstLVal `Inf_le [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`s `s `ha]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Tactic.lift
                     "lift"
                     `s
                     "to"
                     (Term.app `NonemptyInterval [`α])
                     ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
                     [])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                      [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")]))
                    [])])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Tactic.exact "exact" `bot_le) [])])]))))))
          ","
          (Term.structInstField
           (Term.structInstLVal `le_Inf [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`S `s `ha]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                 []
                 («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
                 []
                 (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                      [(Term.anonymousCtor
                        "⟨"
                        [(Init.Core.«term_$_»
                          `supr₂_le
                          " $ "
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`t `hb]
                            []
                            "=>"
                            (Term.proj
                             (Init.Core.«term_$_»
                              (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                              " $ "
                              (Term.app `ha [(Term.hole "_") `hb]))
                             "."
                             (fieldIdx "1")))))
                         ","
                         (Init.Core.«term_$_»
                          `le_infi₂
                          " $ "
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`t `hb]
                            []
                            "=>"
                            (Term.proj
                             (Init.Core.«term_$_»
                              (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                              " $ "
                              (Term.app `ha [(Term.hole "_") `hb]))
                             "."
                             (fieldIdx "2")))))]
                        "⟩")]))
                    [])])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                 []
                 (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
                 []
                 (Tactic.cases
                  "cases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     `h
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`t `hb `c `hc]
                        []
                        "=>"
                        (Init.Core.«term_$_»
                         (Term.proj
                          (Term.proj
                           (Init.Core.«term_$_»
                            (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                            " $ "
                            (Term.app `ha [(Term.hole "_") `hb]))
                           "."
                           (fieldIdx "1"))
                          "."
                          `trans)
                         " $ "
                         (Term.app
                          `s.fst_le_snd.trans
                          [(Term.proj
                            (Init.Core.«term_$_»
                             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                             " $ "
                             (Term.app `ha [(Term.hole "_") `hc]))
                            "."
                            (fieldIdx "2"))]))))]))]
                  []
                  [])]))))))]
         (Term.optEllipsis [])
         []
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.structInst
        "{"
        [[`Interval.lattice "," `Interval.boundedOrder] "with"]
        [(Term.structInstField
          (Term.structInstLVal `sup [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`S]
            []
            "=>"
            (termDepIfThenElse
             "if"
             (Lean.binderIdent `h)
             ":"
             (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
             "then"
             (Order.BoundedOrder.«term⊥» "⊥")
             "else"
             (Term.app
              `some
              [(Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Order.CompleteLattice.«term⨅_,_»
                    "⨅"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinderCollection
                      [(Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `s)
                         [(group ":" (Term.app `NonemptyInterval [`α]))])
                        ")")
                       (Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `h)
                         [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                        ")")]))
                    ", "
                    (Term.proj `s "." `fst))
                   ","
                   (Order.CompleteLattice.«term⨆_,_»
                    "⨆"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinderCollection
                      [(Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `s)
                         [(group ":" (Term.app `NonemptyInterval [`α]))])
                        ")")
                       (Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `h)
                         [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                        ")")]))
                    ", "
                    (Term.proj `s "." `snd))]
                  "⟩")
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                     []
                     (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
                "⟩")])))))
         ","
         (Term.structInstField
          (Term.structInstLVal `le_Sup [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`s `s `ha]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                []
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
                []
                (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                []
                («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
                []
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.app `infi₂_le [(Term.hole "_") `ha])
                        ","
                        (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
                       "⟩")]))
                   [])])]))))))
         ","
         (Term.structInstField
          (Term.structInstLVal `Sup_le [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`s `s `ha]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                []
                («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                []
                (Tactic.lift
                 "lift"
                 `s
                 "to"
                 (Term.app `NonemptyInterval [`α])
                 ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [(Init.Core.«term_$_»
                      `le_infi₂
                      " $ "
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`c `hc]
                        []
                        "=>"
                        (Term.proj
                         (Init.Core.«term_$_»
                          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                          " $ "
                          (Term.app `ha [(Term.hole "_") `hc]))
                         "."
                         (fieldIdx "1")))))
                     ","
                     (Init.Core.«term_$_»
                      `supr₂_le
                      " $ "
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`c `hc]
                        []
                        "=>"
                        (Term.proj
                         (Init.Core.«term_$_»
                          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                          " $ "
                          (Term.app `ha [(Term.hole "_") `hc]))
                         "."
                         (fieldIdx "2")))))]
                    "⟩")]))]))))))
         ","
         (Term.structInstField
          (Term.structInstLVal `inf [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`S]
            []
            "=>"
            (termDepIfThenElse
             "if"
             (Lean.binderIdent `h)
             ":"
             (Init.Logic.«term_∧_»
              (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
              " ∧ "
              (Term.forall
               "∀"
               [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
               []
               ","
               (Term.arrow
                (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
                "→"
                (Term.forall
                 "∀"
                 [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                 []
                 ","
                 (Term.arrow
                  (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
                  "→"
                  (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
             "then"
             (Term.app
              `some
              [(Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Order.CompleteLattice.«term⨆_,_»
                    "⨆"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinderCollection
                      [(Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `s)
                         [(group ":" (Term.app `NonemptyInterval [`α]))])
                        ")")
                       (Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `h)
                         [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                        ")")]))
                    ", "
                    (Term.proj `s "." `fst))
                   ","
                   (Order.CompleteLattice.«term⨅_,_»
                    "⨅"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinderCollection
                      [(Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `s)
                         [(group ":" (Term.app `NonemptyInterval [`α]))])
                        ")")
                       (Std.ExtendedBinder.extBinderParenthesized
                        "("
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `h)
                         [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                        ")")]))
                    ", "
                    (Term.proj `s "." `snd))]
                  "⟩")
                 ","
                 (Init.Core.«term_$_»
                  `supr₂_le
                  " $ "
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`s `hs]
                    []
                    "=>"
                    (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
                "⟩")])
             "else"
             (Order.BoundedOrder.«term⊥» "⊥")))))
         ","
         (Term.structInstField
          (Term.structInstLVal `Inf_le [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`s `s `ha]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
                []
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group
                   (Tactic.lift
                    "lift"
                    `s
                    "to"
                    (Term.app `NonemptyInterval [`α])
                    ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
                    [])
                   [])
                  (group
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                     [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")]))
                   [])])
                []
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group (Tactic.exact "exact" `bot_le) [])])]))))))
         ","
         (Term.structInstField
          (Term.structInstLVal `le_Inf [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`S `s `ha]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
                []
                («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
                []
                (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                []
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                     [(Term.anonymousCtor
                       "⟨"
                       [(Init.Core.«term_$_»
                         `supr₂_le
                         " $ "
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`t `hb]
                           []
                           "=>"
                           (Term.proj
                            (Init.Core.«term_$_»
                             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                             " $ "
                             (Term.app `ha [(Term.hole "_") `hb]))
                            "."
                            (fieldIdx "1")))))
                        ","
                        (Init.Core.«term_$_»
                         `le_infi₂
                         " $ "
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`t `hb]
                           []
                           "=>"
                           (Term.proj
                            (Init.Core.«term_$_»
                             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                             " $ "
                             (Term.app `ha [(Term.hole "_") `hb]))
                            "."
                            (fieldIdx "2")))))]
                       "⟩")]))
                   [])])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                []
                (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
                []
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
                []
                (Tactic.cases
                 "cases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    `h
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`t `hb `c `hc]
                       []
                       "=>"
                       (Init.Core.«term_$_»
                        (Term.proj
                         (Term.proj
                          (Init.Core.«term_$_»
                           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                           " $ "
                           (Term.app `ha [(Term.hole "_") `hb]))
                          "."
                          (fieldIdx "1"))
                         "."
                         `trans)
                        " $ "
                        (Term.app
                         `s.fst_le_snd.trans
                         [(Term.proj
                           (Init.Core.«term_$_»
                            (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                            " $ "
                            (Term.app `ha [(Term.hole "_") `hc]))
                           "."
                           (fieldIdx "2"))]))))]))]
                 []
                 [])]))))))]
        (Term.optEllipsis [])
        []
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Interval.lattice "," `Interval.boundedOrder] "with"]
       [(Term.structInstField
         (Term.structInstLVal `sup [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`S]
           []
           "=>"
           (termDepIfThenElse
            "if"
            (Lean.binderIdent `h)
            ":"
            (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
            "then"
            (Order.BoundedOrder.«term⊥» "⊥")
            "else"
            (Term.app
             `some
             [(Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [(Order.CompleteLattice.«term⨅_,_»
                   "⨅"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinderCollection
                     [(Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `s)
                        [(group ":" (Term.app `NonemptyInterval [`α]))])
                       ")")
                      (Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `h)
                        [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                       ")")]))
                   ", "
                   (Term.proj `s "." `fst))
                  ","
                  (Order.CompleteLattice.«term⨆_,_»
                   "⨆"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinderCollection
                     [(Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `s)
                        [(group ":" (Term.app `NonemptyInterval [`α]))])
                       ")")
                      (Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `h)
                        [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                       ")")]))
                   ", "
                   (Term.proj `s "." `snd))]
                 "⟩")
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.obtain
                     "obtain"
                     [(Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                           [])]
                         "⟩")])]
                     []
                     [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                    []
                    (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
               "⟩")])))))
        ","
        (Term.structInstField
         (Term.structInstLVal `le_Sup [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`s `s `ha]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
               []
               (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
               []
               («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                    [(Term.anonymousCtor
                      "⟨"
                      [(Term.app `infi₂_le [(Term.hole "_") `ha])
                       ","
                       (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
                      "⟩")]))
                  [])])]))))))
        ","
        (Term.structInstField
         (Term.structInstLVal `Sup_le [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`s `s `ha]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
               []
               («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
               []
               (Tactic.lift
                "lift"
                `s
                "to"
                (Term.app `NonemptyInterval [`α])
                ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(Init.Core.«term_$_»
                     `le_infi₂
                     " $ "
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`c `hc]
                       []
                       "=>"
                       (Term.proj
                        (Init.Core.«term_$_»
                         (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                         " $ "
                         (Term.app `ha [(Term.hole "_") `hc]))
                        "."
                        (fieldIdx "1")))))
                    ","
                    (Init.Core.«term_$_»
                     `supr₂_le
                     " $ "
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`c `hc]
                       []
                       "=>"
                       (Term.proj
                        (Init.Core.«term_$_»
                         (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                         " $ "
                         (Term.app `ha [(Term.hole "_") `hc]))
                        "."
                        (fieldIdx "2")))))]
                   "⟩")]))]))))))
        ","
        (Term.structInstField
         (Term.structInstLVal `inf [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`S]
           []
           "=>"
           (termDepIfThenElse
            "if"
            (Lean.binderIdent `h)
            ":"
            (Init.Logic.«term_∧_»
             (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
             " ∧ "
             (Term.forall
              "∀"
              [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
              []
              ","
              (Term.arrow
               (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
               "→"
               (Term.forall
                "∀"
                [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
                []
                ","
                (Term.arrow
                 (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
                 "→"
                 (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
            "then"
            (Term.app
             `some
             [(Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [(Order.CompleteLattice.«term⨆_,_»
                   "⨆"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinderCollection
                     [(Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `s)
                        [(group ":" (Term.app `NonemptyInterval [`α]))])
                       ")")
                      (Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `h)
                        [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                       ")")]))
                   ", "
                   (Term.proj `s "." `fst))
                  ","
                  (Order.CompleteLattice.«term⨅_,_»
                   "⨅"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinderCollection
                     [(Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `s)
                        [(group ":" (Term.app `NonemptyInterval [`α]))])
                       ")")
                      (Std.ExtendedBinder.extBinderParenthesized
                       "("
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `h)
                        [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                       ")")]))
                   ", "
                   (Term.proj `s "." `snd))]
                 "⟩")
                ","
                (Init.Core.«term_$_»
                 `supr₂_le
                 " $ "
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`s `hs]
                   []
                   "=>"
                   (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
               "⟩")])
            "else"
            (Order.BoundedOrder.«term⊥» "⊥")))))
        ","
        (Term.structInstField
         (Term.structInstLVal `Inf_le [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`s `s `ha]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group
                  (Tactic.lift
                   "lift"
                   `s
                   "to"
                   (Term.app `NonemptyInterval [`α])
                   ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
                   [])
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                    [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")]))
                  [])])
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.exact "exact" `bot_le) [])])]))))))
        ","
        (Term.structInstField
         (Term.structInstLVal `le_Inf [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`S `s `ha]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
               []
               («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
               []
               (Mathlib.Tactic.splitIfs "split_ifs" [] [])
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                    [(Term.anonymousCtor
                      "⟨"
                      [(Init.Core.«term_$_»
                        `supr₂_le
                        " $ "
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`t `hb]
                          []
                          "=>"
                          (Term.proj
                           (Init.Core.«term_$_»
                            (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                            " $ "
                            (Term.app `ha [(Term.hole "_") `hb]))
                           "."
                           (fieldIdx "1")))))
                       ","
                       (Init.Core.«term_$_»
                        `le_infi₂
                        " $ "
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`t `hb]
                          []
                          "=>"
                          (Term.proj
                           (Init.Core.«term_$_»
                            (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                            " $ "
                            (Term.app `ha [(Term.hole "_") `hb]))
                           "."
                           (fieldIdx "2")))))]
                      "⟩")]))
                  [])])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
               []
               (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
               []
               (Tactic.cases
                "cases"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   `h
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`t `hb `c `hc]
                      []
                      "=>"
                      (Init.Core.«term_$_»
                       (Term.proj
                        (Term.proj
                         (Init.Core.«term_$_»
                          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                          " $ "
                          (Term.app `ha [(Term.hole "_") `hb]))
                         "."
                         (fieldIdx "1"))
                        "."
                        `trans)
                       " $ "
                       (Term.app
                        `s.fst_le_snd.trans
                        [(Term.proj
                          (Init.Core.«term_$_»
                           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                           " $ "
                           (Term.app `ha [(Term.hole "_") `hc]))
                          "."
                          (fieldIdx "2"))]))))]))]
                []
                [])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`S `s `ha]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
            []
            («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
            []
            (Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            («tactic___;_»
             (cdotTk (patternIgnore (token.«·» "·")))
             [(group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(Init.Core.«term_$_»
                     `supr₂_le
                     " $ "
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`t `hb]
                       []
                       "=>"
                       (Term.proj
                        (Init.Core.«term_$_»
                         (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                         " $ "
                         (Term.app `ha [(Term.hole "_") `hb]))
                        "."
                        (fieldIdx "1")))))
                    ","
                    (Init.Core.«term_$_»
                     `le_infi₂
                     " $ "
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`t `hb]
                       []
                       "=>"
                       (Term.proj
                        (Init.Core.«term_$_»
                         (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                         " $ "
                         (Term.app `ha [(Term.hole "_") `hb]))
                        "."
                        (fieldIdx "2")))))]
                   "⟩")]))
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
            []
            («tactic___;_»
             (cdotTk (patternIgnore (token.«·» "·")))
             [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
            []
            (Tactic.cases
             "cases"
             [(Tactic.casesTarget
               []
               (Term.app
                `h
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`t `hb `c `hc]
                   []
                   "=>"
                   (Init.Core.«term_$_»
                    (Term.proj
                     (Term.proj
                      (Init.Core.«term_$_»
                       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                       " $ "
                       (Term.app `ha [(Term.hole "_") `hb]))
                      "."
                      (fieldIdx "1"))
                     "."
                     `trans)
                    " $ "
                    (Term.app
                     `s.fst_le_snd.trans
                     [(Term.proj
                       (Init.Core.«term_$_»
                        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                        " $ "
                        (Term.app `ha [(Term.hole "_") `hc]))
                       "."
                       (fieldIdx "2"))]))))]))]
             []
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
          []
          («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
          []
          (Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
               [(Term.anonymousCtor
                 "⟨"
                 [(Init.Core.«term_$_»
                   `supr₂_le
                   " $ "
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`t `hb]
                     []
                     "=>"
                     (Term.proj
                      (Init.Core.«term_$_»
                       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                       " $ "
                       (Term.app `ha [(Term.hole "_") `hb]))
                      "."
                      (fieldIdx "1")))))
                  ","
                  (Init.Core.«term_$_»
                   `le_infi₂
                   " $ "
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`t `hb]
                     []
                     "=>"
                     (Term.proj
                      (Init.Core.«term_$_»
                       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                       " $ "
                       (Term.app `ha [(Term.hole "_") `hb]))
                      "."
                      (fieldIdx "2")))))]
                 "⟩")]))
             [])])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
          []
          (Tactic.cases
           "cases"
           [(Tactic.casesTarget
             []
             (Term.app
              `h
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`t `hb `c `hc]
                 []
                 "=>"
                 (Init.Core.«term_$_»
                  (Term.proj
                   (Term.proj
                    (Init.Core.«term_$_»
                     (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                     " $ "
                     (Term.app `ha [(Term.hole "_") `hb]))
                    "."
                    (fieldIdx "1"))
                   "."
                   `trans)
                  " $ "
                  (Term.app
                   `s.fst_le_snd.trans
                   [(Term.proj
                     (Init.Core.«term_$_»
                      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                      " $ "
                      (Term.app `ha [(Term.hole "_") `hc]))
                     "."
                     (fieldIdx "2"))]))))]))]
           []
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases
       "cases"
       [(Tactic.casesTarget
         []
         (Term.app
          `h
          [(Term.fun
            "fun"
            (Term.basicFun
             [`t `hb `c `hc]
             []
             "=>"
             (Init.Core.«term_$_»
              (Term.proj
               (Term.proj
                (Init.Core.«term_$_»
                 (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                 " $ "
                 (Term.app `ha [(Term.hole "_") `hb]))
                "."
                (fieldIdx "1"))
               "."
               `trans)
              " $ "
              (Term.app
               `s.fst_le_snd.trans
               [(Term.proj
                 (Init.Core.«term_$_»
                  (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                  " $ "
                  (Term.app `ha [(Term.hole "_") `hc]))
                 "."
                 (fieldIdx "2"))]))))]))]
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t `hb `c `hc]
          []
          "=>"
          (Init.Core.«term_$_»
           (Term.proj
            (Term.proj
             (Init.Core.«term_$_»
              (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
              " $ "
              (Term.app `ha [(Term.hole "_") `hb]))
             "."
             (fieldIdx "1"))
            "."
            `trans)
           " $ "
           (Term.app
            `s.fst_le_snd.trans
            [(Term.proj
              (Init.Core.«term_$_»
               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
               " $ "
               (Term.app `ha [(Term.hole "_") `hc]))
              "."
              (fieldIdx "2"))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t `hb `c `hc]
        []
        "=>"
        (Init.Core.«term_$_»
         (Term.proj
          (Term.proj
           (Init.Core.«term_$_»
            (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
            " $ "
            (Term.app `ha [(Term.hole "_") `hb]))
           "."
           (fieldIdx "1"))
          "."
          `trans)
         " $ "
         (Term.app
          `s.fst_le_snd.trans
          [(Term.proj
            (Init.Core.«term_$_»
             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
             " $ "
             (Term.app `ha [(Term.hole "_") `hc]))
            "."
            (fieldIdx "2"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_»
       (Term.proj
        (Term.proj
         (Init.Core.«term_$_»
          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
          " $ "
          (Term.app `ha [(Term.hole "_") `hb]))
         "."
         (fieldIdx "1"))
        "."
        `trans)
       " $ "
       (Term.app
        `s.fst_le_snd.trans
        [(Term.proj
          (Init.Core.«term_$_»
           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
           " $ "
           (Term.app `ha [(Term.hole "_") `hc]))
          "."
          (fieldIdx "2"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `s.fst_le_snd.trans
       [(Term.proj
         (Init.Core.«term_$_»
          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
          " $ "
          (Term.app `ha [(Term.hole "_") `hc]))
         "."
         (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Init.Core.«term_$_»
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
        " $ "
        (Term.app `ha [(Term.hole "_") `hc]))
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Init.Core.«term_$_»
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
       " $ "
       (Term.app `ha [(Term.hole "_") `hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Core.«term_$_» (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1")) " $ " (Term.app `ha [(Term.hole "_") `hc]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `s.fst_le_snd.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      (Term.proj
       (Term.proj
        (Init.Core.«term_$_»
         (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
         " $ "
         (Term.app `ha [(Term.hole "_") `hb]))
        "."
        (fieldIdx "1"))
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Init.Core.«term_$_»
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
        " $ "
        (Term.app `ha [(Term.hole "_") `hb]))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Init.Core.«term_$_»
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
       " $ "
       (Term.app `ha [(Term.hole "_") `hb]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Core.«term_$_» (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1")) " $ " (Term.app `ha [(Term.hole "_") `hb]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `ha [(Term.hole "_") `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_and_or) "," (Tactic.rwRule [] `not_not)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_and_or
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.exact
          "exact"
          (Term.app
           (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
           [(Term.anonymousCtor
             "⟨"
             [(Init.Core.«term_$_»
               `supr₂_le
               " $ "
               (Term.fun
                "fun"
                (Term.basicFun
                 [`t `hb]
                 []
                 "=>"
                 (Term.proj
                  (Init.Core.«term_$_»
                   (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                   " $ "
                   (Term.app `ha [(Term.hole "_") `hb]))
                  "."
                  (fieldIdx "1")))))
              ","
              (Init.Core.«term_$_»
               `le_infi₂
               " $ "
               (Term.fun
                "fun"
                (Term.basicFun
                 [`t `hb]
                 []
                 "=>"
                 (Term.proj
                  (Init.Core.«term_$_»
                   (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                   " $ "
                   (Term.app `ha [(Term.hole "_") `hb]))
                  "."
                  (fieldIdx "2")))))]
             "⟩")]))
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Init.Core.«term_$_»
            `supr₂_le
            " $ "
            (Term.fun
             "fun"
             (Term.basicFun
              [`t `hb]
              []
              "=>"
              (Term.proj
               (Init.Core.«term_$_»
                (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                " $ "
                (Term.app `ha [(Term.hole "_") `hb]))
               "."
               (fieldIdx "1")))))
           ","
           (Init.Core.«term_$_»
            `le_infi₂
            " $ "
            (Term.fun
             "fun"
             (Term.basicFun
              [`t `hb]
              []
              "=>"
              (Term.proj
               (Init.Core.«term_$_»
                (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                " $ "
                (Term.app `ha [(Term.hole "_") `hb]))
               "."
               (fieldIdx "2")))))]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
       [(Term.anonymousCtor
         "⟨"
         [(Init.Core.«term_$_»
           `supr₂_le
           " $ "
           (Term.fun
            "fun"
            (Term.basicFun
             [`t `hb]
             []
             "=>"
             (Term.proj
              (Init.Core.«term_$_»
               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
               " $ "
               (Term.app `ha [(Term.hole "_") `hb]))
              "."
              (fieldIdx "1")))))
          ","
          (Init.Core.«term_$_»
           `le_infi₂
           " $ "
           (Term.fun
            "fun"
            (Term.basicFun
             [`t `hb]
             []
             "=>"
             (Term.proj
              (Init.Core.«term_$_»
               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
               " $ "
               (Term.app `ha [(Term.hole "_") `hb]))
              "."
              (fieldIdx "2")))))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Init.Core.«term_$_»
         `supr₂_le
         " $ "
         (Term.fun
          "fun"
          (Term.basicFun
           [`t `hb]
           []
           "=>"
           (Term.proj
            (Init.Core.«term_$_»
             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
             " $ "
             (Term.app `ha [(Term.hole "_") `hb]))
            "."
            (fieldIdx "1")))))
        ","
        (Init.Core.«term_$_»
         `le_infi₂
         " $ "
         (Term.fun
          "fun"
          (Term.basicFun
           [`t `hb]
           []
           "=>"
           (Term.proj
            (Init.Core.«term_$_»
             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
             " $ "
             (Term.app `ha [(Term.hole "_") `hb]))
            "."
            (fieldIdx "2")))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_»
       `le_infi₂
       " $ "
       (Term.fun
        "fun"
        (Term.basicFun
         [`t `hb]
         []
         "=>"
         (Term.proj
          (Init.Core.«term_$_»
           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
           " $ "
           (Term.app `ha [(Term.hole "_") `hb]))
          "."
          (fieldIdx "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t `hb]
        []
        "=>"
        (Term.proj
         (Init.Core.«term_$_»
          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
          " $ "
          (Term.app `ha [(Term.hole "_") `hb]))
         "."
         (fieldIdx "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Init.Core.«term_$_»
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
        " $ "
        (Term.app `ha [(Term.hole "_") `hb]))
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Init.Core.«term_$_»
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
       " $ "
       (Term.app `ha [(Term.hole "_") `hb]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Core.«term_$_» (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1")) " $ " (Term.app `ha [(Term.hole "_") `hb]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      `le_infi₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_»
       `supr₂_le
       " $ "
       (Term.fun
        "fun"
        (Term.basicFun
         [`t `hb]
         []
         "=>"
         (Term.proj
          (Init.Core.«term_$_»
           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
           " $ "
           (Term.app `ha [(Term.hole "_") `hb]))
          "."
          (fieldIdx "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t `hb]
        []
        "=>"
        (Term.proj
         (Init.Core.«term_$_»
          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
          " $ "
          (Term.app `ha [(Term.hole "_") `hb]))
         "."
         (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Init.Core.«term_$_»
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
        " $ "
        (Term.app `ha [(Term.hole "_") `hb]))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Init.Core.«term_$_»
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
       " $ "
       (Term.app `ha [(Term.hole "_") `hb]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Core.«term_$_» (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1")) " $ " (Term.app `ha [(Term.hole "_") `hb]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      `supr₂_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.some_le_some
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `bot_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bot_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s `s `ha]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            («tactic___;_»
             (cdotTk (patternIgnore (token.«·» "·")))
             [(group
               (Tactic.lift
                "lift"
                `s
                "to"
                (Term.app `NonemptyInterval [`α])
                ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
                 [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")]))
               [])])
            []
            («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.lift
              "lift"
              `s
              "to"
              (Term.app `NonemptyInterval [`α])
              ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
               [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")]))
             [])])
          []
          («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `bot_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bot_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.lift
          "lift"
          `s
          "to"
          (Term.app `NonemptyInterval [`α])
          ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
          [])
         [])
        (group
         (Tactic.exact
          "exact"
          (Term.app
           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
           [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")]))
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
        [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
       [(Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `le_supr₂ [`s `ha]) "," (Term.app `infi₂_le [`s `ha])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `infi₂_le [`s `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infi₂_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_supr₂ [`s `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_supr₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.lift
       "lift"
       `s
       "to"
       (Term.app `NonemptyInterval [`α])
       ["using" (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_of_mem_of_not_mem [`ha (Term.proj `h "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_mem_of_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`S]
        []
        "=>"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `h)
         ":"
         (Init.Logic.«term_∧_»
          (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
          " ∧ "
          (Term.forall
           "∀"
           [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
           []
           ","
           (Term.arrow
            (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
            "→"
            (Term.forall
             "∀"
             [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
             []
             ","
             (Term.arrow
              (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
              "→"
              (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
         "then"
         (Term.app
          `some
          [(Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor
              "⟨"
              [(Order.CompleteLattice.«term⨆_,_»
                "⨆"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinderCollection
                  [(Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                    ")")
                   (Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `h)
                     [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                    ")")]))
                ", "
                (Term.proj `s "." `fst))
               ","
               (Order.CompleteLattice.«term⨅_,_»
                "⨅"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinderCollection
                  [(Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                    ")")
                   (Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `h)
                     [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                    ")")]))
                ", "
                (Term.proj `s "." `snd))]
              "⟩")
             ","
             (Init.Core.«term_$_»
              `supr₂_le
              " $ "
              (Term.fun
               "fun"
               (Term.basicFun
                [`s `hs]
                []
                "=>"
                (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
            "⟩")])
         "else"
         (Order.BoundedOrder.«term⊥» "⊥"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h)
       ":"
       (Init.Logic.«term_∧_»
        (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
        " ∧ "
        (Term.forall
         "∀"
         [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
         []
         ","
         (Term.arrow
          (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
          "→"
          (Term.forall
           "∀"
           [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
           []
           ","
           (Term.arrow
            (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
            "→"
            (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
       "then"
       (Term.app
        `some
        [(Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinderCollection
                [(Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                  ")")
                 (Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `h)
                   [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                  ")")]))
              ", "
              (Term.proj `s "." `fst))
             ","
             (Order.CompleteLattice.«term⨅_,_»
              "⨅"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinderCollection
                [(Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                  ")")
                 (Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `h)
                   [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                  ")")]))
              ", "
              (Term.proj `s "." `snd))]
            "⟩")
           ","
           (Init.Core.«term_$_»
            `supr₂_le
            " $ "
            (Term.fun
             "fun"
             (Term.basicFun
              [`s `hs]
              []
              "=>"
              (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
          "⟩")])
       "else"
       (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `some
       [(Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Order.CompleteLattice.«term⨆_,_»
             "⨆"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinderCollection
               [(Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                 ")")
                (Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `h)
                  [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                 ")")]))
             ", "
             (Term.proj `s "." `fst))
            ","
            (Order.CompleteLattice.«term⨅_,_»
             "⨅"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinderCollection
               [(Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                 ")")
                (Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `h)
                  [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                 ")")]))
             ", "
             (Term.proj `s "." `snd))]
           "⟩")
          ","
          (Init.Core.«term_$_»
           `supr₂_le
           " $ "
           (Term.fun
            "fun"
            (Term.basicFun
             [`s `hs]
             []
             "=>"
             (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Order.CompleteLattice.«term⨆_,_»
           "⨆"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinderCollection
             [(Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
               ")")
              (Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `h)
                [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
               ")")]))
           ", "
           (Term.proj `s "." `fst))
          ","
          (Order.CompleteLattice.«term⨅_,_»
           "⨅"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinderCollection
             [(Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
               ")")
              (Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `h)
                [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
               ")")]))
           ", "
           (Term.proj `s "." `snd))]
         "⟩")
        ","
        (Init.Core.«term_$_»
         `supr₂_le
         " $ "
         (Term.fun
          "fun"
          (Term.basicFun
           [`s `hs]
           []
           "=>"
           (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_»
       `supr₂_le
       " $ "
       (Term.fun
        "fun"
        (Term.basicFun
         [`s `hs]
         []
         "=>"
         (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s `hs]
        []
        "=>"
        (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_» `le_infi₂ " $ " (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `h "." (fieldIdx "2")) [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      `le_infi₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      `supr₂_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Order.CompleteLattice.«term⨆_,_»
         "⨆"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinderCollection
           [(Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
             ")")
            (Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `h)
              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
             ")")]))
         ", "
         (Term.proj `s "." `fst))
        ","
        (Order.CompleteLattice.«term⨅_,_»
         "⨅"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinderCollection
           [(Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
             ")")
            (Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `h)
              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
             ")")]))
         ", "
         (Term.proj `s "." `snd))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨅_,_»
       "⨅"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinderCollection
         [(Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
           ")")
          (Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `h)
            [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
           ")")]))
       ", "
       (Term.proj `s "." `snd))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `s "." `snd)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.ExtendedBinder.extBinderCollection', expected 'Std.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term↑_» "↑" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨆_,_»
       "⨆"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinderCollection
         [(Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
           ")")
          (Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `h)
            [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
           ")")]))
       ", "
       (Term.proj `s "." `fst))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `s "." `fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.ExtendedBinder.extBinderCollection', expected 'Std.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term↑_» "↑" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Logic.«term_∧_»
       (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
       " ∧ "
       (Term.forall
        "∀"
        [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
        []
        ","
        (Term.arrow
         (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
         "→"
         (Term.forall
          "∀"
          [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
          []
          ","
          (Term.arrow
           (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
           "→"
           (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.strictImplicitBinder "⦃" [`s] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
       []
       ","
       (Term.arrow
        (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
        "→"
        (Term.forall
         "∀"
         [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
         []
         ","
         (Term.arrow
          (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
          "→"
          (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
       "→"
       (Term.forall
        "∀"
        [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
        []
        ","
        (Term.arrow
         (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
         "→"
         (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.strictImplicitBinder "⦃" [`t] [":" (Term.app `NonemptyInterval [`α])] "⦄")]
       []
       ","
       (Term.arrow
        (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
        "→"
        (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
       "→"
       (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_≤_» (Term.proj `s "." `fst) " ≤ " (Term.proj `t "." `snd))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `t "." `snd)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj `s "." `fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `t) " ∈ " `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term↑_» "↑" `t)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.strictImplicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.strictImplicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.strictImplicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⦄»', expected 'group'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⦃»', expected 'group'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term↑_» "↑" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.strictImplicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.strictImplicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.strictImplicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⦄»', expected 'group'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⦃»', expected 'group'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Init.Core.«term_∉_» (Order.BoundedOrder.«term⊥» "⊥") " ∉ " `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 50, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s `s `ha]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
            []
            (Tactic.lift
             "lift"
             `s
             "to"
             (Term.app `NonemptyInterval [`α])
             ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
              [(Term.anonymousCtor
                "⟨"
                [(Init.Core.«term_$_»
                  `le_infi₂
                  " $ "
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`c `hc]
                    []
                    "=>"
                    (Term.proj
                     (Init.Core.«term_$_»
                      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                      " $ "
                      (Term.app `ha [(Term.hole "_") `hc]))
                     "."
                     (fieldIdx "1")))))
                 ","
                 (Init.Core.«term_$_»
                  `supr₂_le
                  " $ "
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`c `hc]
                    []
                    "=>"
                    (Term.proj
                     (Init.Core.«term_$_»
                      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                      " $ "
                      (Term.app `ha [(Term.hole "_") `hc]))
                     "."
                     (fieldIdx "2")))))]
                "⟩")]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
          []
          (Tactic.lift
           "lift"
           `s
           "to"
           (Term.app `NonemptyInterval [`α])
           ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
            [(Term.anonymousCtor
              "⟨"
              [(Init.Core.«term_$_»
                `le_infi₂
                " $ "
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`c `hc]
                  []
                  "=>"
                  (Term.proj
                   (Init.Core.«term_$_»
                    (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                    " $ "
                    (Term.app `ha [(Term.hole "_") `hc]))
                   "."
                   (fieldIdx "1")))))
               ","
               (Init.Core.«term_$_»
                `supr₂_le
                " $ "
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`c `hc]
                  []
                  "=>"
                  (Term.proj
                   (Init.Core.«term_$_»
                    (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                    " $ "
                    (Term.app `ha [(Term.hole "_") `hc]))
                   "."
                   (fieldIdx "2")))))]
              "⟩")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Init.Core.«term_$_»
            `le_infi₂
            " $ "
            (Term.fun
             "fun"
             (Term.basicFun
              [`c `hc]
              []
              "=>"
              (Term.proj
               (Init.Core.«term_$_»
                (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                " $ "
                (Term.app `ha [(Term.hole "_") `hc]))
               "."
               (fieldIdx "1")))))
           ","
           (Init.Core.«term_$_»
            `supr₂_le
            " $ "
            (Term.fun
             "fun"
             (Term.basicFun
              [`c `hc]
              []
              "=>"
              (Term.proj
               (Init.Core.«term_$_»
                (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
                " $ "
                (Term.app `ha [(Term.hole "_") `hc]))
               "."
               (fieldIdx "2")))))]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
       [(Term.anonymousCtor
         "⟨"
         [(Init.Core.«term_$_»
           `le_infi₂
           " $ "
           (Term.fun
            "fun"
            (Term.basicFun
             [`c `hc]
             []
             "=>"
             (Term.proj
              (Init.Core.«term_$_»
               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
               " $ "
               (Term.app `ha [(Term.hole "_") `hc]))
              "."
              (fieldIdx "1")))))
          ","
          (Init.Core.«term_$_»
           `supr₂_le
           " $ "
           (Term.fun
            "fun"
            (Term.basicFun
             [`c `hc]
             []
             "=>"
             (Term.proj
              (Init.Core.«term_$_»
               (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
               " $ "
               (Term.app `ha [(Term.hole "_") `hc]))
              "."
              (fieldIdx "2")))))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Init.Core.«term_$_»
         `le_infi₂
         " $ "
         (Term.fun
          "fun"
          (Term.basicFun
           [`c `hc]
           []
           "=>"
           (Term.proj
            (Init.Core.«term_$_»
             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
             " $ "
             (Term.app `ha [(Term.hole "_") `hc]))
            "."
            (fieldIdx "1")))))
        ","
        (Init.Core.«term_$_»
         `supr₂_le
         " $ "
         (Term.fun
          "fun"
          (Term.basicFun
           [`c `hc]
           []
           "=>"
           (Term.proj
            (Init.Core.«term_$_»
             (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
             " $ "
             (Term.app `ha [(Term.hole "_") `hc]))
            "."
            (fieldIdx "2")))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_»
       `supr₂_le
       " $ "
       (Term.fun
        "fun"
        (Term.basicFun
         [`c `hc]
         []
         "=>"
         (Term.proj
          (Init.Core.«term_$_»
           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
           " $ "
           (Term.app `ha [(Term.hole "_") `hc]))
          "."
          (fieldIdx "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`c `hc]
        []
        "=>"
        (Term.proj
         (Init.Core.«term_$_»
          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
          " $ "
          (Term.app `ha [(Term.hole "_") `hc]))
         "."
         (fieldIdx "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Init.Core.«term_$_»
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
        " $ "
        (Term.app `ha [(Term.hole "_") `hc]))
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Init.Core.«term_$_»
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
       " $ "
       (Term.app `ha [(Term.hole "_") `hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Core.«term_$_» (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1")) " $ " (Term.app `ha [(Term.hole "_") `hc]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      `supr₂_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_»
       `le_infi₂
       " $ "
       (Term.fun
        "fun"
        (Term.basicFun
         [`c `hc]
         []
         "=>"
         (Term.proj
          (Init.Core.«term_$_»
           (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
           " $ "
           (Term.app `ha [(Term.hole "_") `hc]))
          "."
          (fieldIdx "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`c `hc]
        []
        "=>"
        (Term.proj
         (Init.Core.«term_$_»
          (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
          " $ "
          (Term.app `ha [(Term.hole "_") `hc]))
         "."
         (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Init.Core.«term_$_»
        (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
        " $ "
        (Term.app `ha [(Term.hole "_") `hc]))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Init.Core.«term_$_»
       (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
       " $ "
       (Term.app `ha [(Term.hole "_") `hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Core.«term_$_» (Term.proj `WithBot.coe_le_coe "." (fieldIdx "1")) " $ " (Term.app `ha [(Term.hole "_") `hc]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      `le_infi₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `WithBot.coe_le_coe "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.coe_le_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.lift
       "lift"
       `s
       "to"
       (Term.app `NonemptyInterval [`α])
       ["using" (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_bot_of_le_ne_bot [`hb (Term.app `ha [(Term.hole "_") `hs])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(Term.hole "_") `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ha [(Term.hole "_") `hs]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_bot_of_le_ne_bot
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)]) [])]
           "⟩")])]
       []
       [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `not_subset "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_subset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `bot_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bot_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s `s `ha]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            («tactic___;_»
             (cdotTk (patternIgnore (token.«·» "·")))
             [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
            []
            («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
            []
            («tactic___;_»
             (cdotTk (patternIgnore (token.«·» "·")))
             [(group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.app `infi₂_le [(Term.hole "_") `ha])
                    ","
                    (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
                   "⟩")]))
               [])])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
          []
          (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
          []
          («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.app `infi₂_le [(Term.hole "_") `ha])
                  ","
                  (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
                 "⟩")]))
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.exact
          "exact"
          (Term.app
           (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
           [(Term.anonymousCtor
             "⟨"
             [(Term.app `infi₂_le [(Term.hole "_") `ha]) "," (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
             "⟩")]))
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Term.app `infi₂_le [(Term.hole "_") `ha]) "," (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
       [(Term.anonymousCtor
         "⟨"
         [(Term.app `infi₂_le [(Term.hole "_") `ha]) "," (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `infi₂_le [(Term.hole "_") `ha]) "," (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_supr₂_of_le [(Term.hole "_") `ha `le_rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_supr₂_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `infi₂_le [(Term.hole "_") `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infi₂_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `WithBot.some_le_some "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `WithBot.some_le_some
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_» (cdotTk (patternIgnore (token.«·» "·"))) [(group (Tactic.exact "exact" `bot_le) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `bot_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bot_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `s)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le)) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.app `h [`ha]) "." `le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `h [`ha]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`ha]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`S]
        []
        "=>"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `h)
         ":"
         (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
         "then"
         (Order.BoundedOrder.«term⊥» "⊥")
         "else"
         (Term.app
          `some
          [(Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor
              "⟨"
              [(Order.CompleteLattice.«term⨅_,_»
                "⨅"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinderCollection
                  [(Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                    ")")
                   (Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `h)
                     [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                    ")")]))
                ", "
                (Term.proj `s "." `fst))
               ","
               (Order.CompleteLattice.«term⨆_,_»
                "⨆"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinderCollection
                  [(Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                    ")")
                   (Std.ExtendedBinder.extBinderParenthesized
                    "("
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `h)
                     [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                    ")")]))
                ", "
                (Term.proj `s "." `snd))]
              "⟩")
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
                 []
                 (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
            "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h)
       ":"
       (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
       "then"
       (Order.BoundedOrder.«term⊥» "⊥")
       "else"
       (Term.app
        `some
        [(Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Order.CompleteLattice.«term⨅_,_»
              "⨅"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinderCollection
                [(Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                  ")")
                 (Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `h)
                   [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                  ")")]))
              ", "
              (Term.proj `s "." `fst))
             ","
             (Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinderCollection
                [(Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                  ")")
                 (Std.ExtendedBinder.extBinderParenthesized
                  "("
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `h)
                   [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                  ")")]))
              ", "
              (Term.proj `s "." `snd))]
            "⟩")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
               []
               (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
               []
               (Tactic.exact
                "exact"
                (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `some
       [(Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Order.CompleteLattice.«term⨅_,_»
             "⨅"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinderCollection
               [(Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                 ")")
                (Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `h)
                  [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                 ")")]))
             ", "
             (Term.proj `s "." `fst))
            ","
            (Order.CompleteLattice.«term⨆_,_»
             "⨆"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinderCollection
               [(Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
                 ")")
                (Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `h)
                  [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
                 ")")]))
             ", "
             (Term.proj `s "." `snd))]
           "⟩")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                     [])]
                   "⟩")])]
               []
               [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
              []
              (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
              []
              (Tactic.exact
               "exact"
               (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Order.CompleteLattice.«term⨅_,_»
           "⨅"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinderCollection
             [(Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
               ")")
              (Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `h)
                [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
               ")")]))
           ", "
           (Term.proj `s "." `fst))
          ","
          (Order.CompleteLattice.«term⨆_,_»
           "⨆"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinderCollection
             [(Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
               ")")
              (Std.ExtendedBinder.extBinderParenthesized
               "("
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `h)
                [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
               ")")]))
           ", "
           (Term.proj `s "." `snd))]
         "⟩")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
            []
            (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
            []
            (Tactic.exact
             "exact"
             (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
          []
          (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
          []
          (Tactic.exact
           "exact"
           (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `infi₂_le_of_le [`s `hs (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s.fst_le_snd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_supr₂_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_supr₂_of_le [`s `hs `s.fst_le_snd]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infi₂_le_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.lift "lift" `s "to" (Term.app `NonemptyInterval [`α]) ["using" `ha] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)]) [])]
           "⟩")])]
       []
       [":=" [(Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `not_subset "." (fieldIdx "1")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `not_subset "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_subset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Order.CompleteLattice.«term⨅_,_»
         "⨅"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinderCollection
           [(Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
             ")")
            (Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `h)
              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
             ")")]))
         ", "
         (Term.proj `s "." `fst))
        ","
        (Order.CompleteLattice.«term⨆_,_»
         "⨆"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinderCollection
           [(Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
             ")")
            (Std.ExtendedBinder.extBinderParenthesized
             "("
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `h)
              [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
             ")")]))
         ", "
         (Term.proj `s "." `snd))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨆_,_»
       "⨆"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinderCollection
         [(Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
           ")")
          (Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `h)
            [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
           ")")]))
       ", "
       (Term.proj `s "." `snd))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `s "." `snd)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.ExtendedBinder.extBinderCollection', expected 'Std.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term↑_» "↑" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.CompleteLattice.«term⨅_,_»
       "⨅"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinderCollection
         [(Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `NonemptyInterval [`α]))])
           ")")
          (Std.ExtendedBinder.extBinderParenthesized
           "("
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `h)
            [(group ":" (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S))])
           ")")]))
       ", "
       (Term.proj `s "." `fst))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `s "." `fst)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.ExtendedBinder.extBinderCollection', expected 'Std.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_∈_» (Init.Coe.«term↑_» "↑" `s) " ∈ " `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term↑_» "↑" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NonemptyInterval [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NonemptyInterval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_⊆_» `S " ⊆ " («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [(Order.BoundedOrder.«term⊥» "⊥")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `S
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Interval.boundedOrder
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Interval.lattice
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
noncomputable
  instance
    [ @ DecidableRel α ( · ≤ · ) ] : CompleteLattice Interval α
    :=
      by
        skip
          <;>
          exact
            {
              Interval.lattice , Interval.boundedOrder with
              sup
                  :=
                  fun
                    S
                      =>
                      if
                        h
                        :
                        S ⊆ { ⊥ }
                        then
                        ⊥
                        else
                        some
                          ⟨
                            ⟨
                                ⨅ ( s : NonemptyInterval α ) ( h : ↑ s ∈ S ) , s . fst
                                  ,
                                  ⨆ ( s : NonemptyInterval α ) ( h : ↑ s ∈ S ) , s . snd
                                ⟩
                              ,
                              by
                                obtain ⟨ s , hs , ha ⟩ := not_subset . 1 h
                                  lift s to NonemptyInterval α using ha
                                  exact infi₂_le_of_le s hs le_supr₂_of_le s hs s.fst_le_snd
                            ⟩
                ,
                le_Sup
                  :=
                  fun
                    s s ha
                      =>
                      by
                        split_ifs
                          · exact h ha . le
                          cases s
                          · exact bot_le
                          · exact WithBot.some_le_some . 2 ⟨ infi₂_le _ ha , le_supr₂_of_le _ ha le_rfl ⟩
                ,
                Sup_le
                  :=
                  fun
                    s s ha
                      =>
                      by
                        split_ifs
                          · exact bot_le
                          obtain ⟨ b , hs , hb ⟩ := not_subset . 1 h
                          lift s to NonemptyInterval α using ne_bot_of_le_ne_bot hb ha _ hs
                          exact
                            WithBot.coe_le_coe . 2
                              ⟨
                                le_infi₂ $ fun c hc => WithBot.coe_le_coe . 1 $ ha _ hc . 1
                                  ,
                                  supr₂_le $ fun c hc => WithBot.coe_le_coe . 1 $ ha _ hc . 2
                                ⟩
                ,
                inf
                  :=
                  fun
                    S
                      =>
                      if
                        h
                        :
                        ⊥ ∉ S
                          ∧
                          ∀
                            ⦃ s : NonemptyInterval α ⦄
                            ,
                            ↑ s ∈ S → ∀ ⦃ t : NonemptyInterval α ⦄ , ↑ t ∈ S → s . fst ≤ t . snd
                        then
                        some
                          ⟨
                            ⟨
                                ⨆ ( s : NonemptyInterval α ) ( h : ↑ s ∈ S ) , s . fst
                                  ,
                                  ⨅ ( s : NonemptyInterval α ) ( h : ↑ s ∈ S ) , s . snd
                                ⟩
                              ,
                              supr₂_le $ fun s hs => le_infi₂ $ h . 2 hs
                            ⟩
                        else
                        ⊥
                ,
                Inf_le
                  :=
                  fun
                    s s ha
                      =>
                      by
                        split_ifs
                          ·
                            lift s to NonemptyInterval α using ne_of_mem_of_not_mem ha h . 1
                              exact WithBot.coe_le_coe . 2 ⟨ le_supr₂ s ha , infi₂_le s ha ⟩
                          · exact bot_le
                ,
                le_Inf
                  :=
                  fun
                    S s ha
                      =>
                      by
                        cases s
                          · exact bot_le
                          split_ifs
                          ·
                            exact
                              WithBot.some_le_some . 2
                                ⟨
                                  supr₂_le $ fun t hb => WithBot.coe_le_coe . 1 $ ha _ hb . 1
                                    ,
                                    le_infi₂ $ fun t hb => WithBot.coe_le_coe . 1 $ ha _ hb . 2
                                  ⟩
                          rw [ not_and_or , not_not ] at h
                          cases h
                          · exact ha _ h
                          cases
                            h
                              fun
                                t hb c hc
                                  =>
                                  WithBot.coe_le_coe . 1 $ ha _ hb . 1 . trans
                                    $
                                    s.fst_le_snd.trans WithBot.coe_le_coe . 1 $ ha _ hc . 2
              }

@[simp, norm_cast]
theorem coe_Inf (S : Set (Interval α)) : ↑(inf S) = ⋂ s ∈ S, (s : Set α) := by
  change coe (dite _ _ _) = _
  split_ifs
  · ext
    simp [WithBot.some_eq_coe, Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
    
  simp_rw [not_and_or, not_not] at h
  cases h
  · refine' (eq_empty_of_subset_empty _).symm
    exact Inter₂_subset_of_subset _ h subset.rfl
    
  · refine' (not_nonempty_iff_eq_empty.1 _).symm
    rintro ⟨x, hx⟩
    rw [mem_Inter₂] at hx
    exact h fun s ha t hb => (hx _ ha).1.trans (hx _ hb).2
    
#align interval.coe_Inf Interval.coe_Inf

@[simp, norm_cast]
theorem coe_infi (f : ι → Interval α) : ↑(⨅ i, f i) = ⋂ i, (f i : Set α) := by simp [infi]
#align interval.coe_infi Interval.coe_infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_infi₂ (f : ∀ i, κ i → Interval α) : ↑(⨅ (i) (j), f i j) = ⋂ (i) (j), (f i j : Set α) := by
  simp_rw [coe_infi]
#align interval.coe_infi₂ Interval.coe_infi₂

end CompleteLattice

end Interval

