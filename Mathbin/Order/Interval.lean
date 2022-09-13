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
@[ext]
structure NonemptyInterval (α : Type _) [LE α] extends α × α where
  fst_le_snd : fst ≤ snd

namespace NonemptyInterval

section LE

variable [LE α] {s t : NonemptyInterval α}

/-- The injection that induces the order on intervals. -/
def toDualProd : NonemptyInterval α → αᵒᵈ × α :=
  to_prod

@[simp]
theorem to_dual_prod_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, s.snd) :=
  Prod.mk.etaₓ.symm

theorem to_dual_prod_injective : Injective (toDualProd : NonemptyInterval α → αᵒᵈ × α) := fun s t => (ext_iff _ _).2

instance [IsEmpty α] : IsEmpty (NonemptyInterval α) :=
  ⟨fun s => isEmptyElim s.fst⟩

instance [Subsingleton α] : Subsingleton (NonemptyInterval α) :=
  to_dual_prod_injective.Subsingleton

instance : LE (NonemptyInterval α) :=
  ⟨fun s t => t.fst ≤ s.fst ∧ s.snd ≤ t.snd⟩

theorem le_def : s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd :=
  Iff.rfl

/-- `to_dual_prod` as an order embedding. -/
@[simps]
def toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α where
  toFun := toDualProd
  inj' := to_dual_prod_injective
  map_rel_iff' := fun _ _ => Iff.rfl

/-- Turn an interval into an interval in the dual order. -/
def dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ where
  toFun := fun s => ⟨s.toProd.swap, s.fst_le_snd⟩
  invFun := fun s => ⟨s.toProd.swap, s.fst_le_snd⟩
  left_inv := fun s => ext _ _ <| Prod.swap_swapₓ _
  right_inv := fun s => ext _ _ <| Prod.swap_swapₓ _

@[simp]
theorem fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd :=
  rfl

@[simp]
theorem snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst :=
  rfl

end LE

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ]

instance : Preorderₓ (NonemptyInterval α) :=
  Preorderₓ.lift toDualProd

/-- `{a}` as an interval. -/
@[simps]
def pure (a : α) : NonemptyInterval α :=
  ⟨⟨a, a⟩, le_rflₓ⟩

theorem pure_injective : Injective (pure : α → NonemptyInterval α) := fun s t => congr_arg <| Prod.fst ∘ to_prod

@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl

instance [Inhabited α] : Inhabited (NonemptyInterval α) :=
  ⟨pure default⟩

instance : ∀ [Nonempty α], Nonempty (NonemptyInterval α) :=
  Nonempty.mapₓ pure

instance [Nontrivial α] : Nontrivial (NonemptyInterval α) :=
  pure_injective.Nontrivial

/-- Pushforward of nonempty intervals. -/
@[simps]
def map (f : α →o β) (a : NonemptyInterval α) : NonemptyInterval β :=
  ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩

@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl

@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (a : NonemptyInterval α) : (a.map f).map g = a.map (g.comp f) :=
  rfl

@[simp]
theorem dual_map (f : α →o β) (a : NonemptyInterval α) : (a.map f).dual = a.dual.map f.dual :=
  rfl

variable [BoundedOrder α]

instance : OrderTop (NonemptyInterval α) where
  top := ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top := fun a => ⟨bot_le, le_top⟩

@[simp]
theorem dual_top : (⊤ : NonemptyInterval α).dual = ⊤ :=
  rfl

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {s t : NonemptyInterval α} {x : α × α} {a : α}

instance : PartialOrderₓ (NonemptyInterval α) :=
  PartialOrderₓ.lift _ to_dual_prod_injective

/-- Consider a nonempty interval `[a, b]` as the set `[a, b]`. -/
def coeHom : NonemptyInterval α ↪o Set α :=
  OrderEmbedding.ofMapLeIff (fun s => Icc s.fst s.snd) fun s t => Icc_subset_Icc_iff s.fst_le_snd

instance : SetLike (NonemptyInterval α) α where
  coe := fun s => Icc s.fst s.snd
  coe_injective' := coeHom.Injective

@[simp]
theorem mem_mk {hx : x.1 ≤ x.2} : a ∈ mk x hx ↔ x.1 ≤ a ∧ a ≤ x.2 :=
  Iff.rfl

theorem mem_def : a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le

@[simp, norm_cast]
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt

@[simp]
theorem coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty :=
  nonempty_Icc.2 s.fst_le_snd

@[simp]
theorem coe_coe_hom : (coeHom : NonemptyInterval α → Set α) = coe :=
  rfl

@[simp, norm_cast]
theorem coe_pure (s : α) : (pure s : Set α) = {s} :=
  Icc_self _

@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ :=
  Icc_bot_top

@[simp, norm_cast]
theorem coe_dual (s : NonemptyInterval α) : (s.dual : Set αᵒᵈ) = of_dual ⁻¹' s :=
  dual_Icc

end PartialOrderₓ

section Lattice

variable [Lattice α]

instance : HasSup (NonemptyInterval α) :=
  ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans <| s.fst_le_snd.trans le_sup_left⟩⟩

instance : SemilatticeSup (NonemptyInterval α) :=
  (to_dual_prod_injective.SemilatticeSup _) fun _ _ => rfl

@[simp]
theorem fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst :=
  rfl

@[simp]
theorem snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd :=
  rfl

end Lattice

end NonemptyInterval

/-- The closed intervals in an order.

We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`.
To convert intervals to the set of elements between these endpoints, use the coercion
`interval α → set α`. -/
def Interval (α : Type _) [LE α] :=
  WithBot (NonemptyInterval α)deriving Inhabited, LE, OrderBot

namespace Interval

section LE

variable [LE α] {s t : Interval α}

instance : CoeTₓ (NonemptyInterval α) (Interval α) :=
  WithBot.hasCoeT

instance : CanLift (Interval α) (NonemptyInterval α) :=
  WithBot.canLift

theorem coe_injective : Injective (coe : NonemptyInterval α → Interval α) :=
  WithBot.coe_injective

@[simp, norm_cast]
theorem coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t :=
  WithBot.coe_inj

@[protected]
theorem forall {p : Interval α → Prop} : (∀ s, p s) ↔ p ⊥ ∧ ∀ s : NonemptyInterval α, p s :=
  Option.forall

@[protected]
theorem exists {p : Interval α → Prop} : (∃ s, p s) ↔ p ⊥ ∨ ∃ s : NonemptyInterval α, p s :=
  Option.exists

instance [IsEmpty α] : Unique (Interval α) :=
  Option.unique

/-- Turn an interval into an interval in the dual order. -/
def dual : Interval α ≃ Interval αᵒᵈ :=
  NonemptyInterval.dual.optionCongr

end LE

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ]

instance : Preorderₓ (Interval α) :=
  WithBot.preorder

/-- `{a}` as an interval. -/
def pure (a : α) : Interval α :=
  NonemptyInterval.pure a

theorem pure_injective : Injective (pure : α → Interval α) :=
  coe_injective.comp NonemptyInterval.pure_injective

@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl

@[simp]
theorem dual_bot : (⊥ : Interval α).dual = ⊥ :=
  rfl

instance [Nonempty α] : Nontrivial (Interval α) :=
  Option.nontrivial

/-- Pushforward of intervals. -/
def map (f : α →o β) : Interval α → Interval β :=
  WithBot.map (NonemptyInterval.map f)

@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl

@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (s : Interval α) : (s.map f).map g = s.map (g.comp f) :=
  Option.map_mapₓ _ _ _

@[simp]
theorem dual_map (f : α →o β) (s : Interval α) : (s.map f).dual = s.dual.map f.dual := by
  cases s
  · rfl
    
  · exact WithBot.map_comm rfl _
    

variable [BoundedOrder α]

instance : BoundedOrder (Interval α) :=
  WithBot.boundedOrder

@[simp]
theorem dual_top : (⊤ : Interval α).dual = ⊤ :=
  rfl

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {s t : Interval α}

instance : PartialOrderₓ (Interval α) :=
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
    | some s, ⊥ => iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some s, some t => (@NonemptyInterval.coeHom α _).le_iff_le.trans WithBot.some_le_some.symm

instance : SetLike (Interval α) α where
  coe := coeHom
  coe_injective' := coeHom.Injective

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le

@[simp, norm_cast]
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt

@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _

@[simp, norm_cast]
theorem coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Interval α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ :=
  Icc_bot_top

@[simp, norm_cast]
theorem coe_dual (s : Interval α) : (s.dual : Set αᵒᵈ) = of_dual ⁻¹' s := by
  cases s
  · rfl
    
  exact s.coe_dual

end PartialOrderₓ

section Lattice

variable [Lattice α]

instance : SemilatticeSup (Interval α) :=
  WithBot.semilatticeSup

variable [@DecidableRel α (· ≤ ·)]

instance : Lattice (Interval α) :=
  { Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, t => ⊥
      | s, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then
          some ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩, sup_le (le_inf s.fst_le_snd h.1) <| le_inf h.2 t.fst_le_snd⟩
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
        exact ⟨hb.1.trans <| s.fst_le_snd.trans hc.2, hc.1.trans <| s.fst_le_snd.trans hb.2⟩ }

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
      (Icc_eq_empty fun H =>
          h ⟨le_sup_left.trans <| H.trans inf_le_right, le_sup_right.trans <| H.trans inf_le_left⟩).symm
    

@[simp, norm_cast]
theorem disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t := by
  rw [Disjoint, Disjoint, le_eq_subset, ← coe_subset_coe, coe_inf]
  rfl

end Lattice

end Interval

namespace NonemptyInterval

section Preorderₓ

variable [Preorderₓ α]

@[simp, norm_cast]
theorem coe_pure_interval (s : α) : (pure s : Interval α) = Interval.pure s :=
  rfl

@[simp, norm_cast]
theorem coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α) = ⊤ :=
  rfl

end Preorderₓ

@[simp, norm_cast]
theorem mem_coe_interval [PartialOrderₓ α] {s : NonemptyInterval α} {x : α} : x ∈ (s : Interval α) ↔ x ∈ s :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_sup_interval [Lattice α] (s t : NonemptyInterval α) : (↑(s ⊔ t) : Interval α) = s ⊔ t :=
  rfl

end NonemptyInterval

namespace Interval

section CompleteLattice

variable [CompleteLattice α]

noncomputable instance [@DecidableRel α (· ≤ ·)] : CompleteLattice (Interval α) := by
  classical <;>
    exact
      { Interval.lattice, Interval.boundedOrder with
        sup := fun S =>
          if h : S ⊆ {⊥} then ⊥
          else
            some
              ⟨⟨⨅ (s : NonemptyInterval α) (h : ↑s ∈ S), s.fst, ⨆ (s : NonemptyInterval α) (h : ↑s ∈ S), s.snd⟩, by
                obtain ⟨s, hs, ha⟩ := not_subset.1 h
                lift s to NonemptyInterval α using ha
                exact infi₂_le_of_le s hs (le_supr₂_of_le s hs s.fst_le_snd)⟩,
        le_Sup := fun s s ha => by
          split_ifs
          · exact (h ha).le
            
          cases s
          · exact bot_le
            
          · exact WithBot.some_le_some.2 ⟨infi₂_le _ ha, le_supr₂_of_le _ ha le_rflₓ⟩
            ,
        Sup_le := fun s s ha => by
          split_ifs
          · exact bot_le
            
          obtain ⟨b, hs, hb⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ne_bot_of_le_ne_bot hb (ha _ hs)
          exact
            WithBot.coe_le_coe.2
              ⟨le_infi₂ fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).1,
                supr₂_le fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).2⟩,
        inf := fun S =>
          if h : ⊥ ∉ S ∧ ∀ ⦃s : NonemptyInterval α⦄, ↑s ∈ S → ∀ ⦃t : NonemptyInterval α⦄, ↑t ∈ S → s.fst ≤ t.snd then
            some
              ⟨⟨⨆ (s : NonemptyInterval α) (h : ↑s ∈ S), s.fst, ⨅ (s : NonemptyInterval α) (h : ↑s ∈ S), s.snd⟩,
                supr₂_le fun s hs => le_infi₂ <| h.2 hs⟩
          else ⊥,
        Inf_le := fun s s ha => by
          split_ifs
          · lift s to NonemptyInterval α using ne_of_mem_of_not_memₓ ha h.1
            exact WithBot.coe_le_coe.2 ⟨le_supr₂ s ha, infi₂_le s ha⟩
            
          · exact bot_le
            ,
        le_Inf := fun S s ha => by
          cases s
          · exact bot_le
            
          split_ifs
          · exact
              WithBot.some_le_some.2
                ⟨supr₂_le fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).1,
                  le_infi₂ fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).2⟩
            
          rw [not_and_distrib, not_not] at h
          cases h
          · exact ha _ h
            
          cases
            h fun t hb c hc =>
              (WithBot.coe_le_coe.1 <| ha _ hb).1.trans <| s.fst_le_snd.trans (WithBot.coe_le_coe.1 <| ha _ hc).2 }

@[simp, norm_cast]
theorem coe_Inf (S : Set (Interval α)) : ↑(inf S) = ⋂ s ∈ S, (s : Set α) := by
  change coe (dite _ _ _) = _
  split_ifs
  · ext
    simp [WithBot.some_eq_coe, Interval.forall, h.1, ← forall_and_distrib, ← NonemptyInterval.mem_def]
    
  simp_rw [not_and_distrib, not_not] at h
  cases h
  · refine' (eq_empty_of_subset_empty _).symm
    exact Inter₂_subset_of_subset _ h subset.rfl
    
  · refine' (not_nonempty_iff_eq_empty.1 _).symm
    rintro ⟨x, hx⟩
    rw [mem_Inter₂] at hx
    exact h fun s ha t hb => (hx _ ha).1.trans (hx _ hb).2
    

@[simp, norm_cast]
theorem coe_infi (f : ι → Interval α) : ↑(⨅ i, f i) = ⋂ i, (f i : Set α) := by
  simp [infi]

-- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j)
@[simp, norm_cast]
theorem coe_infi₂ (f : ∀ i, κ i → Interval α) : ↑(⨅ (i) (j), f i j) = ⋂ (i) (j), (f i j : Set α) := by
  simp_rw [coe_infi]

end CompleteLattice

end Interval

