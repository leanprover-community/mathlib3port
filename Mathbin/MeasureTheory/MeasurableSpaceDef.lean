import Mathbin.Order.SymmDiff 
import Mathbin.Order.Disjointed 
import Mathbin.Order.ConditionallyCompleteLattice 
import Mathbin.Data.Equiv.Encodable.Lattice 
import Mathbin.Data.Set.Countable

/-!
# Measurable spaces and measurable functions

This file defines measurable spaces and measurable functions.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

Do not add measurability lemmas (which could be tagged with
@[measurability]) to this file, since the measurability tactic is downstream
from here. Use `measure_theory.measurable_space` instead.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/


open Set Encodable Function Equiv

open_locale Classical

variable {α β γ δ δ' : Type _} {ι : Sort _} {s t u : Set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
structure MeasurableSpace (α : Type _) where 
  MeasurableSet' : Set α → Prop 
  measurable_set_empty : measurable_set' ∅
  measurable_set_compl : ∀ s, measurable_set' s → measurable_set' («expr ᶜ» s)
  measurable_set_Union : ∀ f : ℕ → Set α, (∀ i, measurable_set' (f i)) → measurable_set' (⋃i, f i)

attribute [class] MeasurableSpace

instance [h : MeasurableSpace α] : MeasurableSpace (OrderDual α) :=
  h

section 

variable [MeasurableSpace α]

/-- `measurable_set s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet : Set α → Prop :=
  ‹MeasurableSpace α›.MeasurableSet'

localized [MeasureTheory] notation "measurable_set[" m "]" => @MeasurableSet _ m

@[simp]
theorem MeasurableSet.empty : MeasurableSet (∅ : Set α) :=
  ‹MeasurableSpace α›.measurable_set_empty

theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet («expr ᶜ» s) :=
  ‹MeasurableSpace α›.measurable_set_compl s

theorem MeasurableSet.of_compl (h : MeasurableSet («expr ᶜ» s)) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet («expr ᶜ» s) ↔ MeasurableSet s :=
  ⟨MeasurableSet.of_compl, MeasurableSet.compl⟩

@[simp]
theorem MeasurableSet.univ : MeasurableSet (univ : Set α) :=
  by 
    simpa using (@MeasurableSet.empty α _).Compl

@[nontriviality]
theorem Subsingleton.measurable_set [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t :=
  by 
    rwa [←h]

theorem MeasurableSet.bUnion_decode₂ [Encodable β] ⦃f : β → Set α⦄ (h : ∀ b, MeasurableSet (f b)) (n : ℕ) :
  MeasurableSet (⋃(b : _)(_ : b ∈ decode₂ β n), f b) :=
  Encodable.Union_decode₂_cases MeasurableSet.empty h

theorem MeasurableSet.Union [Encodable β] ⦃f : β → Set α⦄ (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃b, f b) :=
  by 
    rw [←Encodable.Union_decode₂]
    exact ‹MeasurableSpace α›.measurable_set_Union _ (MeasurableSet.bUnion_decode₂ h)

-- error in MeasureTheory.MeasurableSpaceDef: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measurable_set.bUnion
{f : β → set α}
{s : set β}
(hs : countable s)
(h : ∀ b «expr ∈ » s, measurable_set (f b)) : measurable_set «expr⋃ , »((b «expr ∈ » s), f b) :=
begin
  rw [expr bUnion_eq_Union] [],
  haveI [] [] [":=", expr hs.to_encodable],
  exact [expr measurable_set.Union (by simpa [] [] [] [] [] ["using", expr h])]
end

theorem Set.Finite.measurable_set_bUnion {f : β → Set α} {s : Set β} (hs : finite s)
  (h : ∀ b _ : b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃(b : _)(_ : b ∈ s), f b) :=
  MeasurableSet.bUnion hs.countable h

theorem Finset.measurable_set_bUnion {f : β → Set α} (s : Finset β) (h : ∀ b _ : b ∈ s, MeasurableSet (f b)) :
  MeasurableSet (⋃(b : _)(_ : b ∈ s), f b) :=
  s.finite_to_set.measurable_set_bUnion h

theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : countable s) (h : ∀ t _ : t ∈ s, MeasurableSet t) :
  MeasurableSet (⋃₀s) :=
  by 
    rw [sUnion_eq_bUnion]
    exact MeasurableSet.bUnion hs h

theorem Set.Finite.measurable_set_sUnion {s : Set (Set α)} (hs : finite s) (h : ∀ t _ : t ∈ s, MeasurableSet t) :
  MeasurableSet (⋃₀s) :=
  MeasurableSet.sUnion hs.countable h

theorem MeasurableSet.Union_Prop {p : Prop} {f : p → Set α} (hf : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃b, f b) :=
  by 
    byCases' p <;> simp [h, hf, MeasurableSet.empty]

theorem MeasurableSet.Inter [Encodable β] {f : β → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂b, f b) :=
  MeasurableSet.compl_iff.1$
    by 
      rw [compl_Inter]
      exact MeasurableSet.Union fun b => (h b).Compl

section Fintype

attribute [local instance] Fintype.encodable

theorem MeasurableSet.Union_fintype [Fintype β] {f : β → Set α} (h : ∀ b, MeasurableSet (f b)) :
  MeasurableSet (⋃b, f b) :=
  MeasurableSet.Union h

theorem MeasurableSet.Inter_fintype [Fintype β] {f : β → Set α} (h : ∀ b, MeasurableSet (f b)) :
  MeasurableSet (⋂b, f b) :=
  MeasurableSet.Inter h

end Fintype

theorem MeasurableSet.bInter {f : β → Set α} {s : Set β} (hs : countable s) (h : ∀ b _ : b ∈ s, MeasurableSet (f b)) :
  MeasurableSet (⋂(b : _)(_ : b ∈ s), f b) :=
  MeasurableSet.compl_iff.1$
    by 
      rw [compl_bInter]
      exact MeasurableSet.bUnion hs fun b hb => (h b hb).Compl

theorem Set.Finite.measurable_set_bInter {f : β → Set α} {s : Set β} (hs : finite s)
  (h : ∀ b _ : b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂(b : _)(_ : b ∈ s), f b) :=
  MeasurableSet.bInter hs.countable h

theorem Finset.measurable_set_bInter {f : β → Set α} (s : Finset β) (h : ∀ b _ : b ∈ s, MeasurableSet (f b)) :
  MeasurableSet (⋂(b : _)(_ : b ∈ s), f b) :=
  s.finite_to_set.measurable_set_bInter h

theorem MeasurableSet.sInter {s : Set (Set α)} (hs : countable s) (h : ∀ t _ : t ∈ s, MeasurableSet t) :
  MeasurableSet (⋂₀s) :=
  by 
    rw [sInter_eq_bInter]
    exact MeasurableSet.bInter hs h

theorem Set.Finite.measurable_set_sInter {s : Set (Set α)} (hs : finite s) (h : ∀ t _ : t ∈ s, MeasurableSet t) :
  MeasurableSet (⋂₀s) :=
  MeasurableSet.sInter hs.countable h

theorem MeasurableSet.Inter_Prop {p : Prop} {f : p → Set α} (hf : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂b, f b) :=
  by 
    byCases' p <;> simp [h, hf, MeasurableSet.univ]

@[simp]
theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) :=
  by 
    rw [union_eq_Union]
    exact MeasurableSet.Union (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp]
theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) :=
  by 
    rw [inter_eq_compl_compl_union_compl]
    exact (h₁.compl.union h₂.compl).Compl

@[simp]
theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp]
theorem MeasurableSet.symm_diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
  MeasurableSet (s₁ Δ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp]
theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
  MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

@[simp]
theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) {i : Bool} :
  MeasurableSet (cond i s₁ s₂) :=
  by 
    cases i 
    exacts[h₂, h₁]

@[simp]
theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) n : MeasurableSet (disjointed f n) :=
  disjointedRecₓ (fun t i ht => MeasurableSet.diff ht$ h _) (h n)

@[simp]
theorem MeasurableSet.const (p : Prop) : MeasurableSet { a:α | p } :=
  by 
    byCases' p <;> simp [h, MeasurableSet.empty] <;> apply MeasurableSet.univ

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

end 

@[ext]
theorem MeasurableSpace.ext :
  ∀ {m₁ m₂ : MeasurableSpace α}, (∀ s : Set α, m₁.measurable_set' s ↔ m₂.measurable_set' s) → m₁ = m₂
| ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h =>
  have  : s₁ = s₂ := funext$ fun x => propext$ h x 
  by 
    subst this

@[ext]
theorem MeasurableSpace.ext_iff {m₁ m₂ : MeasurableSpace α} :
  m₁ = m₂ ↔ ∀ s : Set α, m₁.measurable_set' s ↔ m₂.measurable_set' s :=
  ⟨by 
      (
        rintro rfl)
      intro s 
      rfl,
    MeasurableSpace.ext⟩

/-- A typeclass mixin for `measurable_space`s such that each singleton is measurable. -/
class MeasurableSingletonClass (α : Type _) [MeasurableSpace α] : Prop where 
  measurable_set_singleton : ∀ x, MeasurableSet ({x} : Set α)

export MeasurableSingletonClass(measurable_set_singleton)

attribute [simp] measurable_set_singleton

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem measurable_set_eq {a : α} : MeasurableSet { x | x = a } :=
  measurable_set_singleton a

theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) : MeasurableSet (insert a s) :=
  (measurable_set_singleton a).union hs

@[simp]
theorem measurable_set_insert {a : α} {s : Set α} : MeasurableSet (insert a s) ↔ MeasurableSet s :=
  ⟨fun h =>
      if ha : a ∈ s then
        by 
          rwa [←insert_eq_of_mem ha]
      else insert_diff_self_of_not_mem ha ▸ h.diff (measurable_set_singleton _),
    fun h => h.insert a⟩

theorem Set.Subsingleton.measurable_set {s : Set α} (hs : s.subsingleton) : MeasurableSet s :=
  hs.induction_on MeasurableSet.empty measurable_set_singleton

theorem Set.Finite.measurable_set {s : Set α} (hs : finite s) : MeasurableSet s :=
  finite.induction_on hs MeasurableSet.empty$ fun a s ha hsf hsm => hsm.insert _

protected theorem Finset.measurable_set (s : Finset α) : MeasurableSet («expr↑ » s : Set α) :=
  s.finite_to_set.measurable_set

theorem Set.Countable.measurable_set {s : Set α} (hs : countable s) : MeasurableSet s :=
  by 
    rw [←bUnion_of_singleton s]
    exact MeasurableSet.bUnion hs fun b hb => measurable_set_singleton b

end MeasurableSingletonClass

namespace MeasurableSpace

section CompleteLattice

instance : LE (MeasurableSpace α) :=
  { le := fun m₁ m₂ => m₁.measurable_set' ≤ m₂.measurable_set' }

theorem le_def {α} {a b : MeasurableSpace α} : a ≤ b ↔ a.measurable_set' ≤ b.measurable_set' :=
  Iff.rfl

instance : PartialOrderₓ (MeasurableSpace α) :=
  { MeasurableSpace.hasLe with le_refl := fun a b => le_reflₓ _,
    le_trans := fun a b c hab hbc => le_def.mpr (le_transₓ hab hbc),
    le_antisymm := fun a b h₁ h₂ => MeasurableSpace.ext$ fun s => ⟨h₁ s, h₂ s⟩ }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive generate_measurable (s : Set (Set α)) : Set α → Prop
  | basic : ∀ u _ : u ∈ s, generate_measurable u
  | Empty : generate_measurable ∅
  | compl : ∀ s, generate_measurable s → generate_measurable («expr ᶜ» s)
  | union : ∀ f : ℕ → Set α, (∀ n, generate_measurable (f n)) → generate_measurable (⋃i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
def generate_from (s : Set (Set α)) : MeasurableSpace α :=
  { MeasurableSet' := generate_measurable s, measurable_set_empty := generate_measurable.empty,
    measurable_set_compl := generate_measurable.compl, measurable_set_Union := generate_measurable.union }

theorem measurable_set_generate_from {s : Set (Set α)} {t : Set α} (ht : t ∈ s) : (generate_from s).MeasurableSet' t :=
  generate_measurable.basic t ht

theorem generate_from_le {s : Set (Set α)} {m : MeasurableSpace α} (h : ∀ t _ : t ∈ s, m.measurable_set' t) :
  generate_from s ≤ m :=
  fun t ht : generate_measurable s t =>
    ht.rec_on h (measurable_set_empty m) (fun s _ hs => measurable_set_compl m s hs)
      fun f _ hf => measurable_set_Union m f hf

theorem generate_from_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
  generate_from s ≤ m ↔ s ⊆ { t | m.measurable_set' t } :=
  Iff.intro (fun h u hu => h _$ measurable_set_generate_from hu) fun h => generate_from_le h

@[simp]
theorem generate_from_measurable_set [MeasurableSpace α] : generate_from { s:Set α | MeasurableSet s } = ‹_› :=
  le_antisymmₓ (generate_from_le$ fun _ => id)$ fun s => measurable_set_generate_from

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mk_of_closure (g : Set (Set α)) (hg : { t | (generate_from g).MeasurableSet' t } = g) :
  MeasurableSpace α :=
  { MeasurableSet' := fun s => s ∈ g, measurable_set_empty := hg ▸ measurable_set_empty _,
    measurable_set_compl := hg ▸ measurable_set_compl _, measurable_set_Union := hg ▸ measurable_set_Union _ }

theorem mk_of_closure_sets {s : Set (Set α)} {hs : { t | (generate_from s).MeasurableSet' t } = s} :
  MeasurableSpace.mkOfClosure s hs = generate_from s :=
  MeasurableSpace.ext$
    fun t =>
      show t ∈ s ↔ _ by 
        convLHS => rw [←hs]
        rfl

/-- We get a Galois insertion between `σ`-algebras on `α` and `set (set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
def gi_generate_from : GaloisInsertion (@generate_from α) fun m => { t | @MeasurableSet α m t } :=
  { gc := fun s => generate_from_le_iff, le_l_u := fun m s => measurable_set_generate_from,
    choice := fun g hg => MeasurableSpace.mkOfClosure g$ le_antisymmₓ hg$ (generate_from_le_iff _).1 le_rfl,
    choice_eq := fun g hg => mk_of_closure_sets }

instance : CompleteLattice (MeasurableSpace α) :=
  gi_generate_from.liftCompleteLattice

instance : Inhabited (MeasurableSpace α) :=
  ⟨⊤⟩

-- error in MeasureTheory.MeasurableSpaceDef: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measurable_set_bot_iff
{s : set α} : «expr ↔ »(@measurable_set α «expr⊥»() s, «expr ∨ »(«expr = »(s, «expr∅»()), «expr = »(s, univ))) :=
let b : measurable_space α := { measurable_set' := λ s, «expr ∨ »(«expr = »(s, «expr∅»()), «expr = »(s, univ)),
      measurable_set_empty := or.inl rfl,
      measurable_set_compl := by simp [] [] [] ["[", expr or_imp_distrib, "]"] [] [] { contextual := tt },
      measurable_set_Union := assume
      f
      hf, classical.by_cases (assume h : «expr∃ , »((i), «expr = »(f i, univ)), let ⟨i, hi⟩ := h in
       «expr $ »(or.inr, «expr $ »(eq_univ_of_univ_subset, «expr ▸ »(hi, le_supr f i)))) (assume
       h : «expr¬ »(«expr∃ , »((i), «expr = »(f i, univ))), «expr $ »(or.inl, «expr $ »(eq_empty_of_subset_empty, «expr $ »(Union_subset, assume
          i, (hf i).elim (by simp [] [] [] [] [] [] { contextual := tt }) (assume
           hi, «expr $ »(false.elim, h ⟨i, hi⟩)))))) } in
have «expr = »(b, «expr⊥»()), from «expr $ »(bot_unique, assume
 s
 hs, hs.elim (λ
  s, «expr ▸ »(s.symm, @measurable_set_empty _ «expr⊥»())) (λ s, «expr ▸ »(s.symm, @measurable_set.univ _ «expr⊥»()))),
«expr ▸ »(this, iff.rfl)

@[simp]
theorem measurable_set_top {s : Set α} : @MeasurableSet _ ⊤ s :=
  trivialₓ

@[simp]
theorem measurable_set_inf {m₁ m₂ : MeasurableSpace α} {s : Set α} :
  @MeasurableSet _ (m₁⊓m₂) s ↔ @MeasurableSet _ m₁ s ∧ @MeasurableSet _ m₂ s :=
  Iff.rfl

@[simp]
theorem measurable_set_Inf {ms : Set (MeasurableSpace α)} {s : Set α} :
  @MeasurableSet _ (Inf ms) s ↔ ∀ m _ : m ∈ ms, @MeasurableSet _ m s :=
  show s ∈ ⋂₀_ ↔ _ by 
    simp 

@[simp]
theorem measurable_set_infi {ι} {m : ι → MeasurableSpace α} {s : Set α} :
  @MeasurableSet _ (infi m) s ↔ ∀ i, @MeasurableSet _ (m i) s :=
  by 
    rw [infi, measurable_set_Inf, forall_range_iff]

theorem measurable_set_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
  @MeasurableSet _ (m₁⊔m₂) s ↔ generate_measurable (m₁.measurable_set' ∪ m₂.measurable_set') s :=
  Iff.refl _

theorem measurable_set_Sup {ms : Set (MeasurableSpace α)} {s : Set α} :
  @MeasurableSet _ (Sup ms) s ↔ generate_measurable { s:Set α | ∃ (m : _)(_ : m ∈ ms), @MeasurableSet _ m s } s :=
  by 
    change @measurable_set' _ (generate_from$ ⋃₀_) _ ↔ _ 
    simp [generate_from, ←set_of_exists]

theorem measurable_set_supr {ι} {m : ι → MeasurableSpace α} {s : Set α} :
  @MeasurableSet _ (supr m) s ↔ generate_measurable { s:Set α | ∃ i, @MeasurableSet _ (m i) s } s :=
  by 
    simp only [supr, measurable_set_Sup, exists_range_iff]

end CompleteLattice

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)

localized [MeasureTheory] notation "measurable[" m "]" => @Measurable _ _ m _

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem measurable_id : Measurable (@id α) :=
  fun t => id

theorem measurable_id' : Measurable fun a : α => a :=
  measurable_id

theorem Measurable.comp {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) : Measurable (g ∘ f) :=
  fun t ht => hf (hg ht)

@[simp]
theorem measurable_const {a : α} : Measurable fun b : β => a :=
  fun s hs => MeasurableSet.const (a ∈ s)

end MeasurableFunctions

