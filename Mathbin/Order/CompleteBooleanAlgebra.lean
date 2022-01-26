import Mathbin.Order.CompleteLattice

/-!
# Completely distributive lattices and Boolean algebras

In this file there are definitions and an API for completely distributive lattices and completely
distributive Boolean algebras.

## Typeclasses

* `complete_distrib_lattice`: Completely distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `complete_boolean_algebra`: Completely distributive Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
-/


universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w}

/-- A complete distributive lattice is a bit stronger than the name might
  suggest; perhaps completely distributive lattice is more descriptive,
  as this class includes a requirement that the lattice join
  distribute over *arbitrary* infima, and similarly for the dual. -/
class CompleteDistribLattice (α) extends CompleteLattice α where
  infi_sup_le_sup_Inf : ∀ a s, (⨅ b ∈ s, a⊔b) ≤ a⊔Inf s
  inf_Sup_le_supr_inf : ∀ a s, a⊓Sup s ≤ ⨆ b ∈ s, a⊓b

section CompleteDistribLattice

variable [CompleteDistribLattice α] {a b : α} {s t : Set α}

instance : CompleteDistribLattice (OrderDual α) :=
  { OrderDual.completeLattice α with infi_sup_le_sup_Inf := CompleteDistribLattice.inf_Sup_le_supr_inf,
    inf_Sup_le_supr_inf := CompleteDistribLattice.infi_sup_le_sup_Inf }

theorem sup_Inf_eq : a⊔Inf s = ⨅ b ∈ s, a⊔b :=
  sup_Inf_le_infi_sup.antisymm (CompleteDistribLattice.infi_sup_le_sup_Inf _ _)

theorem Inf_sup_eq : Inf s⊔b = ⨅ a ∈ s, a⊔b := by
  simpa only [sup_comm] using @sup_Inf_eq α _ b s

theorem inf_Sup_eq : a⊓Sup s = ⨆ b ∈ s, a⊓b :=
  (CompleteDistribLattice.inf_Sup_le_supr_inf _ _).antisymm supr_inf_le_inf_Sup

theorem Sup_inf_eq : Sup s⊓b = ⨆ a ∈ s, a⊓b := by
  simpa only [inf_comm] using @inf_Sup_eq α _ b s

theorem supr_inf_eq (f : ι → α) (a : α) : (⨆ i, f i)⊓a = ⨆ i, f i⊓a := by
  rw [supr, Sup_inf_eq, supr_range]

theorem inf_supr_eq (a : α) (f : ι → α) : (a⊓⨆ i, f i) = ⨆ i, a⊓f i := by
  simpa only [inf_comm] using supr_inf_eq f a

theorem infi_sup_eq (f : ι → α) (a : α) : (⨅ i, f i)⊔a = ⨅ i, f i⊔a :=
  @supr_inf_eq (OrderDual α) _ _ _ _

theorem sup_infi_eq (a : α) (f : ι → α) : (a⊔⨅ i, f i) = ⨅ i, a⊔f i :=
  @inf_supr_eq (OrderDual α) _ _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
theorem bsupr_inf_eq {p : α → Prop} {f : ∀ i hi : p i, α} (a : α) : (⨆ (i) (hi), f i hi)⊓a = ⨆ (i) (hi), f i hi⊓a := by
  simp only [supr_inf_eq]

-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
theorem inf_bsupr_eq (a : α) {p : α → Prop} {f : ∀ i hi : p i, α} : (a⊓⨆ (i) (hi), f i hi) = ⨆ (i) (hi), a⊓f i hi := by
  simp only [inf_supr_eq]

-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
theorem binfi_sup_eq {p : α → Prop} {f : ∀ i hi : p i, α} (a : α) : (⨅ (i) (hi), f i hi)⊔a = ⨅ (i) (hi), f i hi⊔a :=
  @bsupr_inf_eq (OrderDual α) _ _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (i hi)
theorem sup_binfi_eq (a : α) {p : α → Prop} {f : ∀ i hi : p i, α} : (a⊔⨅ (i) (hi), f i hi) = ⨅ (i) (hi), a⊔f i hi :=
  @inf_bsupr_eq (OrderDual α) _ _ _ _

instance Pi.completeDistribLattice {ι : Type _} {π : ι → Type _} [∀ i, CompleteDistribLattice (π i)] :
    CompleteDistribLattice (∀ i, π i) :=
  { Pi.completeLattice with
    infi_sup_le_sup_Inf := fun a s i => by
      simp only [← sup_infi_eq, CompleteLattice.infₓ, Inf_apply, ← infi_subtype'', infi_apply, Pi.sup_apply],
    inf_Sup_le_supr_inf := fun a s i => by
      simp only [CompleteLattice.supₓ, Sup_apply, supr_apply, Pi.inf_apply, inf_supr_eq, ← supr_subtype''] }

theorem Inf_sup_Inf : Inf s⊔Inf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1⊔p.2 := by
  apply le_antisymmₓ
  · simp only [and_imp, Prod.forall, le_infi_iff, Set.mem_prod]
    intro a b ha hb
    exact sup_le_sup (Inf_le ha) (Inf_le hb)
    
  · have : ∀, ∀ a ∈ s, ∀, (⨅ p ∈ s ×ˢ t, (p : α × α).1⊔p.2) ≤ a⊔Inf t := by
      rintro a ha
      have : (⨅ p ∈ s ×ˢ t, ((p : α × α).1 : α)⊔p.2) ≤ ⨅ p ∈ Prod.mk a '' t, (p : α × α).1⊔p.2 := by
        apply infi_le_infi_of_subset
        rintro ⟨x, y⟩
        simp only [and_imp, Set.mem_image, Prod.mk.inj_iffₓ, Set.prod_mk_mem_set_prod_eq, exists_imp_distrib]
        rintro x' x't ax x'y
        rw [← x'y, ← ax]
        simp [ha, x't]
      rw [infi_image] at this
      simp only at this
      rwa [← sup_Inf_eq] at this
    calc (⨅ p ∈ s ×ˢ t, (p : α × α).1⊔p.2) ≤ ⨅ a ∈ s, a⊔Inf t := by
        simp <;> exact this _ = Inf s⊔Inf t := Inf_sup_eq.symm
    

theorem Sup_inf_Sup : Sup s⊓Sup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1⊓p.2 :=
  @Inf_sup_Inf (OrderDual α) _ _ _

theorem supr_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, supr_inf_eq, supr_eq_bot]

theorem disjoint_supr_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [Disjoint.comm] using @supr_disjoint_iff _ _ _ a f

end CompleteDistribLattice

instance (priority := 100) CompleteDistribLattice.toDistribLattice [d : CompleteDistribLattice α] : DistribLattice α :=
  { d with
    le_sup_inf := fun x y z => by
      rw [← Inf_pair, ← Inf_pair, sup_Inf_eq, ← Inf_image, Set.image_pair] }

/-- A complete Boolean algebra is a completely distributive Boolean algebra. -/
class CompleteBooleanAlgebra (α) extends BooleanAlgebra α, CompleteDistribLattice α

instance Pi.completeBooleanAlgebra {ι : Type _} {π : ι → Type _} [∀ i, CompleteBooleanAlgebra (π i)] :
    CompleteBooleanAlgebra (∀ i, π i) :=
  { Pi.booleanAlgebra, Pi.completeDistribLattice with }

instance Prop.completeBooleanAlgebra : CompleteBooleanAlgebra Prop :=
  { Prop.booleanAlgebra, Prop.completeLattice with
    infi_sup_le_sup_Inf := fun p s =>
      Iff.mp <| by
        simp only [forall_or_distrib_left, CompleteLattice.infₓ, infi_Prop_eq, sup_Prop_eq],
    inf_Sup_le_supr_inf := fun p s =>
      Iff.mp <| by
        simp only [CompleteLattice.supₓ, exists_and_distrib_left, inf_Prop_eq, supr_Prop_eq] }

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

theorem compl_infi : infi fᶜ = ⨆ i, f iᶜ :=
  le_antisymmₓ (compl_le_of_compl_le <| le_infi fun i => compl_le_of_compl_le <| le_supr (compl ∘ f) i)
    (supr_le fun i => compl_le_compl <| infi_le _ _)

theorem compl_supr : supr fᶜ = ⨅ i, f iᶜ :=
  compl_injective
    (by
      simp [compl_infi])

theorem compl_Inf : Inf sᶜ = ⨆ i ∈ s, iᶜ := by
  simp only [Inf_eq_infi, compl_infi]

theorem compl_Sup : Sup sᶜ = ⨅ i ∈ s, iᶜ := by
  simp only [Sup_eq_supr, compl_supr]

end CompleteBooleanAlgebra

