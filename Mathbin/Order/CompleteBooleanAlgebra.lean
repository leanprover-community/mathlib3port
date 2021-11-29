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
  infi_sup_le_sup_Inf : ∀ a s, (⨅(b : _)(_ : b ∈ s), a⊔b) ≤ a⊔Inf s 
  inf_Sup_le_supr_inf : ∀ a s, a⊓Sup s ≤ ⨆(b : _)(_ : b ∈ s), a⊓b

section CompleteDistribLattice

variable [CompleteDistribLattice α] {a b : α} {s t : Set α}

instance : CompleteDistribLattice (OrderDual α) :=
  { OrderDual.completeLattice α with infi_sup_le_sup_Inf := CompleteDistribLattice.inf_Sup_le_supr_inf,
    inf_Sup_le_supr_inf := CompleteDistribLattice.infi_sup_le_sup_Inf }

theorem sup_Inf_eq : a⊔Inf s = ⨅(b : _)(_ : b ∈ s), a⊔b :=
  sup_Inf_le_infi_sup.antisymm (CompleteDistribLattice.infi_sup_le_sup_Inf _ _)

theorem Inf_sup_eq : Inf s⊔b = ⨅(a : _)(_ : a ∈ s), a⊔b :=
  by 
    simpa only [sup_comm] using @sup_Inf_eq α _ b s

theorem inf_Sup_eq : a⊓Sup s = ⨆(b : _)(_ : b ∈ s), a⊓b :=
  (CompleteDistribLattice.inf_Sup_le_supr_inf _ _).antisymm supr_inf_le_inf_Sup

theorem Sup_inf_eq : Sup s⊓b = ⨆(a : _)(_ : a ∈ s), a⊓b :=
  by 
    simpa only [inf_comm] using @inf_Sup_eq α _ b s

theorem supr_inf_eq (f : ι → α) (a : α) : (⨆i, f i)⊓a = ⨆i, f i⊓a :=
  by 
    rw [supr, Sup_inf_eq, supr_range]

theorem inf_supr_eq (a : α) (f : ι → α) : (a⊓⨆i, f i) = ⨆i, a⊓f i :=
  by 
    simpa only [inf_comm] using supr_inf_eq f a

theorem infi_sup_eq (f : ι → α) (a : α) : (⨅i, f i)⊔a = ⨅i, f i⊔a :=
  @supr_inf_eq (OrderDual α) _ _ _ _

theorem sup_infi_eq (a : α) (f : ι → α) : (a⊔⨅i, f i) = ⨅i, a⊔f i :=
  @inf_supr_eq (OrderDual α) _ _ _ _

instance Pi.completeDistribLattice {ι : Type _} {π : ι → Type _} [∀ i, CompleteDistribLattice (π i)] :
  CompleteDistribLattice (∀ i, π i) :=
  { Pi.completeLattice with
    infi_sup_le_sup_Inf :=
      fun a s i =>
        by 
          simp only [←sup_infi_eq, CompleteLattice.infₓ, Inf_apply, ←infi_subtype'', infi_apply, Pi.sup_apply],
    inf_Sup_le_supr_inf :=
      fun a s i =>
        by 
          simp only [CompleteLattice.supₓ, Sup_apply, supr_apply, Pi.inf_apply, inf_supr_eq, ←supr_subtype''] }

-- error in Order.CompleteBooleanAlgebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Inf_sup_Inf : «expr = »(«expr ⊔ »(Inf s, Inf t), «expr⨅ , »((p «expr ∈ » set.prod s t), «expr ⊔ »((p : «expr × »(α, α)).1, p.2))) :=
begin
  apply [expr le_antisymm],
  { simp [] [] ["only"] ["[", expr and_imp, ",", expr prod.forall, ",", expr le_infi_iff, ",", expr set.mem_prod, "]"] [] [],
    intros [ident a, ident b, ident ha, ident hb],
    exact [expr sup_le_sup (Inf_le ha) (Inf_le hb)] },
  { have [] [":", expr ∀
     a «expr ∈ » s, «expr ≤ »(«expr⨅ , »((p «expr ∈ » set.prod s t), «expr ⊔ »((p : «expr × »(α, α)).1, p.2)), «expr ⊔ »(a, Inf t))] [],
    { rintro [ident a, ident ha],
      have [] [":", expr «expr ≤ »(«expr⨅ , »((p «expr ∈ » set.prod s t), «expr ⊔ »(((p : «expr × »(α, α)).1 : α), p.2)), «expr⨅ , »((p «expr ∈ » «expr '' »(prod.mk a, t)), «expr ⊔ »((p : «expr × »(α, α)).1, p.2)))] [],
      { apply [expr infi_le_infi_of_subset],
        rintro ["⟨", ident x, ",", ident y, "⟩"],
        simp [] [] ["only"] ["[", expr and_imp, ",", expr set.mem_image, ",", expr prod.mk.inj_iff, ",", expr set.prod_mk_mem_set_prod_eq, ",", expr exists_imp_distrib, "]"] [] [],
        rintro [ident x', ident x't, ident ax, ident x'y],
        rw ["[", "<-", expr x'y, ",", "<-", expr ax, "]"] [],
        simp [] [] [] ["[", expr ha, ",", expr x't, "]"] [] [] },
      rw ["[", expr infi_image, "]"] ["at", ident this],
      simp [] [] ["only"] [] [] ["at", ident this],
      rwa ["<-", expr sup_Inf_eq] ["at", ident this] },
    calc
      «expr ≤ »(«expr⨅ , »((p «expr ∈ » set.prod s t), «expr ⊔ »((p : «expr × »(α, α)).1, p.2)), «expr⨅ , »((a «expr ∈ » s), «expr ⊔ »(a, Inf t))) : by simp [] [] [] [] [] []; exact [expr this]
      «expr = »(..., «expr ⊔ »(Inf s, Inf t)) : Inf_sup_eq.symm }
end

theorem Sup_inf_Sup : Sup s⊓Sup t = ⨆(p : _)(_ : p ∈ Set.Prod s t), (p : α × α).1⊓p.2 :=
  @Inf_sup_Inf (OrderDual α) _ _ _

theorem supr_disjoint_iff {f : ι → α} : Disjoint (⨆i, f i) a ↔ ∀ i, Disjoint (f i) a :=
  by 
    simp only [disjoint_iff, supr_inf_eq, supr_eq_bot]

theorem disjoint_supr_iff {f : ι → α} : Disjoint a (⨆i, f i) ↔ ∀ i, Disjoint a (f i) :=
  by 
    simpa only [Disjoint.comm] using @supr_disjoint_iff _ _ _ a f

end CompleteDistribLattice

instance (priority := 100) CompleteDistribLattice.toDistribLattice [d : CompleteDistribLattice α] : DistribLattice α :=
  { d with
    le_sup_inf :=
      fun x y z =>
        by 
          rw [←Inf_pair, ←Inf_pair, sup_Inf_eq, ←Inf_image, Set.image_pair] }

/-- A complete Boolean algebra is a completely distributive Boolean algebra. -/
class CompleteBooleanAlgebra (α) extends BooleanAlgebra α, CompleteDistribLattice α

instance Pi.completeBooleanAlgebra {ι : Type _} {π : ι → Type _} [∀ i, CompleteBooleanAlgebra (π i)] :
  CompleteBooleanAlgebra (∀ i, π i) :=
  { Pi.booleanAlgebra, Pi.completeDistribLattice with  }

instance Prop.completeBooleanAlgebra : CompleteBooleanAlgebra Prop :=
  { Prop.booleanAlgebra, Prop.completeLattice with
    infi_sup_le_sup_Inf :=
      fun p s =>
        Iff.mp$
          by 
            simp only [forall_or_distrib_left, CompleteLattice.infₓ, infi_Prop_eq, sup_Prop_eq],
    inf_Sup_le_supr_inf :=
      fun p s =>
        Iff.mp$
          by 
            simp only [CompleteLattice.supₓ, exists_and_distrib_left, inf_Prop_eq, supr_Prop_eq] }

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

theorem compl_infi : «expr ᶜ» (infi f) = ⨆i, «expr ᶜ» (f i) :=
  le_antisymmₓ (compl_le_of_compl_le$ le_infi$ fun i => compl_le_of_compl_le$ le_supr (compl ∘ f) i)
    (supr_le$ fun i => compl_le_compl$ infi_le _ _)

theorem compl_supr : «expr ᶜ» (supr f) = ⨅i, «expr ᶜ» (f i) :=
  compl_injective
    (by 
      simp [compl_infi])

theorem compl_Inf : «expr ᶜ» (Inf s) = ⨆(i : _)(_ : i ∈ s), «expr ᶜ» i :=
  by 
    simp only [Inf_eq_infi, compl_infi]

theorem compl_Sup : «expr ᶜ» (Sup s) = ⨅(i : _)(_ : i ∈ s), «expr ᶜ» i :=
  by 
    simp only [Sup_eq_supr, compl_supr]

end CompleteBooleanAlgebra

