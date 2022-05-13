/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Order.RelIso
import Mathbin.Order.LatticeIntervals
import Mathbin.Order.GaloisConnection

/-!
# Modular Lattices
This file defines Modular Lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Main Definitions
- `is_modular_lattice` defines a modular lattice to be one such that
  `x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)`
- `inf_Icc_order_iso_Icc_sup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results
- `is_modular_lattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `distrib_lattice.is_modular_lattice`: Distributive lattices are modular.

## To do
- Relate atoms and coatoms in modular lattices

-/


variable {α : Type _}

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class IsModularLattice (α) [Lattice α] : Prop where
  sup_inf_le_assoc_of_le : ∀ {x : α} y : α {z : α}, x ≤ z → (x⊔y)⊓z ≤ x⊔y⊓z

section IsModularLattice

variable [Lattice α] [IsModularLattice α]

theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) : (x⊔y)⊓z = x⊔y⊓z :=
  le_antisymmₓ (IsModularLattice.sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

theorem IsModularLattice.inf_sup_inf_assoc {x y z : α} : x⊓z⊔y⊓z = (x⊓z⊔y)⊓z :=
  (sup_inf_assoc_of_le y inf_le_right).symm

theorem inf_sup_assoc_of_le {x : α} (y : α) {z : α} (h : z ≤ x) : x⊓y⊔z = x⊓(y⊔z) := by
  rw [inf_comm, sup_comm, ← sup_inf_assoc_of_le y h, inf_comm, sup_comm]

instance : IsModularLattice αᵒᵈ :=
  ⟨fun x y z xz =>
    le_of_eqₓ
      (by
        rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm]
        convert sup_inf_assoc_of_le (OrderDual.ofDual y) (OrderDual.dual_le.2 xz))⟩

variable {x y z : α}

theorem IsModularLattice.sup_inf_sup_assoc : (x⊔z)⊓(y⊔z) = (x⊔z)⊓y⊔z :=
  @IsModularLattice.inf_sup_inf_assoc αᵒᵈ _ _ _ _ _

theorem eq_of_le_of_inf_le_of_sup_le (hxy : x ≤ y) (hinf : y⊓z ≤ x⊓z) (hsup : y⊔z ≤ x⊔z) : x = y :=
  le_antisymmₓ hxy <|
    have h : y ≤ x⊔z :=
      calc
        y ≤ y⊔z := le_sup_left
        _ ≤ x⊔z := hsup
        
    calc
      y ≤ (x⊔z)⊓y := le_inf h le_rfl
      _ = x⊔z⊓y := sup_inf_assoc_of_le _ hxy
      _ ≤ x⊔z⊓x :=
        sup_le_sup_left
          (by
            rw [inf_comm, @inf_comm _ _ z] <;> exact hinf)
          _
      _ ≤ x := sup_le le_rfl inf_le_right
      

theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : x < y) (hinf : y⊓z ≤ x⊓z) : x⊔z < y⊔z :=
  lt_of_le_of_neₓ (sup_le_sup_right (le_of_ltₓ hxy) _) fun hsup =>
    ne_of_ltₓ hxy <| eq_of_le_of_inf_le_of_sup_le (le_of_ltₓ hxy) hinf (le_of_eqₓ hsup.symm)

theorem inf_lt_inf_of_lt_of_sup_le_sup (hxy : x < y) (hinf : y⊔z ≤ x⊔z) : x⊓z < y⊓z :=
  @sup_lt_sup_of_lt_of_inf_le_inf αᵒᵈ _ _ _ _ _ hxy hinf

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian. -/
theorem well_founded_lt_exact_sequence {β γ : Type _} [PartialOrderₓ β] [Preorderₓ γ]
    (h₁ : WellFounded ((· < ·) : β → β → Prop)) (h₂ : WellFounded ((· < ·) : γ → γ → Prop)) (K : α) (f₁ : β → α)
    (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂) (gi : GaloisInsertion g₂ g₁)
    (hf : ∀ a, f₁ (f₂ a) = a⊓K) (hg : ∀ a, g₁ (g₂ a) = a⊔K) : WellFounded ((· < ·) : α → α → Prop) :=
  Subrelation.wfₓ
    (fun A B hAB =>
      show Prod.Lex (· < ·) (· < ·) (f₂ A, g₂ A) (f₂ B, g₂ B) by
        simp only [Prod.lex_def, lt_iff_le_not_leₓ, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg, le_antisymm_iffₓ]
        simp only [gci.l_le_l_iff, gi.u_le_u_iff, ← lt_iff_le_not_leₓ, ← le_antisymm_iffₓ]
        cases' lt_or_eq_of_leₓ (inf_le_inf_right K (le_of_ltₓ hAB)) with h h
        · exact Or.inl h
          
        · exact Or.inr ⟨h, sup_lt_sup_of_lt_of_inf_le_inf hAB (le_of_eqₓ h.symm)⟩
          )
    (InvImage.wfₓ _ (Prod.lex_wf h₁ h₂))

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Noetherian, then `M` is Noetherian.  -/
theorem well_founded_gt_exact_sequence {β γ : Type _} [Preorderₓ β] [PartialOrderₓ γ]
    (h₁ : WellFounded ((· > ·) : β → β → Prop)) (h₂ : WellFounded ((· > ·) : γ → γ → Prop)) (K : α) (f₁ : β → α)
    (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂) (gi : GaloisInsertion g₂ g₁)
    (hf : ∀ a, f₁ (f₂ a) = a⊓K) (hg : ∀ a, g₁ (g₂ a) = a⊔K) : WellFounded ((· > ·) : α → α → Prop) :=
  @well_founded_lt_exact_sequence αᵒᵈ _ _ γᵒᵈ βᵒᵈ _ _ h₂ h₁ K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
def infIccOrderIsoIccSup (a b : α) : Set.Icc (a⊓b) a ≃o Set.Icc b (a⊔b) where
  toFun := fun x => ⟨x⊔b, ⟨le_sup_right, sup_le_sup_right x.Prop.2 b⟩⟩
  invFun := fun x => ⟨a⊓x, ⟨inf_le_inf_left a x.Prop.1, inf_le_left⟩⟩
  left_inv := fun x =>
    Subtype.ext
      (by
        change a⊓(↑x⊔b) = ↑x
        rw [sup_comm, ← inf_sup_assoc_of_le _ x.prop.2, sup_eq_right.2 x.prop.1])
  right_inv := fun x =>
    Subtype.ext
      (by
        change a⊓↑x⊔b = ↑x
        rw [inf_comm, inf_sup_assoc_of_le _ x.prop.1, inf_eq_left.2 x.prop.2])
  map_rel_iff' := fun x y => by
    simp only [Subtype.mk_le_mk, Equivₓ.coe_fn_mk, and_trueₓ, le_sup_right]
    rw [← Subtype.coe_le_coe]
    refine' ⟨fun h => _, fun h => sup_le_sup_right h _⟩
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le _ x.prop.2, sup_comm, ← sup_eq_right.2 y.prop.1,
      inf_sup_assoc_of_le _ y.prop.2, @sup_comm _ _ b]
    exact inf_le_inf_left _ h

end IsModularLattice

namespace IsCompl

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

/-- The diamond isomorphism between the intervals `set.Iic a` and `set.Ici b`. -/
def iicOrderIsoIci {a b : α} (h : IsCompl a b) : Set.Iic a ≃o Set.Ici b :=
  (OrderIso.setCongr (Set.Iic a) (Set.Icc (a⊓b) a) (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans (OrderIso.setCongr (Set.Icc b (a⊔b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))

end IsCompl

theorem is_modular_lattice_iff_inf_sup_inf_assoc [Lattice α] : IsModularLattice α ↔ ∀ x y z : α, x⊓z⊔y⊓z = (x⊓z⊔y)⊓z :=
  ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun x y z xz => by
      rw [← inf_eq_left.2 xz, h]⟩⟩

namespace DistribLattice

instance (priority := 100) [DistribLattice α] : IsModularLattice α :=
  ⟨fun x y z xz => by
    rw [inf_sup_right, inf_eq_left.2 xz]⟩

end DistribLattice

theorem Disjoint.disjoint_sup_right_of_disjoint_sup_left [Lattice α] [OrderBot α] [IsModularLattice α] {a b c : α}
    (h : Disjoint a b) (hsup : Disjoint (a⊔b) c) : Disjoint a (b⊔c) := by
  rw [Disjoint, ← h.eq_bot, sup_comm]
  apply le_inf inf_le_left
  apply (inf_le_inf_right (c⊔b) le_sup_right).trans
  rw [sup_comm, IsModularLattice.sup_inf_sup_assoc, hsup.eq_bot, bot_sup_eq]

theorem Disjoint.disjoint_sup_left_of_disjoint_sup_right [Lattice α] [OrderBot α] [IsModularLattice α] {a b c : α}
    (h : Disjoint b c) (hsup : Disjoint a (b⊔c)) : Disjoint (a⊔b) c := by
  rw [Disjoint.comm, sup_comm]
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  rwa [sup_comm, Disjoint.comm] at hsup

namespace IsModularLattice

variable [Lattice α] [IsModularLattice α] {a : α}

instance is_modular_lattice_Iic : IsModularLattice (Set.Iic a) :=
  ⟨fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x⊔↑y)⊓↑z ≤ ↑x⊔↑y⊓↑z)⟩

instance is_modular_lattice_Ici : IsModularLattice (Set.Ici a) :=
  ⟨fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x⊔↑y)⊓↑z ≤ ↑x⊔↑y⊓↑z)⟩

section IsComplemented

variable [BoundedOrder α] [IsComplemented α]

instance is_complemented_Iic : IsComplemented (Set.Iic a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_is_compl x
    ⟨⟨y⊓a, Set.mem_Iic.2 inf_le_right⟩, by
      constructor
      · change x⊓(y⊓a) ≤ ⊥
        -- improve lattice subtype API
        rw [← inf_assoc]
        exact le_transₓ inf_le_left hy.1
        
      · change a ≤ x⊔y⊓a
        -- improve lattice subtype API
        rw [← sup_inf_assoc_of_le _ (Set.mem_Iic.1 hx), top_le_iff.1 hy.2, top_inf_eq]
        ⟩⟩

instance is_complemented_Ici : IsComplemented (Set.Ici a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_is_compl x
    ⟨⟨y⊔a, Set.mem_Ici.2 le_sup_right⟩, by
      constructor
      · change x⊓(y⊔a) ≤ a
        -- improve lattice subtype API
        rw [← inf_sup_assoc_of_le _ (Set.mem_Ici.1 hx), le_bot_iff.1 hy.1, bot_sup_eq]
        
      · change ⊤ ≤ x⊔(y⊔a)
        -- improve lattice subtype API
        rw [← sup_assoc]
        exact le_transₓ hy.2 le_sup_left
        ⟩⟩

end IsComplemented

end IsModularLattice

