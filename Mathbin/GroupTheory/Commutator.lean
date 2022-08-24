/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
import Mathbin.Data.Bracket
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Tactic.Group

/-!
# Commutators of Subgroups

If `G` is a group and `H₁ H₂ : subgroup G` then the commutator `⁅H₁, H₂⁆ : subgroup G`
is the subgroup of `G` generated by the commutators `h₁ * h₂ * h₁⁻¹ * h₂⁻¹`.

## Main definitions

* `⁅g₁, g₂⁆` : the commutator of the elements `g₁` and `g₂`
    (defined by `commutator_element` elsewhere).
* `⁅H₁, H₂⁆` : the commutator of the subgroups `H₁` and `H₂`.
-/


variable {G G' F : Type _} [Groupₓ G] [Groupₓ G'] [MonoidHomClass F G G'] (f : F) {g₁ g₂ g₃ g : G}

theorem commutator_element_eq_one_iff_mul_comm : ⁅g₁,g₂⁆ = 1 ↔ g₁ * g₂ = g₂ * g₁ := by
  rw [commutator_element_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem commutator_element_eq_one_iff_commute : ⁅g₁,g₂⁆ = 1 ↔ Commute g₁ g₂ :=
  commutator_element_eq_one_iff_mul_comm

theorem Commute.commutator_eq (h : Commute g₁ g₂) : ⁅g₁,g₂⁆ = 1 :=
  commutator_element_eq_one_iff_commute.mpr h

variable (g₁ g₂ g₃ g)

@[simp]
theorem commutator_element_one_right : ⁅g,(1 : G)⁆ = 1 :=
  (Commute.one_right g).commutator_eq

@[simp]
theorem commutator_element_one_left : ⁅(1 : G),g⁆ = 1 :=
  (Commute.one_left g).commutator_eq

@[simp]
theorem commutator_element_inv : ⁅g₁,g₂⁆⁻¹ = ⁅g₂,g₁⁆ := by
  simp_rw [commutator_element_def, mul_inv_rev, inv_invₓ, mul_assoc]

theorem map_commutator_element : (f ⁅g₁,g₂⁆ : G') = ⁅f g₁,f g₂⁆ := by
  simp_rw [commutator_element_def, map_mul f, map_inv f]

theorem conjugate_commutator_element : g₃ * ⁅g₁,g₂⁆ * g₃⁻¹ = ⁅g₃ * g₁ * g₃⁻¹,g₃ * g₂ * g₃⁻¹⁆ :=
  map_commutator_element (MulAut.conj g₃).toMonoidHom g₁ g₂

namespace Subgroup

/-- The commutator of two subgroups `H₁` and `H₂`. -/
instance commutator : HasBracket (Subgroup G) (Subgroup G) :=
  ⟨fun H₁ H₂ => closure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁,g₂⁆ = g }⟩

theorem commutator_def (H₁ H₂ : Subgroup G) : ⁅H₁,H₂⁆ = closure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁,g₂⁆ = g } :=
  rfl

variable {g₁ g₂ g₃} {H₁ H₂ H₃ K₁ K₂ : Subgroup G}

theorem commutator_mem_commutator (h₁ : g₁ ∈ H₁) (h₂ : g₂ ∈ H₂) : ⁅g₁,g₂⁆ ∈ ⁅H₁,H₂⁆ :=
  subset_closure ⟨g₁, h₁, g₂, h₂, rfl⟩

theorem commutator_le : ⁅H₁,H₂⁆ ≤ H₃ ↔ ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, ⁅g₁,g₂⁆ ∈ H₃ :=
  H₃.closure_le.trans ⟨fun h a b c d => h ⟨a, b, c, d, rfl⟩, fun h g ⟨a, b, c, d, h_eq⟩ => h_eq ▸ h a b c d⟩

theorem commutator_mono (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) : ⁅H₁,H₂⁆ ≤ ⁅K₁,K₂⁆ :=
  commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => commutator_mem_commutator (h₁ hg₁) (h₂ hg₂)

theorem commutator_eq_bot_iff_le_centralizer : ⁅H₁,H₂⁆ = ⊥ ↔ H₁ ≤ H₂.Centralizer := by
  rw [eq_bot_iff, commutator_le]
  refine' forall_congrₓ fun p => forall_congrₓ fun hp => forall_congrₓ fun q => forall_congrₓ fun hq => _
  rw [mem_bot, commutator_element_eq_one_iff_mul_comm, eq_comm]

/-- **The Three Subgroups Lemma** (via the Hall-Witt identity) -/
theorem commutator_commutator_eq_bot_of_rotate (h1 : ⁅⁅H₂,H₃⁆,H₁⁆ = ⊥) (h2 : ⁅⁅H₃,H₁⁆,H₂⁆ = ⊥) : ⁅⁅H₁,H₂⁆,H₃⁆ = ⊥ := by
  simp_rw [commutator_eq_bot_iff_le_centralizer, commutator_le, mem_centralizer_iff_commutator_eq_one, ←
    commutator_element_def] at h1 h2⊢
  intro x hx y hy z hz
  trans x * z * ⁅y,⁅z⁻¹,x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹,⁅y⁻¹,z⁆⁆⁻¹ * y⁻¹ * x⁻¹
  · group
    
  · rw [h1 _ (H₂.inv_mem hy) _ hz _ (H₁.inv_mem hx), h2 _ (H₃.inv_mem hz) _ (H₁.inv_mem hx) _ hy]
    group
    

variable (H₁ H₂)

theorem commutator_comm_le : ⁅H₁,H₂⁆ ≤ ⁅H₂,H₁⁆ :=
  commutator_le.mpr fun g₁ h₁ g₂ h₂ =>
    commutator_element_inv g₂ g₁ ▸ ⁅H₂,H₁⁆.inv_mem_iff.mpr (commutator_mem_commutator h₂ h₁)

theorem commutator_comm : ⁅H₁,H₂⁆ = ⁅H₂,H₁⁆ :=
  le_antisymmₓ (commutator_comm_le H₁ H₂) (commutator_comm_le H₂ H₁)

section Normal

instance commutator_normal [h₁ : H₁.Normal] [h₂ : H₂.Normal] : Normal ⁅H₁,H₂⁆ := by
  let base : Set G := { x | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁,g₂⁆ = x }
  change (closure base).Normal
  suffices h_base : base = Groupₓ.ConjugatesOfSet base
  · rw [h_base]
    exact Subgroup.normal_closure_normal
    
  refine' Set.Subset.antisymm Groupₓ.subset_conjugates_of_set fun a h => _
  simp_rw [Groupₓ.mem_conjugates_of_set_iff, is_conj_iff] at h
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩
  exact ⟨_, h₁.conj_mem c hc d, _, h₂.conj_mem e he d, (conjugate_commutator_element c e d).symm⟩

theorem commutator_def' [H₁.Normal] [H₂.Normal] : ⁅H₁,H₂⁆ = normalClosure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁,g₂⁆ = g } :=
  le_antisymmₓ closure_le_normal_closure (normal_closure_le_normal subset_closure)

theorem commutator_le_right [h : H₂.Normal] : ⁅H₁,H₂⁆ ≤ H₂ :=
  commutator_le.mpr fun g₁ h₁ g₂ h₂ => H₂.mul_mem (h.conj_mem g₂ h₂ g₁) (H₂.inv_mem h₂)

theorem commutator_le_left [H₁.Normal] : ⁅H₁,H₂⁆ ≤ H₁ :=
  commutator_comm H₂ H₁ ▸ commutator_le_right H₂ H₁

@[simp]
theorem commutator_bot_left : ⁅(⊥ : Subgroup G),H₁⁆ = ⊥ :=
  le_bot_iff.mp (commutator_le_left ⊥ H₁)

@[simp]
theorem commutator_bot_right : ⁅H₁,⊥⁆ = (⊥ : Subgroup G) :=
  le_bot_iff.mp (commutator_le_right H₁ ⊥)

theorem commutator_le_inf [Normal H₁] [Normal H₂] : ⁅H₁,H₂⁆ ≤ H₁⊓H₂ :=
  le_inf (commutator_le_left H₁ H₂) (commutator_le_right H₁ H₂)

end Normal

theorem map_commutator (f : G →* G') : map f ⁅H₁,H₂⁆ = ⁅map f H₁,map f H₂⁆ := by
  simp_rw [le_antisymm_iffₓ, map_le_iff_le_comap, commutator_le, mem_comap, map_commutator_element]
  constructor
  · intro p hp q hq
    exact commutator_mem_commutator (mem_map_of_mem _ hp) (mem_map_of_mem _ hq)
    
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [← map_commutator_element]
    exact mem_map_of_mem _ (commutator_mem_commutator hp hq)
    

variable {H₁ H₂}

theorem commutator_le_map_commutator {f : G →* G'} {K₁ K₂ : Subgroup G'} (h₁ : K₁ ≤ H₁.map f) (h₂ : K₂ ≤ H₂.map f) :
    ⁅K₁,K₂⁆ ≤ ⁅H₁,H₂⁆.map f :=
  (commutator_mono h₁ h₂).trans (ge_of_eqₓ (map_commutator H₁ H₂ f))

variable (H₁ H₂)

instance commutator_characteristic [h₁ : Characteristic H₁] [h₂ : Characteristic H₂] : Characteristic ⁅H₁,H₂⁆ :=
  characteristic_iff_le_map.mpr fun ϕ =>
    commutator_le_map_commutator (characteristic_iff_le_map.mp h₁ ϕ) (characteristic_iff_le_map.mp h₂ ϕ)

theorem commutator_prod_prod (K₁ K₂ : Subgroup G') : ⁅H₁.Prod K₁,H₂.Prod K₂⁆ = ⁅H₁,H₂⁆.Prod ⁅K₁,K₂⁆ := by
  apply le_antisymmₓ
  · rw [commutator_le]
    rintro ⟨p₁, p₂⟩ ⟨hp₁, hp₂⟩ ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩
    exact ⟨commutator_mem_commutator hp₁ hq₁, commutator_mem_commutator hp₂ hq₂⟩
    
  · rw [prod_le_iff]
    constructor <;>
      · rw [map_commutator]
        apply commutator_mono <;>
          simp [le_prod_iff, map_map, MonoidHom.fst_comp_inl, MonoidHom.snd_comp_inl, MonoidHom.fst_comp_inr,
            MonoidHom.snd_comp_inr]
        
    

/-- The commutator of direct product is contained in the direct product of the commutators.

See `commutator_pi_pi_of_finite` for equality given `fintype η`.
-/
theorem commutator_pi_pi_le {η : Type _} {Gs : η → Type _} [∀ i, Groupₓ (Gs i)] (H K : ∀ i, Subgroup (Gs i)) :
    ⁅Subgroup.pi Set.Univ H,Subgroup.pi Set.Univ K⁆ ≤ Subgroup.pi Set.Univ fun i => ⁅H i,K i⁆ :=
  commutator_le.mpr fun p hp q hq i hi => commutator_mem_commutator (hp i hi) (hq i hi)

/-- The commutator of a finite direct product is contained in the direct product of the commutators.
-/
theorem commutator_pi_pi_of_finite {η : Type _} [Finite η] {Gs : η → Type _} [∀ i, Groupₓ (Gs i)]
    (H K : ∀ i, Subgroup (Gs i)) :
    ⁅Subgroup.pi Set.Univ H,Subgroup.pi Set.Univ K⁆ = Subgroup.pi Set.Univ fun i => ⁅H i,K i⁆ := by
  classical
  apply le_antisymmₓ (commutator_pi_pi_le H K)
  · rw [pi_le_iff]
    intro i hi
    rw [map_commutator]
    apply commutator_mono <;>
      · rw [le_pi_iff]
        intro j hj
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        by_cases' h : j = i
        · subst h
          simpa using hx
          
        · simp [h, one_mem]
          
        
    

end Subgroup

