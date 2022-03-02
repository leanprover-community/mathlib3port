/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
import Mathbin.Data.Fin.VecNotation
import Mathbin.GroupTheory.Abelianization
import Mathbin.SetTheory.Cardinal
import Mathbin.GroupTheory.GeneralCommutator

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `derived_series G n` : the `n`th term in the derived series of `G`, defined by iterating
    `general_commutator` starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/


open Subgroup

variable {G G' : Type _} [Groupₓ G] [Groupₓ G'] {f : G →* G'}

section derivedSeries

variable (G)

/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def derivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅derivedSeries n,derivedSeries n⁆

@[simp]
theorem derived_series_zero : derivedSeries G 0 = ⊤ :=
  rfl

@[simp]
theorem derived_series_succ (n : ℕ) : derivedSeries G (n + 1) = ⁅derivedSeries G n,derivedSeries G n⁆ :=
  rfl

theorem derived_series_normal (n : ℕ) : (derivedSeries G n).Normal := by
  induction' n with n ih
  · exact (⊤ : Subgroup G).normal_of_characteristic
    
  · exact Subgroup.commutator_normal (derivedSeries G n) (derivedSeries G n)
    

@[simp]
theorem derived_series_one : derivedSeries G 1 = commutator G :=
  rfl

end derivedSeries

section CommutatorMap

theorem commutator_le_map_commutator {H₁ H₂ : Subgroup G} {K₁ K₂ : Subgroup G'} (h₁ : K₁ ≤ H₁.map f)
    (h₂ : K₂ ≤ H₂.map f) : ⁅K₁,K₂⁆ ≤ ⁅H₁,H₂⁆.map f := by
  rw [map_commutator]
  exact commutator_mono h₁ h₂

section DerivedSeriesMap

variable (f)

theorem map_derived_series_le_derived_series (n : ℕ) : (derivedSeries G n).map f ≤ derivedSeries G' n := by
  induction' n with n ih
  · simp only [derived_series_zero, le_top]
    
  · simp only [derived_series_succ, map_commutator, commutator_mono, ih]
    

variable {f}

theorem derived_series_le_map_derived_series (hf : Function.Surjective f) (n : ℕ) :
    derivedSeries G' n ≤ (derivedSeries G n).map f := by
  induction' n with n ih
  · rwa [derived_series_zero, derived_series_zero, top_le_iff, ← MonoidHom.range_eq_map, ←
      monoid_hom.range_top_iff_surjective.mpr]
    
  · simp only [*, derived_series_succ, commutator_le_map_commutator]
    

theorem map_derived_series_eq (hf : Function.Surjective f) (n : ℕ) : (derivedSeries G n).map f = derivedSeries G' n :=
  le_antisymmₓ (map_derived_series_le_derived_series f n) (derived_series_le_map_derived_series hf n)

end DerivedSeriesMap

end CommutatorMap

section Solvable

variable (G)

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
class IsSolvable : Prop where
  solvable : ∃ n : ℕ, derivedSeries G n = ⊥

theorem is_solvable_def : IsSolvable G ↔ ∃ n : ℕ, derivedSeries G n = ⊥ :=
  ⟨fun h => h.solvable, fun h => ⟨h⟩⟩

instance (priority := 100) CommGroupₓ.is_solvable {G : Type _} [CommGroupₓ G] : IsSolvable G := by
  use 1
  rw [eq_bot_iff, derived_series_one]
  calc commutator G ≤ (MonoidHom.id G).ker := Abelianization.commutator_subset_ker (MonoidHom.id G)_ = ⊥ := rfl

theorem is_solvable_of_comm {G : Type _} [hG : Groupₓ G] (h : ∀ a b : G, a * b = b * a) : IsSolvable G := by
  let hG' : CommGroupₓ G := { hG with mul_comm := h }
  cases' hG
  exact CommGroupₓ.is_solvable

theorem is_solvable_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : IsSolvable G :=
  ⟨⟨0, h⟩⟩

instance (priority := 100) is_solvable_of_subsingleton [Subsingleton G] : IsSolvable G :=
  is_solvable_of_top_eq_bot G
    (by
      ext <;> simp at *)

variable {G}

theorem solvable_of_solvable_injective (hf : Function.Injective f) [h : IsSolvable G'] : IsSolvable G := by
  rw [is_solvable_def] at *
  cases' h with n hn
  use n
  rw [← map_eq_bot_iff_of_injective _ hf]
  rw [eq_bot_iff] at *
  calc map f (derivedSeries G n) ≤ derivedSeries G' n := map_derived_series_le_derived_series f n _ ≤ ⊥ := hn

instance subgroup_solvable_of_solvable (H : Subgroup G) [h : IsSolvable G] : IsSolvable H :=
  solvable_of_solvable_injective (show Function.Injective (Subtype H) from Subtype.val_injective)

theorem solvable_of_surjective (hf : Function.Surjective f) [h : IsSolvable G] : IsSolvable G' := by
  rw [is_solvable_def] at *
  cases' h with n hn
  use n
  calc derivedSeries G' n = (derivedSeries G n).map f :=
      Eq.symm (map_derived_series_eq hf n)_ = (⊥ : Subgroup G).map f := by
      rw [hn]_ = ⊥ := map_bot f

instance solvable_quotient_of_solvable (H : Subgroup G) [H.Normal] [h : IsSolvable G] : IsSolvable (G ⧸ H) :=
  solvable_of_surjective
    (show Function.Surjective (QuotientGroup.mk' H) by
      tidy)

theorem solvable_of_ker_le_range {G' G'' : Type _} [Groupₓ G'] [Groupₓ G''] (f : G' →* G) (g : G →* G'')
    (hfg : g.ker ≤ f.range) [hG' : IsSolvable G'] [hG'' : IsSolvable G''] : IsSolvable G := by
  obtain ⟨n, hn⟩ := id hG''
  suffices ∀ k : ℕ, derivedSeries G (n + k) ≤ (derivedSeries G' k).map f by
    obtain ⟨m, hm⟩ := id hG'
    use n + m
    specialize this m
    rwa [hm, map_bot, le_bot_iff] at this
  intro k
  induction' k with k hk
  · rw [add_zeroₓ, derived_series_zero, ← MonoidHom.range_eq_map]
    refine' le_transₓ _ hfg
    rw [← map_eq_bot_iff, eq_bot_iff, ← hn]
    exact map_derived_series_le_derived_series g n
    
  · rw [Nat.add_succ, derived_series_succ, derived_series_succ]
    exact commutator_le_map_commutator hk hk
    

instance solvable_prod {G' : Type _} [Groupₓ G'] [h : IsSolvable G] [h' : IsSolvable G'] : IsSolvable (G × G') :=
  solvable_of_ker_le_range (MonoidHom.inl G G') (MonoidHom.snd G G') fun x hx => ⟨x.1, Prod.extₓ rfl hx.symm⟩

end Solvable

section IsSimpleGroup

variable [IsSimpleGroup G]

theorem IsSimpleGroup.derived_series_succ {n : ℕ} : derivedSeries G n.succ = commutator G := by
  induction' n with n ih
  · exact derived_series_one G
    
  rw [derived_series_succ, ih]
  cases' (commutator.normal G).eq_bot_or_eq_top with h h
  · rw [h, commutator_bot]
    
  · rwa [h]
    

theorem IsSimpleGroup.comm_iff_is_solvable : (∀ a b : G, a * b = b * a) ↔ IsSolvable G :=
  ⟨is_solvable_of_comm, fun ⟨⟨n, hn⟩⟩ => by
    cases n
    · rw [derived_series_zero] at hn
      intro a b
      refine' (mem_bot.1 _).trans (mem_bot.1 _).symm <;>
        · rw [← hn]
          exact mem_top _
          
      
    · rw [IsSimpleGroup.derived_series_succ] at hn
      intro a b
      rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← mem_bot, ← hn, commutator_eq_closure]
      exact subset_closure ⟨a, b, rfl⟩
      ⟩

end IsSimpleGroup

section PermNotSolvable

theorem not_solvable_of_mem_derived_series {g : G} (h1 : g ≠ 1) (h2 : ∀ n : ℕ, g ∈ derivedSeries G n) : ¬IsSolvable G :=
  mt (is_solvable_def _).mp
    (not_exists_of_forall_not fun n h => h1 (Subgroup.mem_bot.mp ((congr_argₓ (HasMem.Mem g) h).mp (h2 n))))

theorem Equivₓ.Perm.fin_5_not_solvable : ¬IsSolvable (Equivₓ.Perm (Finₓ 5)) := by
  let x : Equivₓ.Perm (Finₓ 5) :=
    ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by
      decide, by
      decide⟩
  let y : Equivₓ.Perm (Finₓ 5) :=
    ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by
      decide, by
      decide⟩
  let z : Equivₓ.Perm (Finₓ 5) :=
    ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by
      decide, by
      decide⟩
  have x_ne_one : x ≠ 1 := by
    rw [Ne.def, Equivₓ.ext_iff]
    decide
  have key : x = z * (x * (y * x * y⁻¹) * x⁻¹ * (y * x * y⁻¹)⁻¹) * z⁻¹ := by
    ext a
    decide!
  refine' not_solvable_of_mem_derived_series x_ne_one fun n => _
  induction' n with n ih
  · exact mem_top x
    
  · rw [key]
    exact
      (derived_series_normal _ _).conj_mem _
        (commutator_containment _ _ ih ((derived_series_normal _ _).conj_mem _ ih _)) _
    

theorem Equivₓ.Perm.not_solvable (X : Type _) (hX : 5 ≤ Cardinal.mk X) : ¬IsSolvable (Equivₓ.Perm X) := by
  intro h
  have key : Nonempty (Finₓ 5 ↪ X) := by
    rwa [← Cardinal.lift_mk_le, Cardinal.mk_fin, Cardinal.lift_nat_cast, Nat.cast_bit1, Nat.cast_bit0, Nat.cast_oneₓ,
      Cardinal.lift_id]
  exact
    Equivₓ.Perm.fin_5_not_solvable
      (solvable_of_solvable_injective (Equivₓ.Perm.via_embedding_hom_injective (Nonempty.some key)))

end PermNotSolvable

