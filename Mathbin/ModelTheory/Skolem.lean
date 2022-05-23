/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.ElementaryMaps

/-!
# Skolem Functions and Downward Löwenheim–Skolem

## Main Definitions
* `first_order.language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results
* `first_order.language.exists_elementary_substructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.

## TODO
* Use `skolem₁` recursively to construct an actual Skolemization of a language.

-/


universe u v w

namespace FirstOrder

namespace Language

open Structure Cardinal

open Cardinal

variable (L : Language.{u, v}) {M : Type w} [Nonempty M] [L.Structure M]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
@[simps]
def skolem₁ : Language :=
  ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩

variable {L}

theorem card_functions_sum_skolem₁ : # (Σn, (L.Sum L.skolem₁).Functions n) = # (Σn, L.BoundedFormula Empty (n + 1)) :=
  by
  simp only [card_functions_sum, skolem₁_functions, lift_id', mk_sigma, sum_add_distrib']
  rw [add_commₓ, add_eq_max, max_eq_leftₓ]
  · refine' sum_le_sum _ _ fun n => _
    rw [← lift_le, lift_lift, lift_mk_le]
    refine' ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => _⟩⟩
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    rfl
    
  · rw [← mk_sigma]
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy => (Sigma.mk.inj xy).1)
    

theorem card_functions_sum_skolem₁_le : # (Σn, (L.Sum L.skolem₁).Functions n) ≤ max ω L.card := by
  rw [card_functions_sum_skolem₁]
  trans # (Σn, L.bounded_formula Empty n)
  · exact ⟨⟨Sigma.map Nat.succ fun _ => id, nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
    
  · refine' trans bounded_formula.card_le (lift_le.1 _)
    simp only [mk_empty, lift_zero, lift_uzero, zero_addₓ]
    

/-- The structure assigning each function symbol of `L.skolem₁` to a skolem function generated with
choice. -/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun n φ x => Classical.epsilon fun a => φ.realize default (Finₓ.snoc x a : _ → M), fun _ r => Empty.elim r⟩

namespace Substructure

theorem skolem₁_reduct_is_elementary (S : (L.Sum L.skolem₁).Substructure M) :
    (Lhom.sumInl.substructureReduct S).IsElementary := by
  apply (Lhom.sum_inl.substructure_reduct S).is_elementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := Lhom.sum_inr.on_function φ
  exact
    ⟨⟨fun_map φ' (coe ∘ x), S.fun_mem (Lhom.sum_inr.on_function φ) (coe ∘ x) fun i => (x i).2⟩,
      Classical.epsilon_spec ⟨a, h⟩⟩

/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
noncomputable def elementarySkolem₁Reduct (S : (L.Sum L.skolem₁).Substructure M) : L.ElementarySubstructure M :=
  ⟨Lhom.sumInl.substructureReduct S, fun _ => S.skolem₁_reduct_is_elementary⟩

theorem coe_sort_elementary_skolem₁_reduct (S : (L.Sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : Type w) = S :=
  rfl

end Substructure

open Substructure

variable (L) (M)

instance : Small (⊥ : (L.Sum L.skolem₁).Substructure M).elementarySkolem₁Reduct := by
  rw [coe_sort_elementary_skolem₁_reduct]
  infer_instance

theorem exists_small_elementary_substructure : ∃ S : L.ElementarySubstructure M, Small.{max u v} S :=
  ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩

variable {L M}

/-- The Downward Löwenheim–Skolem Theorem :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.  -/
theorem exists_elementary_substructure_card_eq (s : Set M) (κ : Cardinal.{max u v w}) (h1 : ω ≤ κ)
    (h2 : Cardinal.lift.{max u v} (# s) ≤ κ) (h3 : Cardinal.lift.{w} L.card ≤ κ)
    (h4 : κ ≤ Cardinal.lift.{max u v} (# M)) :
    ∃ S : L.ElementarySubstructure M, s ⊆ S ∧ Cardinal.lift.{max u v} (# S) = κ := by
  obtain ⟨s', rfl⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  refine'
    ⟨elementary_skolem₁_reduct (closure (L.sum L.skolem₁) (s ∪ Equivₓ.ulift.{max u v, w} '' s')),
      (s.subset_union_left _).trans subset_closure, _⟩
  rw [coe_sort_elementary_skolem₁_reduct]
  refine' le_antisymmₓ (lift_le.1 _) _
  · rw [lift_lift]
    refine' lift_card_closure_le.trans _
    rw [max_le_iff] at *
    rw [← lift_le, lift_lift, lift_le, add_commₓ, add_eq_max, max_le_iff, lift_id']
    · refine' ⟨h1, _, _⟩
      · refine' (lift_le.2 card_functions_sum_skolem₁_le).trans _
        rw [lift_max', lift_omega, max_le_iff, ← lift_lift, lift_id]
        exact ⟨h1, h3⟩
        
      · refine' (lift_le.2 (mk_union_le _ _)).trans _
        rw [lift_add, add_commₓ, mk_image_eq_lift _ _ equiv.ulift.injective, ← lift_lift, lift_id', add_eq_max h1,
          lift_id', max_eq_leftₓ h2]
        
      
    · rw [← lift_lift, lift_id, ← lift_omega, lift_le, ← infinite_iff]
      exact Infinite.of_injective (fun n => ⟨n, Sum.inr bounded_formula.falsum⟩) fun x y xy => (Sigma.ext_iff.1 xy).1
      
    
  · rw [← lift_le, lift_lift, ← mk_image_eq_lift _ s' equiv.ulift.injective, lift_mk_le]
    exact ⟨⟨Set.inclusion ((Set.subset_union_right _ _).trans subset_closure), Set.inclusion_injective _⟩⟩
    

end Language

end FirstOrder

