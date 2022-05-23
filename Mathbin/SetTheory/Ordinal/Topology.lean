/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Ordinal.Arithmetic
import Mathbin.Topology.Algebra.Order.Basic

/-!
### Topology of ordinals

We prove some miscellaneous results involving the order topology of ordinals.

### Main results

* `ordinal.is_closed_iff_sup` / `ordinal.is_closed_iff_bsup`: A set of ordinals is closed iff it's
  closed under suprema.
* `ordinal.is_normal_iff_strict_mono_and_continuous`: A characterization of normal ordinal
  functions.
* `ordinal.enum_ord_is_normal_iff_is_closed`: The function enumerating the ordinals of a set is
  normal iff the set is closed.
-/


noncomputable section

universe u v

open Cardinal

namespace Ordinal

instance : TopologicalSpace Ordinal.{u} :=
  Preorderₓ.topology Ordinal.{u}

instance : OrderTopology Ordinal.{u} :=
  ⟨rfl⟩

theorem is_open_singleton_iff {o : Ordinal} : IsOpen ({o} : Set Ordinal) ↔ ¬IsLimit o := by
  refine' ⟨fun h ho => _, fun ho => _⟩
  · obtain ⟨a, b, hab, hab'⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0, Ordinal.pos_iff_ne_zero.2 ho.1⟩ ⟨_, lt_succ_self o⟩).1 (h.mem_nhds rfl)
    have hao := ho.2 a hab.1
    exact hao.ne (hab' ⟨lt_succ_self a, hao.trans hab.2⟩)
    
  · rcases zero_or_succ_or_limit o with (rfl | ⟨a, ha⟩ | ho')
    · convert is_open_gt' (1 : Ordinal)
      ext
      exact ordinal.lt_one_iff_zero.symm
      
    · convert @is_open_Ioo _ _ _ _ a (o + 1)
      ext b
      refine' ⟨fun hb => _, _⟩
      · rw [Set.mem_singleton_iff.1 hb]
        refine' ⟨_, lt_succ_self o⟩
        rw [ha]
        exact lt_succ_self a
        
      · rintro ⟨hb, hb'⟩
        apply le_antisymmₓ (lt_succ.1 hb')
        rw [ha]
        exact Ordinal.succ_le.2 hb
        
      
    · exact (ho ho').elim
      
    

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem is_open_iff (s : Set Ordinal) : IsOpen s ↔ ∀, ∀ o ∈ s, ∀, IsLimit o → ∃ a < o, Set.Ioo a o ⊆ s := by
  classical
  refine' ⟨_, fun h => _⟩
  · rw [is_open_iff_generate_intervals]
    intro h o hos ho
    have ho₀ := Ordinal.pos_iff_ne_zero.2 ho.1
    induction' h with t ht t u ht hu ht' hu' t ht H
    · rcases ht with ⟨a, rfl | rfl⟩
      · exact ⟨a, hos, fun b hb => hb.1⟩
        
      · exact ⟨0, ho₀, fun b hb => hb.2.trans hos⟩
        
      
    · exact ⟨0, ho₀, fun b _ => Set.mem_univ b⟩
      
    · rcases ht' hos.1 with ⟨a, ha, ha'⟩
      rcases hu' hos.2 with ⟨b, hb, hb'⟩
      exact
        ⟨_, max_ltₓ ha hb, fun c hc =>
          ⟨ha' ⟨(le_max_leftₓ a b).trans_lt hc.1, hc.2⟩, hb' ⟨(le_max_rightₓ a b).trans_lt hc.1, hc.2⟩⟩⟩
      
    · rcases hos with ⟨u, hu, hu'⟩
      rcases H u hu hu' with ⟨a, ha, ha'⟩
      exact ⟨a, ha, fun b hb => ⟨u, hu, ha' hb⟩⟩
      
    
  · let f : s → Set Ordinal := fun o =>
      if ho : is_limit o.val then Set.Ioo (Classical.some (h o.val o.Prop ho)) (o + 1) else {o.val}
    have : ∀ a, IsOpen (f a) := fun a => by
      change IsOpen (dite _ _ _)
      split_ifs
      · exact is_open_Ioo
        
      · rwa [is_open_singleton_iff]
        
    convert is_open_Union this
    ext o
    refine' ⟨fun ho => Set.mem_Union.2 ⟨⟨o, ho⟩, _⟩, _⟩
    · split_ifs with ho'
      · refine' ⟨_, lt_succ_self o⟩
        cases' Classical.some_spec (h o ho ho') with H
        exact H
        
      · exact Set.mem_singleton o
        
      
    · rintro ⟨t, ⟨a, ht⟩, hoa⟩
      change dite _ _ _ = t at ht
      split_ifs  at ht with ha <;> subst ht
      · cases' Classical.some_spec (h a.val a.prop ha) with H has
        rcases lt_or_eq_of_leₓ (lt_succ.1 hoa.2) with (hoa' | rfl)
        · exact has ⟨hoa.1, hoa'⟩
          
        · exact a.prop
          
        
      · convert a.prop
        
      
    

theorem mem_closure_iff_sup {s : Set Ordinal.{u}} {a : Ordinal.{u}} :
    a ∈ Closure s ↔ ∃ (ι : Type u)(_ : Nonempty ι)(f : ι → Ordinal.{u}), (∀ i, f i ∈ s) ∧ sup.{u, u} f = a := by
  refine' mem_closure_iff.trans ⟨fun h => _, _⟩
  · by_cases' has : a ∈ s
    · exact
        ⟨PUnit, by
          infer_instance, fun _ => a, fun _ => has, sup_const a⟩
      
    · have H := fun hba : b < a => h _ (@is_open_Ioo _ _ _ _ b (a + 1)) ⟨hba, lt_succ_self a⟩
      let f : a.out.α → Ordinal := fun i => Classical.some (H (typein (· < ·) i) (typein_lt_self i))
      have hf : ∀ i, f i ∈ Set.Ioo (typein (· < ·) i) (a + 1) ∩ s := fun i => Classical.some_spec (H _ _)
      rcases eq_zero_or_pos a with (rfl | ha₀)
      · rcases h _ (is_open_singleton_iff.2 not_zero_is_limit) rfl with ⟨b, hb, hb'⟩
        rw [Set.mem_singleton_iff.1 hb] at *
        exact (has hb').elim
        
      refine'
        ⟨_, out_nonempty_iff_ne_zero.2 (Ordinal.pos_iff_ne_zero.1 ha₀), f, fun i => (hf i).2,
          le_antisymmₓ (sup_le fun i => lt_succ.1 (hf i).1.2) _⟩
      by_contra' h
      cases' H _ h with b hb
      rcases eq_or_lt_of_le (lt_succ.1 hb.1.2) with (rfl | hba)
      · exact has hb.2
        
      · have :
          b <
            f
              (enum (· < ·) b
                (by
                  rwa [type_lt])) :=
          by
          have :=
            (hf
                  (enum (· < ·) b
                    (by
                      rwa [type_lt]))).1.1
          rwa [typein_enum] at this
        have : b ≤ sup.{u, u} f := this.le.trans (le_sup f _)
        exact this.not_lt hb.1.1
        
      
    
  · rintro ⟨ι, ⟨i⟩, f, hf, rfl⟩ t ht hat
    cases' eq_zero_or_pos (sup.{u, u} f) with ha₀ ha₀
    · rw [ha₀] at hat
      use 0, hat
      convert hf i
      exact (sup_eq_zero_iff.1 ha₀ i).symm
      
    rcases(mem_nhds_iff_exists_Ioo_subset' ⟨0, ha₀⟩ ⟨_, lt_succ_self _⟩).1 (ht.mem_nhds hat) with
      ⟨b, c, ⟨hab, hac⟩, hbct⟩
    cases' lt_sup.1 hab with i hi
    exact ⟨_, hbct ⟨hi, (le_sup.{u, u} f i).trans_lt hac⟩, hf i⟩
    

theorem mem_closed_iff_sup {s : Set Ordinal.{u}} {a : Ordinal.{u}} (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u)(hι : Nonempty ι)(f : ι → Ordinal.{u}), (∀ i, f i ∈ s) ∧ sup.{u, u} f = a := by
  rw [← mem_closure_iff_sup, hs.closure_eq]

theorem mem_closure_iff_bsup {s : Set Ordinal.{u}} {a : Ordinal.{u}} :
    a ∈ Closure s ↔
      ∃ (o : Ordinal)(ho : o ≠ 0)(f : ∀, ∀ a < o, ∀, Ordinal.{u}), (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  mem_closure_iff_sup.trans
    ⟨fun ⟨ι, ⟨i⟩, f, hf, ha⟩ =>
      ⟨_, fun h => (type_eq_zero_iff_is_empty.1 h).elim i, bfamilyOfFamily f, fun i hi => hf _, by
        rwa [bsup_eq_sup]⟩,
      fun ⟨o, ho, f, hf, ha⟩ =>
      ⟨_, out_nonempty_iff_ne_zero.2 ho, familyOfBfamily o f, fun i => hf _ _, by
        rwa [sup_eq_bsup]⟩⟩

theorem mem_closed_iff_bsup {s : Set Ordinal.{u}} {a : Ordinal.{u}} (hs : IsClosed s) :
    a ∈ s ↔ ∃ (o : Ordinal)(ho : o ≠ 0)(f : ∀, ∀ a < o, ∀, Ordinal.{u}), (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  by
  rw [← mem_closure_iff_bsup, hs.closure_eq]

theorem is_closed_iff_sup {s : Set Ordinal.{u}} :
    IsClosed s ↔ ∀ {ι : Type u} hι : Nonempty ι f : ι → Ordinal.{u}, (∀ i, f i ∈ s) → sup.{u, u} f ∈ s := by
  use fun hs ι hι f hf => (mem_closed_iff_sup hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_is_closed]
  intro h x hx
  rcases mem_closure_iff_sup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf

theorem is_closed_iff_bsup {s : Set Ordinal.{u}} :
    IsClosed s ↔
      ∀ {o : Ordinal.{u}} ho : o ≠ 0 f : ∀, ∀ a < o, ∀, Ordinal.{u}, (∀ i hi, f i hi ∈ s) → bsup.{u, u} o f ∈ s :=
  by
  rw [is_closed_iff_sup]
  refine' ⟨fun H o ho f hf => H (out_nonempty_iff_ne_zero.2 ho) _ _, fun H ι hι f hf => _⟩
  · exact fun i => hf _ _
    
  · rw [← bsup_eq_sup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _
    

theorem is_limit_of_mem_frontier {s : Set Ordinal} {o : Ordinal} (ho : o ∈ Frontier s) : IsLimit o := by
  simp only [frontier_eq_closure_inter_closure, Set.mem_inter_iff, mem_closure_iff] at ho
  by_contra h
  rw [← is_open_singleton_iff] at h
  rcases ho.1 _ h rfl with ⟨a, ha, ha'⟩
  rcases ho.2 _ h rfl with ⟨b, hb, hb'⟩
  rw [Set.mem_singleton_iff] at *
  subst ha
  subst hb
  exact hb' ha'

theorem is_normal_iff_strict_mono_and_continuous (f : Ordinal.{u} → Ordinal.{u}) :
    IsNormal f ↔ StrictMono f ∧ Continuous f := by
  refine' ⟨fun h => ⟨h.StrictMono, _⟩, _⟩
  · rw [continuous_def]
    intro s hs
    rw [is_open_iff] at *
    intro o ho ho'
    rcases hs _ ho (h.is_limit ho') with ⟨a, ha, has⟩
    rw [← IsNormal.bsup_eq.{u, u} h ho', lt_bsup] at ha
    rcases ha with ⟨b, hb, hab⟩
    exact ⟨b, hb, fun c hc => Set.mem_preimage.2 (has ⟨hab.trans (h.strict_mono hc.1), h.strict_mono hc.2⟩)⟩
    
  · rw [is_normal_iff_strict_mono_limit]
    rintro ⟨h, h'⟩
    refine' ⟨h, fun o ho a h => _⟩
    suffices : o ∈ f ⁻¹' Set.Iic a
    exact Set.mem_preimage.1 this
    rw [mem_closed_iff_sup (IsClosed.preimage h' (@is_closed_Iic _ _ _ _ a))]
    exact ⟨_, out_nonempty_iff_ne_zero.2 ho.1, typein (· < ·), fun i => h _ (typein_lt_self i), sup_typein_limit ho.2⟩
    

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (b «expr < » a)
theorem enum_ord_is_normal_iff_is_closed {S : Set Ordinal.{u}} (hS : S.Unbounded (· < ·)) :
    IsNormal (enumOrd S) ↔ IsClosed S := by
  have HS := enum_ord_strict_mono hS
  refine'
    ⟨fun h => is_closed_iff_sup.2 fun ι hι f hf => _, fun h =>
      (is_normal_iff_strict_mono_limit _).2 ⟨HS, fun a ha o H => _⟩⟩
  · let g : ι → Ordinal.{u} := fun i => (enum_ord_order_iso hS).symm ⟨_, hf i⟩
    suffices enum_ord S (sup.{u, u} g) = sup.{u, u} f by
      rw [← this]
      exact enum_ord_mem hS _
    rw [IsNormal.sup.{u, u, u} h g hι]
    congr
    ext
    change ((enum_ord_order_iso hS) _).val = f x
    rw [OrderIso.apply_symm_apply]
    
  · rw [is_closed_iff_bsup] at h
    suffices : enum_ord S a ≤ bsup.{u, u} a fun b _ : b < a => enum_ord S b
    exact this.trans (bsup_le H)
    cases' enum_ord_surjective hS _ (h ha.1 (fun b hb => enum_ord S b) fun b hb => enum_ord_mem hS b) with b hb
    rw [← hb]
    apply HS.monotone
    by_contra' hba
    apply (HS (lt_succ_self b)).not_le
    rw [hb]
    exact le_bsup.{u, u} _ _ (ha.2 _ hba)
    

end Ordinal

