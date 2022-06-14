/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Cardinal.Ordinal
import Mathbin.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality

This file contains the definition of cofinality of an ordinal number and regular cardinals

## Main Definitions

* `ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `cardinal.is_limit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `cardinal.is_strong_limit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `cardinal.is_regular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `cardinal.is_inaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ is_regular c ∧ is_strong_limit c`.

## Main Statements

* `ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`
* `cardinal.univ_inaccessible`: The type of ordinals in `Type u` form an inaccessible cardinal
  (in `Type v` with `v > u`). This shows (externally) that in `Type u` there are at least `u`
  inaccessible cardinals.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.

## Tags

cofinality, regular cardinals, limits cardinals, inaccessible cardinals,
infinite pigeonhole principle
-/


noncomputable section

open Function Cardinal Set Order

open Classical Cardinal Ordinal

universe u v w

variable {α : Type _} {r : α → α → Prop}

/-! ### Cofinality of orders -/


namespace Order

/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) : Cardinal :=
  inf { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ # S = c }

/-- The set in the definition of `order.cof` is nonempty. -/
theorem cof_nonempty (r : α → α → Prop) [IsRefl α r] : { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ # S = c }.Nonempty :=
  ⟨_, Set.Univ, fun a => ⟨a, ⟨⟩, refl _⟩, rfl⟩

theorem cof_le (r : α → α → Prop) {S : Set α} (h : ∀ a, ∃ b ∈ S, r a b) : cof r ≤ # S :=
  cInf_le' ⟨S, h, rfl⟩

theorem le_cof {r : α → α → Prop} [IsRefl α r] (c : Cardinal) :
    c ≤ cof r ↔ ∀ {S : Set α}, (∀ a, ∃ b ∈ S, r a b) → c ≤ # S := by
  rw [cof, le_cInf_iff'' (cof_nonempty r)]
  use fun H S h => H _ ⟨S, h, rfl⟩
  rintro H d ⟨S, h, rfl⟩
  exact H h

end Order

theorem RelIso.cof_le_lift {α : Type u} {β : Type v} {r : α → α → Prop} {s} [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) ≤ Cardinal.lift.{max u v} (Order.cof s) := by
  rw [Order.cof, Order.cof, lift_Inf, lift_Inf, le_cInf_iff'' (nonempty_image_iff.2 (Order.cof_nonempty s))]
  rintro - ⟨-, ⟨u, H, rfl⟩, rfl⟩
  apply cInf_le'
  refine' ⟨_, ⟨f.symm '' u, fun a => _, rfl⟩, lift_mk_eq.{u, v, max u v}.2 ⟨(f.symm.toEquiv.Image u).symm⟩⟩
  rcases H (f a) with ⟨b, hb, hb'⟩
  refine' ⟨f.symm b, mem_image_of_mem _ hb, f.map_rel_iff.1 _⟩
  rwa [RelIso.apply_symm_apply]

theorem RelIso.cof_eq_lift {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) = Cardinal.lift.{max u v} (Order.cof s) :=
  (RelIso.cof_le_lift f).antisymm (RelIso.cof_le_lift f.symm)

theorem RelIso.cof_le {α β : Type u} {r : α → α → Prop} {s} [IsRefl β s] (f : r ≃r s) : Order.cof r ≤ Order.cof s :=
  lift_le.1 (RelIso.cof_le_lift f)

theorem RelIso.cof_eq {α β : Type u} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) : Order.cof r = Order.cof s :=
  lift_inj.1 (RelIso.cof_eq_lift f)

/-- Cofinality of a strict order `≺`. This is the smallest cardinality of a set `S : set α` such
that `∀ a, ∃ b ∈ S, ¬ b ≺ a`. -/
def StrictOrder.cof (r : α → α → Prop) : Cardinal :=
  Order.cof (swap rᶜ)

/-- The set in the definition of `order.strict_order.cof` is nonempty. -/
theorem StrictOrder.cof_nonempty (r : α → α → Prop) [IsIrrefl α r] :
    { c | ∃ S : Set α, Unbounded r S ∧ # S = c }.Nonempty :=
  @Order.cof_nonempty α _ (IsRefl.swap (rᶜ))

/-! ### Cofinality of ordinals -/


namespace Ordinal

/-- Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, a ≤ b`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOn (fun a => StrictOrder.cof a.R)
    (by
      rintro ⟨α, r, wo₁⟩ ⟨β, s, wo₂⟩ ⟨⟨f, hf⟩⟩
      have := wo₁
      have := wo₂
      apply @RelIso.cof_eq _ _ _ _ _ _
      · constructor
        exact fun a b => not_iff_not.2 hf
        
      · exact ⟨(IsWellOrder.is_irrefl r).1⟩
        
      · exact ⟨(IsWellOrder.is_irrefl s).1⟩
        )

theorem cof_type (r : α → α → Prop) [IsWellOrder α r] : (type r).cof = StrictOrder.cof r :=
  rfl

theorem le_cof_type [IsWellOrder α r] {c} : c ≤ cof (type r) ↔ ∀ S, Unbounded r S → c ≤ # S :=
  (le_cInf_iff'' (StrictOrder.cof_nonempty r)).trans
    ⟨fun H S h => H _ ⟨S, h, rfl⟩, by
      rintro H d ⟨S, h, rfl⟩
      exact H _ h⟩

theorem cof_type_le [IsWellOrder α r] {S : Set α} (h : Unbounded r S) : cof (type r) ≤ # S :=
  le_cof_type.1 le_rfl S h

theorem lt_cof_type [IsWellOrder α r] {S : Set α} : # S < cof (type r) → Bounded r S := by
  simpa using not_imp_not.2 cof_type_le

theorem cof_eq (r : α → α → Prop) [IsWellOrder α r] : ∃ S, Unbounded r S ∧ # S = cof (type r) :=
  Inf_mem (StrictOrder.cof_nonempty r)

theorem ord_cof_eq (r : α → α → Prop) [IsWellOrder α r] : ∃ S, Unbounded r S ∧ type (Subrel r S) = (cof (type r)).ord :=
  by
  let ⟨S, hS, e⟩ := cof_eq r
  let ⟨s, _, e'⟩ := Cardinal.ord_eq S
  let T : Set α := { a | ∃ aS : a ∈ S, ∀ b : S, s b ⟨_, aS⟩ → r b a }
  skip
  suffices
  · refine' ⟨T, this, le_antisymmₓ _ (Cardinal.ord_le.2 <| cof_type_le this)⟩
    rw [← e, e']
    refine'
      type_le'.2
        ⟨RelEmbedding.ofMonotone
            (fun a =>
              ⟨a,
                let ⟨aS, _⟩ := a.2
                aS⟩)
            fun a b h => _⟩
    rcases a with ⟨a, aS, ha⟩
    rcases b with ⟨b, bS, hb⟩
    change s ⟨a, _⟩ ⟨b, _⟩
    refine' ((trichotomous_of s _ _).resolve_left fun hn => _).resolve_left _
    · exact asymm h (ha _ hn)
      
    · intro e
      injection e with e
      subst b
      exact irrefl _ h
      
    
  · intro a
    have : { b : S | ¬r b a }.Nonempty :=
      let ⟨b, bS, ba⟩ := hS a
      ⟨⟨b, bS⟩, ba⟩
    let b := IsWellOrder.wf.min _ this
    have ba : ¬r b a := IsWellOrder.wf.min_mem _ this
    refine' ⟨b, ⟨b.2, fun c => not_imp_not.1 fun h => _⟩, ba⟩
    rw
      [show ∀ b : S, (⟨b, b.2⟩ : S) = b by
        intro b <;> cases b <;> rfl]
    exact IsWellOrder.wf.not_lt_min _ this (IsOrderConnected.neg_trans h ba)
    

/-! ### Cofinality of suprema and least strict upper bounds -/


private theorem card_mem_cof {o} : ∃ (ι : _)(f : ι → Ordinal), lsub.{u, u} f = o ∧ # ι = o.card :=
  ⟨_, _, lsub_typein o, mk_ordinal_out o⟩

/-- The set in the `lsub` characterization of `cof` is nonempty. -/
theorem cof_lsub_def_nonempty o : { a : Cardinal | ∃ (ι : _)(f : ι → Ordinal), lsub.{u, u} f = o ∧ # ι = a }.Nonempty :=
  ⟨_, card_mem_cof⟩

theorem cof_eq_Inf_lsub (o : Ordinal.{u}) :
    cof o = inf { a : Cardinal | ∃ (ι : Type u)(f : ι → Ordinal), lsub.{u, u} f = o ∧ # ι = a } := by
  refine' le_antisymmₓ (le_cInf (cof_lsub_def_nonempty o) _) (cInf_le' _)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← type_lt o]
    refine'
      (cof_type_le fun a => _).trans
        (@mk_le_of_injective _ _
          (fun s : typein ((· < ·) : o.out.α → o.out.α → Prop) ⁻¹' Set.Range f => Classical.some s.Prop) fun s t hst =>
          by
          let H := congr_arg f hst
          rwa [Classical.some_spec s.prop, Classical.some_spec t.prop, typein_inj, Subtype.coe_inj] at H)
    have := typein_lt_self a
    simp_rw [← hf, lt_lsub_iff]  at this
    cases' this with i hi
    refine' ⟨enum (· < ·) (f i) _, _, _⟩
    · rw [type_lt, ← hf]
      apply lt_lsub
      
    · rw [mem_preimage, typein_enum]
      exact mem_range_self i
      
    · rwa [← typein_le_typein, typein_enum]
      
    
  · rcases cof_eq (· < ·) with ⟨S, hS, hS'⟩
    let f : S → Ordinal := fun s => typein (· < ·) s.val
    refine'
      ⟨S, f, le_antisymmₓ (lsub_le fun i => typein_lt_self i) (le_of_forall_lt fun a ha => _), by
        rwa [type_lt o] at hS'⟩
    rw [← type_lt o] at ha
    rcases hS (enum (· < ·) a ha) with ⟨b, hb, hb'⟩
    rw [← typein_le_typein, typein_enum] at hb'
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)
    

@[simp]
theorem lift_cof o : (cof o).lift = cof o.lift :=
  induction_on o <| by
    intro α r _
    cases' lift_type r with _ e
    rw [e]
    apply le_antisymmₓ
    · refine' le_cof_type.2 fun S H => _
      have : (# (ULift.up ⁻¹' S)).lift ≤ # S :=
        ⟨⟨fun ⟨⟨x, h⟩⟩ => ⟨⟨x⟩, h⟩, fun e => by
            simp at e <;> congr <;> injection e⟩⟩
      refine' (Cardinal.lift_le.2 <| cof_type_le _).trans this
      exact fun a =>
        let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩
        ⟨b, bs, br⟩
      
    · rcases cof_eq r with ⟨S, H, e'⟩
      have : # (ULift.down ⁻¹' S) ≤ (# S).lift :=
        ⟨⟨fun ⟨⟨x⟩, h⟩ => ⟨⟨x, h⟩⟩, fun e => by
            simp at e <;> congr <;> injections⟩⟩
      rw [e'] at this
      refine' (cof_type_le _).trans this
      exact fun ⟨a⟩ =>
        let ⟨b, bs, br⟩ := H a
        ⟨⟨b⟩, bs, br⟩
      

theorem cof_le_card o : cof o ≤ card o := by
  rw [cof_eq_Inf_lsub]
  exact cInf_le' card_mem_cof

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by
  simpa using cof_le_card c.ord

theorem ord_cof_le (o : Ordinal.{u}) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

theorem exists_lsub_cof (o : Ordinal) : ∃ (ι : _)(f : ι → Ordinal), lsub.{u, u} f = o ∧ # ι = cof o := by
  rw [cof_eq_Inf_lsub]
  exact Inf_mem (cof_lsub_def_nonempty o)

theorem cof_lsub_le {ι} (f : ι → Ordinal) : cof (lsub.{u, u} f) ≤ # ι := by
  rw [cof_eq_Inf_lsub]
  exact cInf_le' ⟨ι, f, rfl, rfl⟩

theorem cof_lsub_le_lift {ι} (f : ι → Ordinal) : cof (lsub f) ≤ Cardinal.lift.{v, u} (# ι) := by
  rw [← mk_ulift]
  convert cof_lsub_le fun i : ULift ι => f i.down
  exact
    lsub_eq_of_range_eq.{u, max u v, max u v}
      (Set.ext fun x => ⟨fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩)

theorem le_cof_iff_lsub {o : Ordinal} {a : Cardinal} : a ≤ cof o ↔ ∀ {ι} f : ι → Ordinal, lsub.{u, u} f = o → a ≤ # ι :=
  by
  rw [cof_eq_Inf_lsub]
  exact
    (le_cInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩

theorem lsub_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift (# ι) < c.cof) (hf : ∀ i, f i < c) :
    lsub.{u, v} f < c :=
  lt_of_le_of_neₓ (lsub_le hf) fun h => by
    subst h
    exact (cof_lsub_le_lift f).not_lt hι

theorem lsub_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : # ι < c.cof) : (∀ i, f i < c) → lsub.{u, u} f < c :=
  lsub_lt_ord_lift
    (by
      rwa [(# ι).lift_id])

theorem cof_sup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup f) : cof (sup f) ≤ (# ι).lift := by
  rw [← sup_eq_lsub_iff_lt_sup] at H
  rw [H]
  exact cof_lsub_le_lift f

theorem cof_sup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup.{u, u} f) : cof (sup.{u, u} f) ≤ # ι := by
  rw [← (# ι).lift_id]
  exact cof_sup_le_lift H

theorem sup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift (# ι) < c.cof) (hf : ∀ i, f i < c) :
    sup.{u, v} f < c :=
  (sup_le_lsub.{u, v} f).trans_lt (lsub_lt_ord_lift hι hf)

theorem sup_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : # ι < c.cof) : (∀ i, f i < c) → sup.{u, u} f < c :=
  sup_lt_ord_lift
    (by
      rwa [(# ι).lift_id])

theorem sup_lt_lift {ι} {f : ι → Cardinal} {c : Cardinal} (hι : Cardinal.lift (# ι) < c.ord.cof) (hf : ∀ i, f i < c) :
    Cardinal.sup.{u, v} f < c := by
  rw [← ord_lt_ord, ← sup_ord]
  refine' sup_lt_ord_lift hι fun i => _
  rw [ord_lt_ord]
  apply hf

theorem sup_lt {ι} {f : ι → Cardinal} {c : Cardinal} (hι : # ι < c.ord.cof) :
    (∀ i, f i < c) → Cardinal.sup.{u, u} f < c :=
  sup_lt_lift
    (by
      rwa [(# ι).lift_id])

theorem nfp_family_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : (# ι).lift < cof c)
    (hf : ∀ i, ∀ b < c, ∀, f i b < c) {a} (ha : a < c) : nfpFamily.{u, v} f a < c := by
  refine' sup_lt_ord_lift ((Cardinal.lift_le.2 (mk_list_le_max ι)).trans_lt _) fun l => _
  · rw [lift_max]
    apply max_ltₓ _ hc'
    rwa [Cardinal.lift_aleph_0]
    
  · induction' l with i l H
    · exact ha
      
    · exact hf _ _ H
      
    

theorem nfp_family_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : # ι < cof c)
    (hf : ∀ i, ∀ b < c, ∀, f i b < c) {a} : a < c → nfpFamily.{u, u} f a < c :=
  nfp_family_lt_ord_lift hc
    (by
      rwa [(# ι).lift_id])
    hf

theorem nfp_bfamily_lt_ord_lift {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : o.card.lift < cof c) (hf : ∀ i hi, ∀ b < c, ∀, f i hi b < c) {a} : a < c → nfpBfamily.{u, v} o f a < c :=
  nfp_family_lt_ord_lift hc
    (by
      rwa [mk_ordinal_out])
    fun i => hf _ _

theorem nfp_bfamily_lt_ord {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : o.card < cof c) (hf : ∀ i hi, ∀ b < c, ∀, f i hi b < c) {a} : a < c → nfpBfamily.{u, u} o f a < c :=
  nfp_bfamily_lt_ord_lift hc
    (by
      rwa [o.card.lift_id])
    hf

theorem nfp_lt_ord {f : Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hf : ∀, ∀ i < c, ∀, f i < c) {a} :
    a < c → nfp f a < c :=
  nfp_family_lt_ord_lift hc
    (by
      simpa using cardinal.one_lt_aleph_0.trans hc)
    fun _ => hf

theorem exists_blsub_cof (o : Ordinal) : ∃ f : ∀, ∀ a < (cof o).ord, ∀, Ordinal, blsub.{u, u} _ f = o := by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι, hι']
  exact ⟨_, hf⟩

theorem le_cof_iff_blsub {b : Ordinal} {a : Cardinal} :
    a ≤ cof b ↔ ∀ {o} f : ∀, ∀ a < o, ∀, Ordinal, blsub.{u, u} o f = b → a ≤ o.card :=
  le_cof_iff_lsub.trans
    ⟨fun H o f hf => by
      simpa using H _ hf, fun H ι f hf => by
      rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩

theorem cof_blsub_le_lift {o} (f : ∀, ∀ a < o, ∀, Ordinal) : cof (blsub o f) ≤ Cardinal.lift.{v, u} o.card := by
  convert cof_lsub_le_lift _
  exact (mk_ordinal_out o).symm

theorem cof_blsub_le {o} (f : ∀, ∀ a < o, ∀, Ordinal) : cof (blsub.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f

theorem blsub_lt_ord_lift {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c : Ordinal} (ho : o.card.lift < c.cof)
    (hf : ∀ i hi, f i hi < c) : blsub.{u, v} o f < c :=
  lt_of_le_of_neₓ (blsub_le hf) fun h =>
    ho.not_le
      (by
        simpa [sup_ord, hf, h] using cof_blsub_le_lift.{u} f)

theorem blsub_lt_ord {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
    (hf : ∀ i hi, f i hi < c) : blsub.{u, u} o f < c :=
  blsub_lt_ord_lift
    (by
      rwa [o.card.lift_id])
    hf

theorem cof_bsup_le_lift {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} (H : ∀ i h, f i h < bsup o f) :
    cof (bsup o f) ≤ o.card.lift := by
  rw [← bsup_eq_blsub_iff_lt_bsup] at H
  rw [H]
  exact cof_blsub_le_lift f

theorem cof_bsup_le {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} :
    (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift

theorem bsup_lt_ord_lift {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c : Ordinal} (ho : o.card.lift < c.cof)
    (hf : ∀ i hi, f i hi < c) : bsup.{u, v} o f < c :=
  (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

theorem bsup_lt_ord {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c : Ordinal} (ho : o.card < c.cof) :
    (∀ i hi, f i hi < c) → bsup.{u, u} o f < c :=
  bsup_lt_ord_lift
    (by
      rwa [o.card.lift_id])

/-! ### Basic results -/


@[simp]
theorem cof_zero : cof 0 = 0 :=
  (cof_le_card 0).antisymm (Cardinal.zero_le _)

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
  ⟨(induction_on o) fun α r _ z =>
      let ⟨S, hl, e⟩ := cof_eq r
      type_eq_zero_iff_is_empty.2 <|
        ⟨fun a =>
          let ⟨b, h, _⟩ := hl a
          (mk_eq_zero_iff.1 (e.trans z)).elim' ⟨_, h⟩⟩,
    fun e => by
    simp [e]⟩

theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.Not

@[simp]
theorem cof_succ o : cof (succ o) = 1 := by
  apply le_antisymmₓ
  · refine' induction_on o fun α r _ => _
    change cof (type _) ≤ _
    rw [← (_ : # _ = 1)]
    apply cof_type_le
    · refine' fun a => ⟨Sum.inr PUnit.unit, Set.mem_singleton _, _⟩
      rcases a with (a | ⟨⟨⟨⟩⟩⟩) <;> simp [EmptyRelation]
      
    · rw [Cardinal.mk_fintype, Set.card_singleton]
      simp
      
    
  · rw [← Cardinal.succ_zero, succ_le_iff]
    simpa [lt_iff_le_and_ne, Cardinal.zero_le] using fun h => succ_ne_zero o (cof_eq_zero.1 (Eq.symm h))
    

@[simp]
theorem cof_eq_one_iff_is_succ {o} : cof.{u} o = 1 ↔ ∃ a, o = succ a :=
  ⟨(induction_on o) fun α r _ z => by
      skip
      rcases cof_eq r with ⟨S, hl, e⟩
      rw [z] at e
      cases'
        mk_ne_zero_iff.1
          (by
            rw [e] <;> exact one_ne_zero) with
        a
      refine'
        ⟨typein r a,
          Eq.symm <| Quotientₓ.sound ⟨RelIso.ofSurjective (RelEmbedding.ofMonotone _ fun x y => _) fun x => _⟩⟩
      · apply Sum.rec <;> [exact Subtype.val, exact fun _ => a]
        
      · rcases x with (x | ⟨⟨⟨⟩⟩⟩) <;> rcases y with (y | ⟨⟨⟨⟩⟩⟩) <;> simp [Subrel, Order.Preimage, EmptyRelation]
        exact x.2
        
      · suffices r x a ∨ ∃ b : PUnit, ↑a = x by
          simpa
        rcases trichotomous_of r x a with (h | h | h)
        · exact Or.inl h
          
        · exact Or.inr ⟨PUnit.unit, h.symm⟩
          
        · rcases hl x with ⟨a', aS, hn⟩
          rw [(_ : ↑a = a')] at h
          · exact absurd h hn
            
          refine' congr_arg Subtype.val (_ : a = ⟨a', aS⟩)
          have := le_one_iff_subsingleton.1 (le_of_eqₓ e)
          apply Subsingleton.elimₓ
          
        ,
    fun ⟨a, e⟩ => by
    simp [e]⟩

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀, ∀ b < o, ∀, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} hi hj, i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a

namespace IsFundamentalSequence

variable {a o : Ordinal.{u}} {f : ∀, ∀ b < o, ∀, Ordinal.{u}}

protected theorem cof_eq (hf : IsFundamentalSequence a o f) : a.cof.ord = o :=
  hf.1.antisymm' <| by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)

protected theorem strict_mono (hf : IsFundamentalSequence a o f) : ∀ {i j} hi hj, i < j → f i hi < f j hj :=
  hf.2.1

theorem blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a :=
  hf.2.2

theorem ord_cof (hf : IsFundamentalSequence a o f) :
    IsFundamentalSequence a a.cof.ord fun i hi =>
      f i
        (hi.trans_le
          (by
            rw [hf.cof_eq])) :=
  by
  have H := hf.cof_eq
  subst H
  exact hf

theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSequence o o fun a _ => a :=
  ⟨h, fun _ _ _ _ => id, blsub_id o⟩

protected theorem zero {f : ∀, ∀ b < (0 : Ordinal), ∀, Ordinal} : IsFundamentalSequence 0 0 f :=
  ⟨by
    rw [cof_zero, ord_zero], fun i j hi => (Ordinal.not_lt_zero i hi).elim, blsub_zero f⟩

protected theorem succ : IsFundamentalSequence (succ o) 1 fun _ _ => o := by
  refine' ⟨_, fun i j hi hj h => _, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
    
  · rw [lt_one_iff_zero] at hi hj
    rw [hi, hj] at h
    exact h.false.elim
    

protected theorem monotone (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o) (hj : j < o) (hij : i ≤ j) :
    f i hi ≤ f j hj := by
  rcases lt_or_eq_of_leₓ hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
    
  · rfl
    

theorem trans {a o o' : Ordinal.{u}} {f : ∀, ∀ b < o, ∀, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
    {g : ∀, ∀ b < o', ∀, Ordinal.{u}} (hg : IsFundamentalSequence o o' g) :
    IsFundamentalSequence a o' fun i hi =>
      f (g i hi)
        (by
          rw [← hg.2.2]
          apply lt_blsub) :=
  by
  refine' ⟨_, fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), _⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
    
  · rw [@blsub_comp.{u, u, u} o _ f (@is_fundamental_sequence.monotone _ _ f hf)]
    exact hf.2.2
    

end IsFundamentalSequence

/-- Every ordinal has a fundamental sequence. -/
theorem exists_fundamental_sequence (a : Ordinal.{u}) : ∃ f, IsFundamentalSequence a a.cof.ord f := by
  suffices ∃ o f, is_fundamental_sequence a o f by
    rcases this with ⟨o, f, hf⟩
    exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  have := wo
  let r' := Subrel r { i | ∀ j, r j i → f j < f i }
  let hrr' : r' ↪r r := Subrel.relEmbedding _ _
  have := hrr'.is_well_order
  refine'
    ⟨_, _, (type_le'.2 ⟨hrr'⟩).trans _, fun i j _ h _ => (enum r' j h).Prop _ _,
      le_antisymmₓ (blsub_le fun i hi => lsub_le_iff.1 hf.le _) _⟩
  · rw [← hι, hr]
    
  · change r (hrr'.1 _) (hrr'.1 _)
    rwa [hrr'.2, @enum_lt_enum _ r']
    
  · rw [← hf, lsub_le_iff]
    intro i
    suffices ∃ i' hi', f i ≤ bfamily_of_family' r' (fun i => f i) i' hi' by
      rcases this with ⟨i', hi', hfg⟩
      exact hfg.trans_lt (lt_blsub _ _ _)
    by_cases' h : ∀ j, r j i → f j < f i
    · refine' ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, _⟩
      rw [bfamily_of_family'_typein]
      rfl
      
    · push_neg  at h
      cases' wo.wf.min_mem _ h with hji hij
      refine' ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_leₓ _ hij⟩, typein_lt_type _ _, _⟩
      · by_contra' H
        exact (wo.wf.not_lt_min _ h ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
        
      · rwa [bfamily_of_family'_typein]
        
      
    

@[simp]
theorem cof_cof (a : Ordinal.{u}) : cof (cof a).ord = cof a := by
  cases' exists_fundamental_sequence a with f hf
  cases' exists_fundamental_sequence a.cof.ord with g hg
  exact ord_injective (hf.trans hg).cof_eq.symm

protected theorem IsNormal.is_fundamental_sequence {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) {a o}
    (ha : IsLimit a) {g} (hg : IsFundamentalSequence a o g) : IsFundamentalSequence (f a) o fun b hb => f (g b hb) := by
  refine' ⟨_, fun i j _ _ h => hf.strict_mono (hg.2.1 _ _ h), _⟩
  · rcases exists_lsub_cof (f a) with ⟨ι, f', hf', hι⟩
    rw [← hg.cof_eq, ord_le_ord, ← hι]
    suffices (lsub.{u, u} fun i => Inf { b : Ordinal | f' i ≤ f b }) = a by
      rw [← this]
      apply cof_lsub_le
    have H : ∀ i, ∃ b < a, f' i ≤ f b := fun i => by
      have := lt_lsub.{u, u} f' i
      rwa [hf', ← IsNormal.blsub_eq.{u, u} hf ha, lt_blsub_iff] at this
    refine' (lsub_le fun i => _).antisymm (le_of_forall_lt fun b hb => _)
    · rcases H i with ⟨b, hb, hb'⟩
      exact lt_of_le_of_ltₓ (cInf_le' hb') hb
      
    · have := hf.strict_mono hb
      rw [← hf', lt_lsub_iff] at this
      cases' this with i hi
      rcases H i with ⟨b, _, hb⟩
      exact ((le_cInf_iff'' ⟨b, hb⟩).2 fun c hc => hf.strict_mono.le_iff_le.1 (hi.trans hc)).trans_lt (lt_lsub _ i)
      
    
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (fun i j hi hj h => hf.strict_mono.monotone h) g hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha
    

theorem IsNormal.cof_eq {f} (hf : IsNormal f) {a} (ha : IsLimit a) : cof (f a) = cof a :=
  let ⟨g, hg⟩ := exists_fundamental_sequence a
  ord_injective (hf.IsFundamentalSequence ha hg).cof_eq

theorem IsNormal.cof_le {f} (hf : IsNormal f) a : cof a ≤ cof (f a) := by
  rcases zero_or_succ_or_limit a with (rfl | ⟨b, rfl⟩ | ha)
  · rw [cof_zero]
    exact zero_le _
    
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_ne_zero, ← Ordinal.pos_iff_ne_zero]
    exact (Ordinal.zero_le (f b)).trans_lt (hf.1 b)
    
  · rw [hf.cof_eq ha]
    

@[simp]
theorem cof_add (a b : Ordinal) : b ≠ 0 → cof (a + b) = cof b := fun h => by
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
    
  · rw [add_succ, cof_succ, cof_succ]
    
  · exact (add_is_normal a).cof_eq hb
    

theorem aleph_0_le_cof {o} : ℵ₀ ≤ cof o ↔ IsLimit o := by
  rcases zero_or_succ_or_limit o with (rfl | ⟨o, rfl⟩ | l)
  · simp [not_zero_is_limit, Cardinal.aleph_0_ne_zero]
    
  · simp [not_succ_is_limit, Cardinal.one_lt_aleph_0]
    
  · simp [l]
    refine' le_of_not_ltₓ fun h => _
    cases' Cardinal.lt_aleph_0.1 h with n e
    have := cof_cof o
    rw [e, ord_nat] at this
    cases n
    · simp at e
      simpa [e, not_zero_is_limit] using l
      
    · rw [← nat_cast_succ, cof_succ] at this
      rw [← this, cof_eq_one_iff_is_succ] at e
      rcases e with ⟨a, rfl⟩
      exact not_succ_is_limit _ l
      
    

@[simp]
theorem aleph'_cof {o : Ordinal} (ho : o.IsLimit) : (aleph' o).ord.cof = o.cof :=
  aleph'_is_normal.cof_eq ho

@[simp]
theorem aleph_cof {o : Ordinal} (ho : o.IsLimit) : (aleph o).ord.cof = o.cof :=
  aleph_is_normal.cof_eq ho

@[simp]
theorem cof_omega : cof ω = ℵ₀ :=
  (aleph_0_le_cof.2 omega_is_limit).antisymm' <| by
    rw [← card_omega]
    apply cof_le_card

theorem cof_eq' (r : α → α → Prop) [IsWellOrder α r] (h : IsLimit (type r)) :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ # S = cof (type r) :=
  let ⟨S, H, e⟩ := cof_eq r
  ⟨S, fun a =>
    let a' := enum r _ (h.2 _ (typein_lt_type r a))
    let ⟨b, h, ab⟩ := H a'
    ⟨b, h,
      (IsOrderConnected.conn a b a' <|
            (typein_lt_typein r).1
              (by
                rw [typein_enum]
                exact lt_succ (typein _ _))).resolve_right
        ab⟩,
    e⟩

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ :=
  le_antisymmₓ (cof_le_card _)
    (by
      refine' le_of_forall_lt fun c h => _
      rcases lt_univ'.1 h with ⟨c, rfl⟩
      rcases@cof_eq Ordinal.{u} (· < ·) _ with ⟨S, H, Se⟩
      rw [univ, ← lift_cof, ← Cardinal.lift_lift, Cardinal.lift_lt, ← Se]
      refine' lt_of_not_geₓ fun h => _
      cases' Cardinal.lift_down h with a e
      refine' Quotientₓ.induction_on a (fun α e => _) e
      cases' Quotientₓ.exact e with f
      have f := equiv.ulift.symm.trans f
      let g := fun a => (f a).1
      let o := succ (sup.{u, u} g)
      rcases H o with ⟨b, h, l⟩
      refine' l (lt_succ_iff.2 _)
      rw [←
        show g (f.symm ⟨b, h⟩) = b by
          dsimp' [g] <;> simp ]
      apply le_sup)

/-! ### Infinite pigeonhole principle -/


/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : IsWellOrder α r] {s : Set (Set α)}
    (h₁ : Unbounded r <| ⋃₀s) (h₂ : # s < StrictOrder.cof r) : ∃ x ∈ s, Unbounded r x := by
  by_contra' h
  simp_rw [not_unbounded_iff]  at h
  let f : s → α := fun x : s => wo.wf.sup x (h x.1 x.2)
  refine' h₂.not_le (le_transₓ (cInf_le' ⟨range f, fun x => _, rfl⟩) mk_range_le)
  rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩
  exact ⟨f ⟨c, hc⟩, mem_range_self _, fun hxz => hxy (trans (wo.wf.lt_sup _ hy) hxz)⟩

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_Union {α β : Type u} (r : α → α → Prop) [wo : IsWellOrder α r] (s : β → Set α)
    (h₁ : Unbounded r <| ⋃ x, s x) (h₂ : # β < StrictOrder.cof r) : ∃ x : β, Unbounded r (s x) := by
  rw [← sUnion_range] at h₁
  rcases unbounded_of_unbounded_sUnion r h₁ (mk_range_le.trans_lt h₂) with ⟨_, ⟨x, rfl⟩, u⟩
  exact ⟨x, u⟩

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ℵ₀ ≤ # β) (h₂ : # α < (# β).ord.cof) :
    ∃ a : α, # (f ⁻¹' {a}) = # β := by
  have : ∃ a, # β ≤ # (f ⁻¹' {a}) := by
    by_contra' h
    apply mk_univ.not_lt
    rw [← preimage_univ, ← Union_of_singleton, preimage_Union]
    exact
      mk_Union_le_sum_mk.trans_lt
        ((sum_le_sup _).trans_lt <| mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (sup_lt h₂ h))
  cases' this with x h
  refine' ⟨x, h.antisymm' _⟩
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩

/-- Pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ # β) (h₁ : ℵ₀ ≤ θ)
    (h₂ : # α < θ.ord.cof) : ∃ a : α, θ ≤ # (f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  cases' infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂ with a ha
  use a
  rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective

theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal) (hθ : θ ≤ # s) (h₁ : ℵ₀ ≤ θ)
    (h₂ : # α < θ.ord.cof) : ∃ (a : α)(t : Set β)(h : t ⊆ s), θ ≤ # t ∧ ∀ ⦃x⦄ hx : x ∈ t, f ⟨x, h hx⟩ = a := by
  cases' infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha
  refine' ⟨a, { x | ∃ h, f ⟨x, h⟩ = a }, _, _, _⟩
  · rintro x ⟨hx, hx'⟩
    exact hx
    
  · refine' ha.trans (ge_of_eq <| Quotientₓ.sound ⟨Equivₓ.trans _ (Equivₓ.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_set_of_eq]
    
  rintro x ⟨hx, hx'⟩
  exact hx'

end Ordinal

/-! ### Regular and inaccessible cardinals -/


namespace Cardinal

open Ordinal

-- mathport name: «expr ^ »
local infixr:0 "^" => @pow Cardinal.{u} Cardinal Cardinal.hasPow

/-- A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ℵ₀` is a limit cardinal by this definition. -/
def IsLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀, ∀ x < c, ∀, succ x < c

theorem IsLimit.ne_zero {c} (h : IsLimit c) : c ≠ 0 :=
  h.1

theorem IsLimit.succ_lt {x c} (h : IsLimit c) : x < c → succ x < c :=
  h.2 x

theorem IsLimit.aleph_0_le {c} (h : IsLimit c) : ℵ₀ ≤ c := by
  by_contra' h'
  rcases lt_aleph_0.1 h' with ⟨_ | n, rfl⟩
  · exact h.1.irrefl
    
  · simpa using h.2 n
    

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ℵ₀` is a strong limit by this definition. -/
def IsStrongLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀, ∀ x < c, ∀, (2^x) < c

theorem IsStrongLimit.ne_zero {c} (h : IsStrongLimit c) : c ≠ 0 :=
  h.1

theorem IsStrongLimit.two_power_lt {x c} (h : IsStrongLimit c) : x < c → (2^x) < c :=
  h.2 x

theorem is_strong_limit_aleph_0 : IsStrongLimit ℵ₀ :=
  ⟨aleph_0_ne_zero, fun x hx => by
    rcases lt_aleph_0.1 hx with ⟨n, rfl⟩
    exact_mod_cast nat_lt_aleph_0 (pow 2 n)⟩

theorem IsStrongLimit.is_limit {c} (H : IsStrongLimit c) : IsLimit c :=
  ⟨H.1, fun x h => (succ_le_of_lt <| cantor x).trans_lt (H.2 _ h)⟩

theorem is_limit_aleph_0 : IsLimit ℵ₀ :=
  is_strong_limit_aleph_0.IsLimit

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def IsRegular (c : Cardinal) : Prop :=
  ℵ₀ ≤ c ∧ c ≤ c.ord.cof

theorem IsRegular.aleph_0_le {c : Cardinal} (H : c.IsRegular) : ℵ₀ ≤ c :=
  H.1

theorem IsRegular.cof_eq {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2

theorem IsRegular.pos {c : Cardinal} (H : c.IsRegular) : 0 < c :=
  aleph_0_pos.trans_le H.1

theorem IsRegular.ord_pos {c : Cardinal} (H : c.IsRegular) : 0 < c.ord := by
  rw [Cardinal.lt_ord]
  exact H.pos

theorem is_regular_cof {o : Ordinal} (h : o.IsLimit) : IsRegular o.cof :=
  ⟨aleph_0_le_cof.2 h, (cof_cof o).Ge⟩

theorem is_regular_aleph_0 : IsRegular ℵ₀ :=
  ⟨le_rfl, by
    simp ⟩

theorem is_regular_succ {c : Cardinal.{u}} (h : ℵ₀ ≤ c) : IsRegular (succ c) :=
  ⟨h.trans (le_succ c),
    succ_le_of_lt
      (by
        cases' Quotientₓ.exists_rep (@succ Cardinal _ _ c) with α αe
        simp at αe
        rcases ord_eq α with ⟨r, wo, re⟩
        skip
        have := ord_is_limit (h.trans (le_succ _))
        rw [← αe, re] at this⊢
        rcases cof_eq' r this with ⟨S, H, Se⟩
        rw [← Se]
        apply lt_imp_lt_of_le_imp_le fun h => mul_le_mul_right' h c
        rw [mul_eq_self h, ← succ_le_iff, ← αe, ← sum_const']
        refine' le_transₓ _ (sum_le_sum (fun x => card (typein r x)) _ fun i => _)
        · simp only [← card_typein, ← mk_sigma]
          exact
            ⟨embedding.of_surjective (fun x => x.2.1) fun a =>
                let ⟨b, h, ab⟩ := H a
                ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩⟩
          
        · rw [← lt_succ_iff, ← lt_ord, ← αe, re]
          apply typein_lt_type
          )⟩

theorem is_regular_aleph_one : IsRegular (aleph 1) := by
  rw [← succ_aleph_0]
  exact is_regular_succ le_rfl

theorem is_regular_aleph'_succ {o : Ordinal} (h : ω ≤ o) : IsRegular (aleph' (succ o)) := by
  rw [aleph'_succ]
  exact is_regular_succ (aleph_0_le_aleph'.2 h)

theorem is_regular_aleph_succ (o : Ordinal) : IsRegular (aleph (succ o)) := by
  rw [aleph_succ]
  exact is_regular_succ (aleph_0_le_aleph o)

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (w : # α < # β) (w' : ℵ₀ ≤ # α) :
    ∃ a : α, # α < # (f ⁻¹' {a}) := by
  simp_rw [← succ_le_iff]
  exact
    Ordinal.infinite_pigeonhole_card f (succ (# α)) (succ_le_of_lt w) (w'.trans (lt_succ _).le)
      ((lt_succ _).trans_le (is_regular_succ w').2.Ge)

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type _} (f : β → α) (w : # α < # β) (w' : Infinite α) :
    ∃ a : α, Infinite (f ⁻¹' {a}) := by
  simp_rw [Cardinal.infinite_iff]  at w'⊢
  cases' infinite_pigeonhole_card_lt f w w' with a ha
  exact ⟨a, w'.trans ha.le⟩

/-- If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
theorem le_range_of_union_finset_eq_top {α β : Type _} [Infinite β] (f : α → Finset β) (w : (⋃ a, (f a : Set β)) = ⊤) :
    # β ≤ # (Range f) := by
  have k : _root_.infinite (range f) := by
    rw [infinite_coe_iff]
    apply mt (union_finset_finite_of_range_finite f)
    rw [w]
    exact infinite_univ
  by_contra h
  simp only [not_leₓ] at h
  let u : ∀ b, ∃ a, b ∈ f a := fun b => by
    simpa using (w.ge : _) (Set.mem_univ b)
  let u' : β → range f := fun b =>
    ⟨f (u b).some, by
      simp ⟩
  have v' :
    ∀ a,
      u' ⁻¹'
          {⟨f a, by
              simp ⟩} ≤
        f a :=
    by
    rintro a p m
    simp at m
    rw [← m]
    apply fun b => (u b).some_spec
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h k
  exact (@Infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).False

theorem lsub_lt_ord_lift_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : Cardinal.lift (# ι) < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  lsub_lt_ord_lift
    (by
      rwa [hc.cof_eq])

theorem lsub_lt_ord_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : # ι < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  lsub_lt_ord
    (by
      rwa [hc.cof_eq])

theorem sup_lt_ord_lift_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : Cardinal.lift (# ι) < c) :
    (∀ i, f i < c.ord) → Ordinal.sup f < c.ord :=
  sup_lt_ord_lift
    (by
      rwa [hc.cof_eq])

theorem sup_lt_ord_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : # ι < c) :
    (∀ i, f i < c.ord) → Ordinal.sup f < c.ord :=
  sup_lt_ord
    (by
      rwa [hc.cof_eq])

theorem blsub_lt_ord_lift_of_is_regular {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c} (hc : IsRegular c)
    (ho : Cardinal.lift o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord_lift
    (by
      rwa [hc.cof_eq])

theorem blsub_lt_ord_of_is_regular {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c} (hc : IsRegular c) (ho : o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord
    (by
      rwa [hc.cof_eq])

theorem bsup_lt_ord_lift_of_is_regular {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord_lift
    (by
      rwa [hc.cof_eq])

theorem bsup_lt_ord_of_is_regular {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} {c} (hc : IsRegular c) (hι : o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord
    (by
      rwa [hc.cof_eq])

theorem sup_lt_lift_of_is_regular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c) (hι : Cardinal.lift (# ι) < c) :
    (∀ i, f i < c) → sup.{u, v} f < c :=
  sup_lt_lift
    (by
      rwa [hc.cof_eq])

theorem sup_lt_of_is_regular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c) (hι : # ι < c) :
    (∀ i, f i < c) → sup.{u, u} f < c :=
  sup_lt
    (by
      rwa [hc.cof_eq])

theorem sum_lt_lift_of_is_regular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} (# ι) < c) (hf : ∀ i, f i < c) : sum f < c :=
  (sum_le_sup_lift _).trans_lt <| mul_lt_of_lt hc.1 hι (sup_lt_lift_of_is_regular hc hι hf)

theorem sum_lt_of_is_regular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c) (hι : # ι < c) :
    (∀ i, f i < c) → sum f < c :=
  sum_lt_lift_of_is_regular.{u, u} hc
    (by
      rwa [lift_id])

theorem nfp_family_lt_ord_lift_of_is_regular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : (# ι).lift < c) (hc' : c ≠ ℵ₀) (hf : ∀ i, ∀ b < c.ord, ∀, f i b < c.ord) {a} (ha : a < c.ord) :
    nfpFamily.{u, v} f a < c.ord := by
  apply nfp_family_lt_ord_lift _ _ hf ha <;> rwa [hc.cof_eq]
  exact lt_of_le_of_neₓ hc.1 hc'.symm

theorem nfp_family_lt_ord_of_is_regular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : # ι < c)
    (hc' : c ≠ ℵ₀) {a} (hf : ∀ i, ∀ b < c.ord, ∀, f i b < c.ord) : a < c.ord → nfpFamily.{u, u} f a < c.ord :=
  nfp_family_lt_ord_lift_of_is_regular hc
    (by
      rwa [lift_id])
    hc' hf

theorem nfp_bfamily_lt_ord_lift_of_is_regular {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (ho : o.card.lift < c) (hc' : c ≠ ℵ₀) (hf : ∀ i hi, ∀ b < c.ord, ∀, f i hi b < c.ord) {a} :
    a < c.ord → nfpBfamily.{u, v} o f a < c.ord :=
  nfp_family_lt_ord_lift_of_is_regular hc
    (by
      rwa [mk_ordinal_out])
    hc' fun i => hf _ _

theorem nfp_bfamily_lt_ord_of_is_regular {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal → Ordinal} {c} (hc : IsRegular c)
    (ho : o.card < c) (hc' : c ≠ ℵ₀) (hf : ∀ i hi, ∀ b < c.ord, ∀, f i hi b < c.ord) {a} :
    a < c.ord → nfpBfamily.{u, u} o f a < c.ord :=
  nfp_bfamily_lt_ord_lift_of_is_regular hc
    (by
      rwa [lift_id])
    hc' hf

theorem nfp_lt_ord_of_is_regular {f : Ordinal → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀, ∀ i < c.ord, ∀, f i < c.ord) {a} : a < c.ord → nfp f a < c.ord :=
  nfp_lt_ord
    (by
      rw [hc.cof_eq]
      exact lt_of_le_of_neₓ hc.1 hc'.symm)
    hf

theorem deriv_family_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : (# ι).lift < c)
    (hc' : c ≠ ℵ₀) (hf : ∀ i, ∀ b < c.ord, ∀, f i b < c.ord) {a} : a < c.ord → derivFamily.{u, v} f a < c.ord := by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_eq]
    exact lt_of_le_of_neₓ hc.1 hc'.symm
  apply a.limit_rec_on
  · rw [deriv_family_zero]
    exact
      nfp_family_lt_ord_lift hω
        (by
          rwa [hc.cof_eq])
        hf
    
  · intro b hb hb'
    rw [deriv_family_succ]
    exact
      nfp_family_lt_ord_lift hω
        (by
          rwa [hc.cof_eq])
        hf ((ord_is_limit hc.1).2 _ (hb ((lt_succ b).trans hb')))
    
  · intro b hb H hb'
    rw [deriv_family_limit f hb]
    exact
      bsup_lt_ord_of_is_regular hc (ord_lt_ord.1 ((ord_card_le b).trans_lt hb')) fun o' ho' => H o' ho' (ho'.trans hb')
    

theorem deriv_family_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : # ι < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i, ∀ b < c.ord, ∀, f i b < c.ord) {a} : a < c.ord → derivFamily.{u, u} f a < c.ord :=
  deriv_family_lt_ord_lift hc
    (by
      rwa [lift_id])
    hc' hf

theorem deriv_bfamily_lt_ord_lift {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : o.card.lift < c) (hc' : c ≠ ℵ₀) (hf : ∀ i hi, ∀ b < c.ord, ∀, f i hi b < c.ord) {a} :
    a < c.ord → derivBfamily.{u, v} o f a < c.ord :=
  deriv_family_lt_ord_lift hc
    (by
      rwa [mk_ordinal_out])
    hc' fun i => hf _ _

theorem deriv_bfamily_lt_ord {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) (hc' : c ≠ ℵ₀) (hf : ∀ i hi, ∀ b < c.ord, ∀, f i hi b < c.ord) {a} :
    a < c.ord → derivBfamily.{u, u} o f a < c.ord :=
  deriv_bfamily_lt_ord_lift hc
    (by
      rwa [lift_id])
    hc' hf

theorem deriv_lt_ord {f : Ordinal.{u} → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀, ∀ i < c.ord, ∀, f i < c.ord) {a} : a < c.ord → deriv f a < c.ord :=
  deriv_family_lt_ord_lift hc
    (by
      simpa using cardinal.one_lt_aleph_0.trans (lt_of_le_of_neₓ hc.1 hc'.symm))
    hc' fun _ => hf

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def IsInaccessible (c : Cardinal) :=
  ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c

theorem IsInaccessible.mk {c} (h₁ : ℵ₀ < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀, ∀ x < c, ∀, (2^x) < c) : IsInaccessible c :=
  ⟨h₁, ⟨h₁.le, h₂⟩, (aleph_0_pos.trans h₁).ne', h₃⟩

-- Lean's foundations prove the existence of ℵ₀ many inaccessible cardinals
theorem univ_inaccessible : IsInaccessible univ.{u, v} :=
  IsInaccessible.mk
    (by
      simpa using lift_lt_univ' ℵ₀)
    (by
      simp )
    fun c h => by
    rcases lt_univ'.1 h with ⟨c, rfl⟩
    rw [← lift_two_power.{u, max (u + 1) v}]
    apply lift_lt_univ'

theorem lt_power_cof {c : Cardinal.{u}} : ℵ₀ ≤ c → c < (c^cof c.ord) :=
  (Quotientₓ.induction_on c) fun α h => by
    rcases ord_eq α with ⟨r, wo, re⟩
    skip
    have := ord_is_limit h
    rw [mk_def, re] at this⊢
    rcases cof_eq' r this with ⟨S, H, Se⟩
    have := sum_lt_prod (fun a : S => # { x // r x a }) (fun _ => # α) fun i => _
    · simp only [Cardinal.prod_const, Cardinal.lift_id, ← Se, ← mk_sigma, power_def] at this⊢
      refine' lt_of_le_of_ltₓ _ this
      refine' ⟨embedding.of_surjective _ _⟩
      · exact fun x => x.2.1
        
      · exact fun a =>
          let ⟨b, h, ab⟩ := H a
          ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩
        
      
    · have := typein_lt_type r i
      rwa [← re, lt_ord] at this
      

theorem lt_cof_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < cof (b^a).ord := by
  have b0 : b ≠ 0 := (zero_lt_one.trans b1).ne'
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a b0)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof (ha.trans <| (cantor' _ b1).le)

end Cardinal

