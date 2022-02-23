/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathbin.SetTheory.CardinalOrdinal

/-!
# Cofinality

This file contains the definition of cofinality of a ordinal number and regular cardinals

## Main Definitions

* `ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `cardinal.is_limit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `cardinal.is_strong_limit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `cardinal.is_regular c` means that `c` is a regular cardinal: `ω ≤ c ∧ c.ord.cof = c`.
* `cardinal.is_inaccessible c` means that `c` is strongly inaccessible:
  `ω < c ∧ is_regular c ∧ is_strong_limit c`.

## Main Statements

* `ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ω`
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

open Function Cardinal Set

open_locale Classical Cardinal

universe u v w

variable {α : Type _} {r : α → α → Prop}

namespace Order

/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) [IsRefl α r] : Cardinal :=
  @Cardinal.min { S : Set α // ∀ a, ∃ b ∈ S, r a b } ⟨⟨Set.Univ, fun a => ⟨a, ⟨⟩, refl _⟩⟩⟩ fun S => # S

theorem cof_le (r : α → α → Prop) [IsRefl α r] {S : Set α} (h : ∀ a, ∃ b ∈ S, r a b) : Order.cof r ≤ # S :=
  le_transₓ (Cardinal.min_le _ ⟨S, h⟩) le_rfl

theorem le_cof {r : α → α → Prop} [IsRefl α r] (c : Cardinal) :
    c ≤ Order.cof r ↔ ∀ {S : Set α} h : ∀ a, ∃ b ∈ S, r a b, c ≤ # S := by
  rw [Order.cof, Cardinal.le_min]
  exact ⟨fun H S h => H ⟨S, h⟩, fun H ⟨S, h⟩ => H h⟩

end Order

theorem RelIso.Cof.aux {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) ≤ Cardinal.lift.{max u v} (Order.cof s) := by
  rw [Order.cof, Order.cof, lift_min, lift_min, Cardinal.le_min]
  intro S
  cases' S with S H
  simp only [comp, coe_sort_coe_base, Subtype.coe_mk]
  refine' le_transₓ (min_le _ _) _
  · exact
      ⟨f ⁻¹' S, fun a =>
        let ⟨b, bS, h⟩ := H (f a)
        ⟨f.symm b, by
          simp [bS, ← f.map_rel_iff, h, -coe_fn_coe_base, -coe_fn_coe_trans, PrincipalSeg.coe_coe_fn',
            InitialSeg.coe_coe_fn]⟩⟩
    
  · exact
      lift_mk_le.{u, v, max u v}.2
        ⟨⟨fun ⟨x, h⟩ => ⟨f x, h⟩, fun h₃ => by
            congr <;> injection h₃ with h' <;> exact f.to_equiv.injective h'⟩⟩
    

theorem RelIso.cof {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) = Cardinal.lift.{max u v} (Order.cof s) :=
  le_antisymmₓ (RelIso.Cof.aux f) (RelIso.Cof.aux f.symm)

def StrictOrder.cof (r : α → α → Prop) [h : IsIrrefl α r] : Cardinal :=
  @Order.cof α (fun x y => ¬r y x) ⟨h.1⟩

namespace Ordinal

/-- Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, ¬(b > a)`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  Quot.liftOn o (fun ⟨α, r, _⟩ => StrictOrder.cof r)
    (by
      rintro ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨⟨f, hf⟩⟩
      rw [← Cardinal.lift_inj]
      apply RelIso.cof ⟨f, _⟩
      simp [hf])

theorem cof_type (r : α → α → Prop) [IsWellOrder α r] : (type r).cof = StrictOrder.cof r :=
  rfl

theorem le_cof_type [IsWellOrder α r] {c} : c ≤ cof (type r) ↔ ∀ S : Set α, (∀ a, ∃ b ∈ S, ¬r b a) → c ≤ # S := by
  dsimp [cof, StrictOrder.cof, Order.cof, type, Quotientₓ.mk, Quot.liftOn] <;>
    rw [Cardinal.le_min, Subtype.forall] <;> rfl

theorem cof_type_le [IsWellOrder α r] (S : Set α) (h : ∀ a, ∃ b ∈ S, ¬r b a) : cof (type r) ≤ # S :=
  le_cof_type.1 le_rfl S h

theorem lt_cof_type [IsWellOrder α r] (S : Set α) (hl : # S < cof (type r)) : ∃ a, ∀, ∀ b ∈ S, ∀, r b a :=
  not_forall_not.1 fun h => not_le_of_lt hl <| cof_type_le S fun a => not_ball.1 (h a)

theorem cof_eq (r : α → α → Prop) [IsWellOrder α r] : ∃ S : Set α, (∀ a, ∃ b ∈ S, ¬r b a) ∧ # S = cof (type r) :=
  have : ∃ i, cof (type r) = _ := by
    dsimp [cof, Order.cof, type, Quotientₓ.mk, Quot.liftOn]
    apply Cardinal.min_eq
  let ⟨⟨S, hl⟩, e⟩ := this
  ⟨S, hl, e.symm⟩

theorem ord_cof_eq (r : α → α → Prop) [IsWellOrder α r] :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, ¬r b a) ∧ type (Subrel r S) = (cof (type r)).ord := by
  let ⟨S, hS, e⟩ := cof_eq r
  let ⟨s, _, e'⟩ := Cardinal.ord_eq S
  let T : Set α := { a | ∃ aS : a ∈ S, ∀ b : S, s b ⟨_, aS⟩ → r b a }
  skip
  suffices
  · refine' ⟨T, this, le_antisymmₓ _ (Cardinal.ord_le.2 <| cof_type_le T this)⟩
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
    

theorem lift_cof o : (cof o).lift = cof o.lift :=
  induction_on o <| by
    intros α r _
    cases' lift_type r with _ e
    rw [e]
    apply le_antisymmₓ
    · refine' le_cof_type.2 fun S H => _
      have : (# (ULift.up ⁻¹' S)).lift ≤ # S :=
        ⟨⟨fun ⟨⟨x, h⟩⟩ => ⟨⟨x⟩, h⟩, fun e => by
            simp at e <;> congr <;> injection e⟩⟩
      refine' le_transₓ (Cardinal.lift_le.2 <| cof_type_le _ _) this
      exact fun a =>
        let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩
        ⟨b, bs, br⟩
      
    · rcases cof_eq r with ⟨S, H, e'⟩
      have : # (ULift.down ⁻¹' S) ≤ (# S).lift :=
        ⟨⟨fun ⟨⟨x⟩, h⟩ => ⟨⟨x, h⟩⟩, fun e => by
            simp at e <;> congr <;> injections⟩⟩
      rw [e'] at this
      refine' le_transₓ (cof_type_le _ _) this
      exact fun ⟨a⟩ =>
        let ⟨b, bs, br⟩ := H a
        ⟨⟨b⟩, bs, br⟩
      

theorem cof_le_card o : cof o ≤ card o :=
  (induction_on o) fun α r _ => by
    skip
    have : # (@Set.Univ α) = card (type r) := Quotientₓ.sound ⟨Equivₓ.Set.univ _⟩
    rw [← this]
    exact cof_type_le Set.Univ fun a => ⟨a, ⟨⟩, irrefl a⟩

theorem cof_ord_le (c : Cardinal) : cof c.ord ≤ c := by
  simpa using cof_le_card c.ord

@[simp]
theorem cof_zero : cof 0 = 0 :=
  le_antisymmₓ
    (by
      simpa using cof_le_card 0)
    (Cardinal.zero_le _)

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
      
    
  · rw [← Cardinal.succ_zero, Cardinal.succ_le]
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
            
          refine' congr_argₓ Subtype.val (_ : a = ⟨a', aS⟩)
          have := le_one_iff_subsingleton.1 (le_of_eqₓ e)
          apply Subsingleton.elimₓ
          
        ,
    fun ⟨a, e⟩ => by
    simp [e]⟩

@[simp]
theorem cof_add (a b : Ordinal) : b ≠ 0 → cof (a + b) = cof b :=
  (induction_on a) fun α r _ =>
    (induction_on b) fun β s _ b0 => by
      skip
      change cof (type _) = _
      refine' eq_of_forall_le_iff fun c => _
      rw [le_cof_type, le_cof_type]
      constructor <;> intro H S hS
      · refine' le_transₓ (H { a | Sum.recOn a (∅ : Set α) S } fun a => _) ⟨⟨_, _⟩⟩
        · cases' a with a b
          · cases' type_ne_zero_iff_nonempty.1 b0 with b
            rcases hS b with ⟨b', bs, _⟩
            exact
              ⟨Sum.inr b', bs, by
                simp ⟩
            
          · rcases hS b with ⟨b', bs, h⟩
            exact
              ⟨Sum.inr b', bs, by
                simp [h]⟩
            
          
        · exact fun a =>
            match a with
            | ⟨Sum.inr b, h⟩ => ⟨b, h⟩
          
        · exact fun a b =>
            match a, b with
            | ⟨Sum.inr a, h₁⟩, ⟨Sum.inr b, h₂⟩, h => by
              congr <;> injection h
          
        
      · refine' le_transₓ (H (Sum.inr ⁻¹' S) fun a => _) ⟨⟨_, _⟩⟩
        · rcases hS (Sum.inr a) with ⟨a' | b', bs, h⟩ <;> simp at h
          · cases h
            
          · exact ⟨b', bs, h⟩
            
          
        · exact fun ⟨a, h⟩ => ⟨_, h⟩
          
        · exact fun h => by
            injection h with h <;> congr <;> injection h
          
        

@[simp]
theorem cof_cof (o : Ordinal) : cof (cof o).ord = cof o :=
  le_antisymmₓ
      (le_transₓ (cof_le_card _)
        (by
          simp )) <|
    (induction_on o) fun α r _ => by
      let ⟨S, hS, e₁⟩ := ord_cof_eq r
      let ⟨T, hT, e₂⟩ := cof_eq (Subrel r S)
      rw [e₁] at e₂
      rw [← e₂]
      refine' le_transₓ (cof_type_le { a | ∃ h, (Subtype.mk a h : S) ∈ T } fun a => _) ⟨⟨_, _⟩⟩
      · rcases hS a with ⟨b, bS, br⟩
        rcases hT ⟨b, bS⟩ with ⟨⟨c, cS⟩, cT, cs⟩
        exact ⟨c, ⟨cS, cT⟩, IsOrderConnected.neg_trans cs br⟩
        
      · exact fun ⟨a, h⟩ => ⟨⟨a, h.fst⟩, h.snd⟩
        
      · exact fun h => by
          injection h with h <;> congr <;> injection h
        

theorem omega_le_cof {o} : ω ≤ cof o ↔ IsLimit o := by
  rcases zero_or_succ_or_limit o with (rfl | ⟨o, rfl⟩ | l)
  · simp [not_zero_is_limit, Cardinal.omega_ne_zero]
    
  · simp [not_succ_is_limit, Cardinal.one_lt_omega]
    
  · simp [l]
    refine' le_of_not_ltₓ fun h => _
    cases' Cardinal.lt_omega.1 h with n e
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
theorem cof_omega : cof omega = ω :=
  le_antisymmₓ
    (by
      rw [← card_omega] <;> apply cof_le_card)
    (omega_le_cof.2 omega_is_limit)

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
                rw [typein_enum] <;> apply Ordinal.lt_succ_self)).resolve_right
        ab⟩,
    e⟩

theorem cof_sup_le_lift {ι} (f : ι → Ordinal) (H : ∀ i, f i < sup f) : cof (sup f) ≤ (# ι).lift := by
  generalize e : sup f = o
  refine' Ordinal.induction_on o _ e
  intros α r _ e'
  rw [e'] at H
  refine' le_transₓ (cof_type_le (Set.Range fun i => enum r _ (H i)) _) ⟨embedding.of_surjective _ _⟩
  · intro a
    by_contra h
    apply not_le_of_lt (typein_lt_type r a)
    rw [← e', sup_le]
    intro i
    have h : ∀ x : ι, r (enum r (f x) _) a := by
      simpa using h
    simpa only [typein_enum] using le_of_ltₓ ((typein_lt_typein r).2 (h i))
    
  · exact fun i => ⟨_, Set.mem_range_self i.1⟩
    
  · intro a
    rcases a with ⟨_, i, rfl⟩
    exact
      ⟨⟨i⟩, by
        simp ⟩
    

theorem cof_sup_le {ι} (f : ι → Ordinal) (H : ∀ i, f i < sup.{u, u} f) : cof (sup.{u, u} f) ≤ # ι := by
  simpa using cof_sup_le_lift.{u, u} f H

theorem cof_bsup_le_lift {o : Ordinal} :
    ∀ f : ∀, ∀ a < o, ∀, Ordinal, (∀ i h, f i h < bsup o f) → cof (bsup o f) ≤ o.card.lift :=
  (induction_on o) fun α r _ f H => by
    skip
    rw [bsup_eq_sup' r rfl]
    refine' cof_sup_le_lift _ _
    rw [← bsup_eq_sup']
    exact fun a => H _ _

theorem cof_bsup_le {o : Ordinal} :
    ∀ f : ∀, ∀ a < o, ∀, Ordinal, (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card :=
  (induction_on o) fun α r _ f H => by
    simpa using cof_bsup_le_lift.{u, u} f H

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
      refine' l (lt_succ.2 _)
      rw [←
        show g (f.symm ⟨b, h⟩) = b by
          dsimp [g] <;> simp ]
      apply le_sup)

theorem sup_lt_ord {ι} (f : ι → Ordinal) {c : Ordinal} (H1 : # ι < c.cof) (H2 : ∀ i, f i < c) : sup.{u, u} f < c := by
  apply lt_of_le_of_neₓ
  · rw [sup_le]
    exact fun i => le_of_ltₓ (H2 i)
    
  rintro h
  apply not_le_of_lt H1
  simpa [sup_ord, H2, h] using cof_sup_le.{u} f

theorem sup_lt {ι} (f : ι → Cardinal) {c : Cardinal} (H1 : # ι < c.ord.cof) (H2 : ∀ i, f i < c) :
    Cardinal.sup.{u, u} f < c := by
  rw [← ord_lt_ord, ← sup_ord]
  apply sup_lt_ord _ H1
  intro i
  rw [ord_lt_ord]
  apply H2

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : IsWellOrder α r] {s : Set (Set α)}
    (h₁ : Unbounded r <| ⋃₀s) (h₂ : # s < StrictOrder.cof r) : ∃ x ∈ s, Unbounded r x := by
  by_contra h
  simp only [not_exists, exists_prop, not_and, not_unbounded_iff] at h
  apply not_le_of_lt h₂
  let f : s → α := fun x : s => wo.wf.sup x (h x.1 x.2)
  let t : Set α := range f
  have : # t ≤ # s := mk_range_le
  refine' le_transₓ _ this
  have : unbounded r t := by
    intro x
    rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩
    refine' ⟨f ⟨c, hc⟩, mem_range_self _, _⟩
    intro hxz
    apply hxy
    refine' trans (wo.wf.lt_sup _ hy) hxz
  exact Cardinal.min_le _ (Subtype.mk t this)

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_Union {α β : Type u} (r : α → α → Prop) [wo : IsWellOrder α r] (s : β → Set α)
    (h₁ : Unbounded r <| ⋃ x, s x) (h₂ : # β < StrictOrder.cof r) : ∃ x : β, Unbounded r (s x) := by
  rw [← sUnion_range] at h₁
  have : # (range fun i : β => s i) < StrictOrder.cof r := lt_of_le_of_ltₓ mk_range_le h₂
  rcases unbounded_of_unbounded_sUnion r h₁ this with ⟨_, ⟨x, rfl⟩, u⟩
  exact ⟨x, u⟩

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ω ≤ # β) (h₂ : # α < (# β).ord.cof) :
    ∃ a : α, # (f ⁻¹' {a}) = # β := by
  have : ¬∀ a, # (f ⁻¹' {a}) < # β := by
    intro h
    apply not_lt_of_geₓ (ge_of_eq <| mk_univ)
    rw [← @preimage_univ _ _ f, ← Union_of_singleton, preimage_Union]
    apply lt_of_le_of_ltₓ mk_Union_le_sum_mk
    apply lt_of_le_of_ltₓ (sum_le_sup _)
    apply mul_lt_of_lt h₁ (lt_of_lt_of_leₓ h₂ <| cof_ord_le _)
    exact sup_lt _ h₂ h
  rw [not_forall] at this
  cases' this with x h
  use x
  apply le_antisymmₓ _ (le_of_not_gtₓ h)
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩

/-- pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ # β) (h₁ : ω ≤ θ)
    (h₂ : # α < θ.ord.cof) : ∃ a : α, θ ≤ # (f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  cases' infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂ with a ha
  use a
  rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  apply mk_preimage_of_injective _ _ Subtype.val_injective

theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal) (hθ : θ ≤ # s) (h₁ : ω ≤ θ)
    (h₂ : # α < θ.ord.cof) : ∃ (a : α)(t : Set β)(h : t ⊆ s), θ ≤ # t ∧ ∀ ⦃x⦄ hx : x ∈ t, f ⟨x, h hx⟩ = a := by
  cases' infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha
  refine' ⟨a, { x | ∃ h : x ∈ s, f ⟨x, h⟩ = a }, _, _, _⟩
  · rintro x ⟨hx, hx'⟩
    exact hx
    
  · refine' le_transₓ ha _
    apply ge_of_eq
    apply Quotientₓ.sound
    constructor
    refine' Equivₓ.trans _ (Equivₓ.subtypeSubtypeEquivSubtypeExists _ _).symm
    simp only [set_coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_set_of_eq]
    
  rintro x ⟨hx, hx'⟩
  exact hx'

end Ordinal

namespace Cardinal

open Ordinal

-- mathport name: «expr ^ »
local infixr:0 "^" => @pow Cardinal.{u} Cardinal Cardinal.hasPow

/-- A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ω` is a limit cardinal by this definition. -/
def IsLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀, ∀ x < c, ∀, succ x < c

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ω` is a strong limit by this definition. -/
def IsStrongLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀, ∀ x < c, ∀, (2^x) < c

theorem IsStrongLimit.is_limit {c} (H : IsStrongLimit c) : IsLimit c :=
  ⟨H.1, fun x h => lt_of_le_of_ltₓ (succ_le.2 <| cantor _) (H.2 _ h)⟩

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def IsRegular (c : Cardinal) : Prop :=
  ω ≤ c ∧ c.ord.cof = c

theorem IsRegular.pos {c : Cardinal} (H : c.IsRegular) : 0 < c :=
  omega_pos.trans_le H.left

theorem IsRegular.ord_pos {c : Cardinal} (H : c.IsRegular) : 0 < c.ord := by
  rw [Cardinal.lt_ord]
  exact H.pos

theorem cof_is_regular {o : Ordinal} (h : o.IsLimit) : IsRegular o.cof :=
  ⟨omega_le_cof.2 h, cof_cof _⟩

theorem omega_is_regular : IsRegular ω :=
  ⟨le_rfl, by
    simp ⟩

theorem succ_is_regular {c : Cardinal.{u}} (h : ω ≤ c) : IsRegular (succ c) :=
  ⟨le_transₓ h (le_of_ltₓ <| lt_succ_self _), by
    refine' le_antisymmₓ (cof_ord_le _) (succ_le.2 _)
    cases' Quotientₓ.exists_rep (succ c) with α αe
    simp at αe
    rcases ord_eq α with ⟨r, wo, re⟩
    skip
    have := ord_is_limit (le_transₓ h <| le_of_ltₓ <| lt_succ_self _)
    rw [← αe, re] at this⊢
    rcases cof_eq' r this with ⟨S, H, Se⟩
    rw [← Se]
    apply lt_imp_lt_of_le_imp_le fun h : # S ≤ c => mul_le_mul_right' h c
    rw [mul_eq_self h, ← succ_le, ← αe, ← sum_const']
    refine' le_transₓ _ (sum_le_sum (fun x : S => card (typein r x)) _ _)
    · simp only [← card_typein, ← mk_sigma]
      refine' ⟨embedding.of_surjective _ _⟩
      · exact fun x => x.2.1
        
      · exact fun a =>
          let ⟨b, h, ab⟩ := H a
          ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩
        
      
    · intro i
      rw [← lt_succ, ← lt_ord, ← αe, re]
      apply typein_lt_type
      ⟩

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (w : # α < # β) (w' : ω ≤ # α) :
    ∃ a : α, # α < # (f ⁻¹' {a}) := by
  simp_rw [← succ_le]
  exact
    Ordinal.infinite_pigeonhole_card f (# α).succ (succ_le.mpr w) (w'.trans (lt_succ_self _).le)
      ((lt_succ_self _).trans_le (succ_is_regular w').2.Ge)

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

theorem sup_lt_ord_of_is_regular {ι} (f : ι → Ordinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c.ord) :
    Ordinal.sup.{u, u} f < c.ord := by
  apply sup_lt_ord _ _ H2
  rw [hc.2]
  exact H1

theorem sup_lt_of_is_regular {ι} (f : ι → Cardinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c) :
    sup.{u, u} f < c := by
  apply sup_lt _ _ H2
  rwa [hc.2]

theorem sum_lt_of_is_regular {ι} (f : ι → Cardinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c) :
    sum.{u, u} f < c :=
  lt_of_le_of_ltₓ (sum_le_sup _) <| mul_lt_of_lt hc.1 H1 <| sup_lt_of_is_regular f hc H1 H2

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def IsInaccessible (c : Cardinal) :=
  ω < c ∧ IsRegular c ∧ IsStrongLimit c

theorem IsInaccessible.mk {c} (h₁ : ω < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀, ∀ x < c, ∀, (2^x) < c) : IsInaccessible c :=
  ⟨h₁, ⟨le_of_ltₓ h₁, le_antisymmₓ (cof_ord_le _) h₂⟩, ne_of_gtₓ (lt_transₓ omega_pos h₁), h₃⟩

-- Lean's foundations prove the existence of ω many inaccessible cardinals
theorem univ_inaccessible : IsInaccessible univ.{u, v} :=
  IsInaccessible.mk
    (by
      simpa using lift_lt_univ' ω)
    (by
      simp )
    fun c h => by
    rcases lt_univ'.1 h with ⟨c, rfl⟩
    rw [← lift_two_power.{u, max (u + 1) v}]
    apply lift_lt_univ'

theorem lt_power_cof {c : Cardinal.{u}} : ω ≤ c → c < (c^cof c.ord) :=
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
      

theorem lt_cof_power {a b : Cardinal} (ha : ω ≤ a) (b1 : 1 < b) : a < cof (b^a).ord := by
  have b0 : b ≠ 0 := ne_of_gtₓ (lt_transₓ zero_lt_one b1)
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a b0)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof (le_transₓ ha <| le_of_ltₓ <| cantor' _ b1)

end Cardinal

