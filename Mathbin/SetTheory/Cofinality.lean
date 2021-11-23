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


noncomputable theory

open Function Cardinal Set

open_locale Classical Cardinal

universe u v w

variable{α : Type _}{r : α → α → Prop}

namespace Order

/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) [IsRefl α r] : Cardinal :=
  @Cardinal.min { S : Set α // ∀ a, ∃ (b : _)(_ : b ∈ S), r a b } ⟨⟨Set.Univ, fun a => ⟨a, ⟨⟩, refl _⟩⟩⟩ fun S => # S

theorem cof_le (r : α → α → Prop) [IsRefl α r] {S : Set α} (h : ∀ a, ∃ (b : _)(_ : b ∈ S), r a b) : Order.cof r ≤ # S :=
  le_transₓ (Cardinal.min_le _ ⟨S, h⟩) (le_reflₓ _)

theorem le_cof {r : α → α → Prop} [IsRefl α r] (c : Cardinal) :
  c ≤ Order.cof r ↔ ∀ {S : Set α} h : ∀ a, ∃ (b : _)(_ : b ∈ S), r a b, c ≤ # S :=
  by 
    rw [Order.cof, Cardinal.le_min]
    exact ⟨fun H S h => H ⟨S, h⟩, fun H ⟨S, h⟩ => H h⟩

end Order

theorem RelIso.Cof.aux {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
  Cardinal.lift.{max u v} (Order.cof r) ≤ Cardinal.lift.{max u v} (Order.cof s) :=
  by 
    rw [Order.cof, Order.cof, lift_min, lift_min, Cardinal.le_min]
    intro S 
    cases' S with S H 
    simp only [comp, coe_sort_coe_base, Subtype.coe_mk]
    refine' le_transₓ (min_le _ _) _
    ·
      exact
        ⟨f ⁻¹' S,
          fun a =>
            let ⟨b, bS, h⟩ := H (f a)
            ⟨f.symm b,
              by 
                simp [bS, ←f.map_rel_iff, h, -coe_fn_coe_base, -coe_fn_coe_trans, PrincipalSeg.coe_coe_fn',
                  InitialSeg.coe_coe_fn]⟩⟩
    ·
      exact
        lift_mk_le.{u, v, max u v}.2
          ⟨⟨fun ⟨x, h⟩ => ⟨f x, h⟩,
              fun ⟨x, h₁⟩ ⟨y, h₂⟩ h₃ =>
                by 
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
  Quot.liftOn o
    (fun ⟨α, r, _⟩ =>
      by 
        exact StrictOrder.cof r)
    (by 
      rintro ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨⟨f, hf⟩⟩
      rw [←Cardinal.lift_inj]
      apply RelIso.cof ⟨f, _⟩
      simp [hf])

theorem cof_type (r : α → α → Prop) [IsWellOrder α r] : (type r).cof = StrictOrder.cof r :=
  rfl

theorem le_cof_type [IsWellOrder α r] {c} :
  c ≤ cof (type r) ↔ ∀ S : Set α, (∀ a, ∃ (b : _)(_ : b ∈ S), ¬r b a) → c ≤ # S :=
  by 
    dsimp [cof, StrictOrder.cof, Order.cof, type, Quotientₓ.mk, Quot.liftOn] <;>
      rw [Cardinal.le_min, Subtype.forall] <;> rfl

theorem cof_type_le [IsWellOrder α r] (S : Set α) (h : ∀ a, ∃ (b : _)(_ : b ∈ S), ¬r b a) : cof (type r) ≤ # S :=
  le_cof_type.1 (le_reflₓ _) S h

theorem lt_cof_type [IsWellOrder α r] (S : Set α) (hl : # S < cof (type r)) : ∃ a, ∀ b _ : b ∈ S, r b a :=
  not_forall_not.1$ fun h => not_le_of_lt hl$ cof_type_le S fun a => not_ball.1 (h a)

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cof_eq
(r : α → α → exprProp())
[is_well_order α r] : «expr∃ , »((S : set α), «expr ∧ »(∀
  a, «expr∃ , »((b «expr ∈ » S), «expr¬ »(r b a)), «expr = »(«expr#»() S, cof (type r)))) :=
begin
  have [] [":", expr «expr∃ , »((i), «expr = »(cof (type r), _))] [],
  { dsimp [] ["[", expr cof, ",", expr order.cof, ",", expr type, ",", expr quotient.mk, ",", expr quot.lift_on, "]"] [] [],
    apply [expr cardinal.min_eq] },
  exact [expr let ⟨⟨S, hl⟩, e⟩ := this in ⟨S, hl, e.symm⟩]
end

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ord_cof_eq
(r : α → α → exprProp())
[is_well_order α r] : «expr∃ , »((S : set α), «expr ∧ »(∀
  a, «expr∃ , »((b «expr ∈ » S), «expr¬ »(r b a)), «expr = »(type (subrel r S), (cof (type r)).ord))) :=
let ⟨S, hS, e⟩ := cof_eq r,
    ⟨s, _, e'⟩ := cardinal.ord_eq S,
    T : set α := {a | «expr∃ , »((aS : «expr ∈ »(a, S)), ∀ b : S, s b ⟨_, aS⟩ → r b a)} in
begin
  resetI,
  suffices [] [],
  { refine [expr ⟨T, this, le_antisymm _ «expr $ »(cardinal.ord_le.2, cof_type_le T this)⟩],
    rw ["[", "<-", expr e, ",", expr e', "]"] [],
    refine [expr type_le'.2 ⟨rel_embedding.of_monotone (λ a, ⟨a, let ⟨aS, _⟩ := a.2 in aS⟩) (λ a b h, _)⟩],
    rcases [expr a, "with", "⟨", ident a, ",", ident aS, ",", ident ha, "⟩"],
    rcases [expr b, "with", "⟨", ident b, ",", ident bS, ",", ident hb, "⟩"],
    change [expr s ⟨a, _⟩ ⟨b, _⟩] [] [],
    refine [expr ((trichotomous_of s _ _).resolve_left (λ hn, _)).resolve_left _],
    { exact [expr asymm h (ha _ hn)] },
    { intro [ident e],
      injection [expr e] ["with", ident e],
      subst [expr b],
      exact [expr irrefl _ h] } },
  { intro [ident a],
    have [] [":", expr {b : S | «expr¬ »(r b a)}.nonempty] [":=", expr let ⟨b, bS, ba⟩ := hS a in ⟨⟨b, bS⟩, ba⟩],
    let [ident b] [] [":=", expr is_well_order.wf.min _ this],
    have [ident ba] [":", expr «expr¬ »(r b a)] [":=", expr is_well_order.wf.min_mem _ this],
    refine [expr ⟨b, ⟨b.2, λ c, «expr $ »(not_imp_not.1, λ h, _)⟩, ba⟩],
    rw ["[", expr show ∀ b : S, «expr = »((⟨b, b.2⟩ : S), b), by intro [ident b]; cases [expr b] []; refl, "]"] [],
    exact [expr is_well_order.wf.not_lt_min _ this (is_order_connected.neg_trans h ba)] }
end

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_cof (o) : «expr = »((cof o).lift, cof o.lift) :=
«expr $ »(induction_on o, begin
   introsI [ident α, ident r, "_"],
   cases [expr lift_type r] ["with", "_", ident e],
   rw [expr e] [],
   apply [expr le_antisymm],
   { unfreezingI { refine [expr le_cof_type.2 (λ S H, _)] },
     have [] [":", expr «expr ≤ »((«expr#»() «expr ⁻¹' »(ulift.up, S)).lift, «expr#»() S)] [":=", expr ⟨⟨λ
        ⟨⟨x, h⟩⟩, ⟨⟨x⟩, h⟩, λ
        ⟨⟨x, h₁⟩⟩
        ⟨⟨y, h₂⟩⟩
        (e), by simp [] [] [] [] [] ["at", ident e]; congr; injection [expr e] []⟩⟩],
     refine [expr le_trans «expr $ »(cardinal.lift_le.2, cof_type_le _ _) this],
     exact [expr λ a, let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩ in ⟨b, bs, br⟩] },
   { rcases [expr cof_eq r, "with", "⟨", ident S, ",", ident H, ",", ident e', "⟩"],
     have [] [":", expr «expr ≤ »(«expr#»() «expr ⁻¹' »(ulift.down, S), («expr#»() S).lift)] [":=", expr ⟨⟨λ
        ⟨⟨x⟩, h⟩, ⟨⟨x, h⟩⟩, λ ⟨⟨x⟩, h₁⟩ ⟨⟨y⟩, h₂⟩ (e), by simp [] [] [] [] [] ["at", ident e]; congr; injections []⟩⟩],
     rw [expr e'] ["at", ident this],
     unfreezingI { refine [expr le_trans (cof_type_le _ _) this] },
     exact [expr λ ⟨a⟩, let ⟨b, bs, br⟩ := H a in ⟨⟨b⟩, bs, br⟩] }
 end)

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cof_le_card (o) : «expr ≤ »(cof o, card o) :=
«expr $ »(induction_on o, λ α r _, begin
   resetI,
   have [] [":", expr «expr = »(«expr#»() (@set.univ α), card (type r))] [":=", expr quotient.sound ⟨equiv.set.univ _⟩],
   rw ["<-", expr this] [],
   exact [expr cof_type_le set.univ (λ a, ⟨a, ⟨⟩, irrefl a⟩)]
 end)

theorem cof_ord_le (c : Cardinal) : cof c.ord ≤ c :=
  by 
    simpa using cof_le_card c.ord

@[simp]
theorem cof_zero : cof 0 = 0 :=
  le_antisymmₓ
    (by 
      simpa using cof_le_card 0)
    (Cardinal.zero_le _)

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
  ⟨induction_on o$
      fun α r _ z =>
        by 
          exact
            let ⟨S, hl, e⟩ := cof_eq r 
            type_eq_zero_iff_is_empty.2$
              ⟨fun a =>
                  let ⟨b, h, _⟩ := hl a
                  (mk_eq_zero_iff.1 (e.trans z)).elim' ⟨_, h⟩⟩,
    fun e =>
      by 
        simp [e]⟩

@[simp]
theorem cof_succ o : cof (succ o) = 1 :=
  by 
    apply le_antisymmₓ
    ·
      refine' induction_on o fun α r _ => _ 
      change cof (type _) ≤ _ 
      rw [←(_ : # _ = 1)]
      apply cof_type_le
      ·
        refine' fun a => ⟨Sum.inr PUnit.unit, Set.mem_singleton _, _⟩
        rcases a with (a | ⟨⟨⟨⟩⟩⟩) <;> simp [EmptyRelation]
      ·
        rw [Cardinal.mk_fintype, Set.card_singleton]
        simp 
    ·
      rw [←Cardinal.succ_zero, Cardinal.succ_le]
      simpa [lt_iff_le_and_ne, Cardinal.zero_le] using fun h => succ_ne_zero o (cof_eq_zero.1 (Eq.symm h))

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem cof_eq_one_iff_is_succ {o} : «expr ↔ »(«expr = »(cof.{u} o, 1), «expr∃ , »((a), «expr = »(o, succ a))) :=
⟨«expr $ »(induction_on o, λ α r _ z, begin
    resetI,
    rcases [expr cof_eq r, "with", "⟨", ident S, ",", ident hl, ",", ident e, "⟩"],
    rw [expr z] ["at", ident e],
    cases [expr mk_ne_zero_iff.1 (by rw [expr e] []; exact [expr one_ne_zero])] ["with", ident a],
    refine [expr ⟨typein r a, «expr $ »(eq.symm, quotient.sound ⟨rel_iso.of_surjective (rel_embedding.of_monotone _ (λ
          x y, _)) (λ x, _)⟩)⟩],
    { apply [expr sum.rec]; [exact [expr subtype.val], exact [expr λ _, a]] },
    { rcases [expr x, "with", ident x, "|", "⟨", "⟨", "⟨", "⟩", "⟩", "⟩"]; rcases [expr y, "with", ident y, "|", "⟨", "⟨", "⟨", "⟩", "⟩", "⟩"]; simp [] [] [] ["[", expr subrel, ",", expr order.preimage, ",", expr empty_relation, "]"] [] [],
      exact [expr x.2] },
    { suffices [] [":", expr «expr ∨ »(r x a, «expr∃ , »((b : punit), «expr = »(«expr↑ »(a), x)))],
      { simpa [] [] [] [] [] [] },
      rcases [expr trichotomous_of r x a, "with", ident h, "|", ident h, "|", ident h],
      { exact [expr or.inl h] },
      { exact [expr or.inr ⟨punit.star, h.symm⟩] },
      { rcases [expr hl x, "with", "⟨", ident a', ",", ident aS, ",", ident hn, "⟩"],
        rw [expr (_ : «expr = »(«expr↑ »(a), a'))] ["at", ident h],
        { exact [expr absurd h hn] },
        refine [expr congr_arg subtype.val (_ : «expr = »(a, ⟨a', aS⟩))],
        haveI [] [] [":=", expr le_one_iff_subsingleton.1 (le_of_eq e)],
        apply [expr subsingleton.elim] } }
  end), λ ⟨a, e⟩, by simp [] [] [] ["[", expr e, "]"] [] []⟩

@[simp]
theorem cof_add (a b : Ordinal) : b ≠ 0 → cof (a+b) = cof b :=
  induction_on a$
    fun α r _ =>
      induction_on b$
        fun β s _ b0 =>
          by 
            skip 
            change cof (type _) = _ 
            refine' eq_of_forall_le_iff fun c => _ 
            rw [le_cof_type, le_cof_type]
            split  <;> intro H S hS
            ·
              refine' le_transₓ (H { a | Sum.recOn a (∅ : Set α) S } fun a => _) ⟨⟨_, _⟩⟩
              ·
                cases' a with a b
                ·
                  cases' type_ne_zero_iff_nonempty.1 b0 with b 
                  rcases hS b with ⟨b', bs, _⟩
                  exact
                    ⟨Sum.inr b', bs,
                      by 
                        simp ⟩
                ·
                  rcases hS b with ⟨b', bs, h⟩
                  exact
                    ⟨Sum.inr b', bs,
                      by 
                        simp [h]⟩
              ·
                exact
                  fun a =>
                    match a with 
                    | ⟨Sum.inr b, h⟩ => ⟨b, h⟩
              ·
                exact
                  fun a b =>
                    match a, b with 
                    | ⟨Sum.inr a, h₁⟩, ⟨Sum.inr b, h₂⟩, h =>
                      by 
                        congr <;> injection h
            ·
              refine' le_transₓ (H (Sum.inr ⁻¹' S) fun a => _) ⟨⟨_, _⟩⟩
              ·
                rcases hS (Sum.inr a) with ⟨a' | b', bs, h⟩ <;> simp  at h
                ·
                  cases h
                ·
                  exact ⟨b', bs, h⟩
              ·
                exact fun ⟨a, h⟩ => ⟨_, h⟩
              ·
                exact
                  fun ⟨a, h₁⟩ ⟨b, h₂⟩ h =>
                    by 
                      injection h with h <;> congr <;> injection h

@[simp]
theorem cof_cof (o : Ordinal) : cof (cof o).ord = cof o :=
  le_antisymmₓ
      (le_transₓ (cof_le_card _)
        (by 
          simp ))$
    induction_on o$
      fun α r _ =>
        by 
          exact
            let ⟨S, hS, e₁⟩ := ord_cof_eq r 
            let ⟨T, hT, e₂⟩ := cof_eq (Subrel r S)
            by 
              rw [e₁] at e₂ 
              rw [←e₂]
              refine' le_transₓ (cof_type_le { a | ∃ h, (Subtype.mk a h : S) ∈ T } fun a => _) ⟨⟨_, _⟩⟩
              ·
                rcases hS a with ⟨b, bS, br⟩
                rcases hT ⟨b, bS⟩ with ⟨⟨c, cS⟩, cT, cs⟩
                exact ⟨c, ⟨cS, cT⟩, IsOrderConnected.neg_trans cs br⟩
              ·
                exact fun ⟨a, h⟩ => ⟨⟨a, h.fst⟩, h.snd⟩
              ·
                exact
                  fun ⟨a, ha⟩ ⟨b, hb⟩ h =>
                    by 
                      injection h with h <;> congr <;> injection h

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem omega_le_cof {o} : «expr ↔ »(«expr ≤ »(exprω(), cof o), is_limit o) :=
begin
  rcases [expr zero_or_succ_or_limit o, "with", ident rfl, "|", "⟨", ident o, ",", ident rfl, "⟩", "|", ident l],
  { simp [] [] [] ["[", expr not_zero_is_limit, ",", expr cardinal.omega_ne_zero, "]"] [] [] },
  { simp [] [] [] ["[", expr not_succ_is_limit, ",", expr cardinal.one_lt_omega, "]"] [] [] },
  { simp [] [] [] ["[", expr l, "]"] [] [],
    refine [expr le_of_not_lt (λ h, _)],
    cases [expr cardinal.lt_omega.1 h] ["with", ident n, ident e],
    have [] [] [":=", expr cof_cof o],
    rw ["[", expr e, ",", expr ord_nat, "]"] ["at", ident this],
    cases [expr n] [],
    { simp [] [] [] [] [] ["at", ident e],
      simpa [] [] [] ["[", expr e, ",", expr not_zero_is_limit, "]"] [] ["using", expr l] },
    { rw ["[", "<-", expr nat_cast_succ, ",", expr cof_succ, "]"] ["at", ident this],
      rw ["[", "<-", expr this, ",", expr cof_eq_one_iff_is_succ, "]"] ["at", ident e],
      rcases [expr e, "with", "⟨", ident a, ",", ident rfl, "⟩"],
      exact [expr not_succ_is_limit _ l] } }
end

@[simp]
theorem cof_omega : cof omega = ω :=
  le_antisymmₓ
    (by 
      rw [←card_omega] <;> apply cof_le_card)
    (omega_le_cof.2 omega_is_limit)

theorem cof_eq' (r : α → α → Prop) [IsWellOrder α r] (h : is_limit (type r)) :
  ∃ S : Set α, (∀ a, ∃ (b : _)(_ : b ∈ S), r a b) ∧ # S = cof (type r) :=
  let ⟨S, H, e⟩ := cof_eq r
  ⟨S,
    fun a =>
      let a' := enum r _ (h.2 _ (typein_lt_type r a))
      let ⟨b, h, ab⟩ := H a'
      ⟨b, h,
        (IsOrderConnected.conn a b a'$
              (typein_lt_typein r).1
                (by 
                  rw [typein_enum] <;> apply Ordinal.lt_succ_self)).resolve_right
          ab⟩,
    e⟩

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cof_sup_le_lift
{ι}
(f : ι → ordinal)
(H : ∀ i, «expr < »(f i, sup f)) : «expr ≤ »(cof (sup f), («expr#»() ι).lift) :=
begin
  generalize [ident e] [":"] [expr «expr = »(sup f, o)],
  refine [expr ordinal.induction_on o _ e],
  introsI [ident α, ident r, "_", ident e'],
  rw [expr e'] ["at", ident H],
  refine [expr le_trans (cof_type_le (set.range (λ i, enum r _ (H i))) _) ⟨embedding.of_surjective _ _⟩],
  { intro [ident a],
    by_contra [ident h],
    apply [expr not_le_of_lt (typein_lt_type r a)],
    rw ["[", "<-", expr e', ",", expr sup_le, "]"] [],
    intro [ident i],
    have [ident h] [":", expr ∀ x : ι, r (enum r (f x) _) a] [],
    { simpa [] [] [] [] [] ["using", expr h] },
    simpa [] [] ["only"] ["[", expr typein_enum, "]"] [] ["using", expr le_of_lt ((typein_lt_typein r).2 (h i))] },
  { exact [expr λ i, ⟨_, set.mem_range_self i.1⟩] },
  { intro [ident a],
    rcases [expr a, "with", "⟨", "_", ",", ident i, ",", ident rfl, "⟩"],
    exact [expr ⟨⟨i⟩, by simp [] [] [] [] [] []⟩] }
end

theorem cof_sup_le {ι} (f : ι → Ordinal) (H : ∀ i, f i < sup.{u, u} f) : cof (sup.{u, u} f) ≤ # ι :=
  by 
    simpa using cof_sup_le_lift.{u, u} f H

theorem cof_bsup_le_lift {o : Ordinal} :
  ∀ f : ∀ a _ : a < o, Ordinal, (∀ i h, f i h < bsup o f) → cof (bsup o f) ≤ o.card.lift :=
  induction_on o$
    fun α r _ f H =>
      by 
        rw [bsup_type] <;> refine' cof_sup_le_lift _ _ <;> rw [←bsup_type] <;> intro a <;> apply H

theorem cof_bsup_le {o : Ordinal} :
  ∀ f : ∀ a _ : a < o, Ordinal, (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card :=
  induction_on o$
    fun α r _ f H =>
      by 
        simpa using cof_bsup_le_lift.{u, u} f H

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem cof_univ : «expr = »(cof univ.{u, v}, cardinal.univ) :=
le_antisymm (cof_le_card _) (begin
   refine [expr le_of_forall_lt (λ c h, _)],
   rcases [expr lt_univ'.1 h, "with", "⟨", ident c, ",", ident rfl, "⟩"],
   rcases [expr @cof_eq ordinal.{u} ((«expr < »)) _, "with", "⟨", ident S, ",", ident H, ",", ident Se, "⟩"],
   rw ["[", expr univ, ",", "<-", expr lift_cof, ",", "<-", expr cardinal.lift_lift, ",", expr cardinal.lift_lt, ",", "<-", expr Se, "]"] [],
   refine [expr lt_of_not_ge (λ h, _)],
   cases [expr cardinal.lift_down h] ["with", ident a, ident e],
   refine [expr quotient.induction_on a (λ α e, _) e],
   cases [expr quotient.exact e] ["with", ident f],
   have [ident f] [] [":=", expr equiv.ulift.symm.trans f],
   let [ident g] [] [":=", expr λ a, (f a).1],
   let [ident o] [] [":=", expr succ (sup.{u, u} g)],
   rcases [expr H o, "with", "⟨", ident b, ",", ident h, ",", ident l, "⟩"],
   refine [expr l (lt_succ.2 _)],
   rw ["<-", expr show «expr = »(g (f.symm ⟨b, h⟩), b), by dsimp [] ["[", expr g, "]"] [] []; simp [] [] [] [] [] []] [],
   apply [expr le_sup]
 end)

theorem sup_lt_ord {ι} (f : ι → Ordinal) {c : Ordinal} (H1 : # ι < c.cof) (H2 : ∀ i, f i < c) : sup.{u, u} f < c :=
  by 
    apply lt_of_le_of_neₓ
    ·
      rw [sup_le]
      exact fun i => le_of_ltₓ (H2 i)
    rintro h 
    apply not_le_of_lt H1 
    simpa [sup_ord, H2, h] using cof_sup_le.{u} f

theorem sup_lt {ι} (f : ι → Cardinal) {c : Cardinal} (H1 : # ι < c.ord.cof) (H2 : ∀ i, f i < c) :
  Cardinal.sup.{u, u} f < c :=
  by 
    rw [←ord_lt_ord, ←sup_ord]
    apply sup_lt_ord _ H1 
    intro i 
    rw [ord_lt_ord]
    apply H2

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion
(r : α → α → exprProp())
[wo : is_well_order α r]
{s : set (set α)}
(h₁ : «expr $ »(unbounded r, «expr⋃₀ »(s)))
(h₂ : «expr < »(«expr#»() s, strict_order.cof r)) : «expr∃ , »((x «expr ∈ » s), unbounded r x) :=
begin
  by_contra [ident h],
  simp [] [] ["only"] ["[", expr not_exists, ",", expr exists_prop, ",", expr not_and, ",", expr not_unbounded_iff, "]"] [] ["at", ident h],
  apply [expr not_le_of_lt h₂],
  let [ident f] [":", expr s → α] [":=", expr λ x : s, wo.wf.sup x (h x.1 x.2)],
  let [ident t] [":", expr set α] [":=", expr range f],
  have [] [":", expr «expr ≤ »(«expr#»() t, «expr#»() s)] [],
  exact [expr mk_range_le],
  refine [expr le_trans _ this],
  have [] [":", expr unbounded r t] [],
  { intro [ident x],
    rcases [expr h₁ x, "with", "⟨", ident y, ",", "⟨", ident c, ",", ident hc, ",", ident hy, "⟩", ",", ident hxy, "⟩"],
    refine [expr ⟨f ⟨c, hc⟩, mem_range_self _, _⟩],
    intro [ident hxz],
    apply [expr hxy],
    refine [expr trans (wo.wf.lt_sup _ hy) hxz] },
  exact [expr cardinal.min_le _ (subtype.mk t this)]
end

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_Union
{α β : Type u}
(r : α → α → exprProp())
[wo : is_well_order α r]
(s : β → set α)
(h₁ : «expr $ »(unbounded r, «expr⋃ , »((x), s x)))
(h₂ : «expr < »(«expr#»() β, strict_order.cof r)) : «expr∃ , »((x : β), unbounded r (s x)) :=
begin
  rw ["[", "<-", expr sUnion_range, "]"] ["at", ident h₁],
  have [] [":", expr «expr < »(«expr#»() (range (λ
      i : β, s i)), strict_order.cof r)] [":=", expr lt_of_le_of_lt mk_range_le h₂],
  rcases [expr unbounded_of_unbounded_sUnion r h₁ this, "with", "⟨", "_", ",", "⟨", ident x, ",", ident rfl, "⟩", ",", ident u, "⟩"],
  exact [expr ⟨x, u⟩]
end

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole
{β α : Type u}
(f : β → α)
(h₁ : «expr ≤ »(exprω(), «expr#»() β))
(h₂ : «expr < »(«expr#»() α, («expr#»() β).ord.cof)) : «expr∃ , »((a : α), «expr = »(«expr#»() «expr ⁻¹' »(f, {a}), «expr#»() β)) :=
begin
  have [] [":", expr «expr¬ »(∀ a, «expr < »(«expr#»() «expr ⁻¹' »(f, {a}), «expr#»() β))] [],
  { intro [ident h],
    apply [expr not_lt_of_ge «expr $ »(ge_of_eq, mk_univ)],
    rw ["[", "<-", expr @preimage_univ _ _ f, ",", "<-", expr Union_of_singleton, ",", expr preimage_Union, "]"] [],
    apply [expr lt_of_le_of_lt mk_Union_le_sum_mk],
    apply [expr lt_of_le_of_lt (sum_le_sup _)],
    apply [expr mul_lt_of_lt h₁ «expr $ »(lt_of_lt_of_le h₂, cof_ord_le _)],
    exact [expr sup_lt _ h₂ h] },
  rw ["[", expr not_forall, "]"] ["at", ident this],
  cases [expr this] ["with", ident x, ident h],
  use [expr x],
  apply [expr le_antisymm _ (le_of_not_gt h)],
  rw ["[", expr le_mk_iff_exists_set, "]"] [],
  exact [expr ⟨_, rfl⟩]
end

/-- pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ # β) (h₁ : ω ≤ θ)
  (h₂ : # α < θ.ord.cof) : ∃ a : α, θ ≤ # (f ⁻¹' {a}) :=
  by 
    rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
    cases' infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂ with a ha 
    use a 
    rw [←ha, @preimage_comp _ _ _ Subtype.val f]
    apply mk_preimage_of_injective _ _ Subtype.val_injective

theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal) (hθ : θ ≤ # s) (h₁ : ω ≤ θ)
  (h₂ : # α < θ.ord.cof) : ∃ (a : α)(t : Set β)(h : t ⊆ s), θ ≤ # t ∧ ∀ ⦃x⦄ hx : x ∈ t, f ⟨x, h hx⟩ = a :=
  by 
    cases' infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha 
    refine' ⟨a, { x | ∃ h : x ∈ s, f ⟨x, h⟩ = a }, _, _, _⟩
    ·
      rintro x ⟨hx, hx'⟩
      exact hx
    ·
      refine' le_transₓ ha _ 
      apply ge_of_eq 
      apply Quotientₓ.sound 
      constructor 
      refine' Equiv.trans _ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm 
      simp only [set_coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_set_of_eq]
    rintro x ⟨hx, hx'⟩
    exact hx'

end Ordinal

namespace Cardinal

open Ordinal

local infixr:0 "^" => @pow Cardinal.{u} Cardinal Cardinal.hasPow

/-- A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ω` is a limit cardinal by this definition. -/
def is_limit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀ x _ : x < c, succ x < c

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ω` is a strong limit by this definition. -/
def is_strong_limit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀ x _ : x < c, (2^x) < c

theorem is_strong_limit.is_limit {c} (H : is_strong_limit c) : is_limit c :=
  ⟨H.1, fun x h => lt_of_le_of_ltₓ (succ_le.2$ cantor _) (H.2 _ h)⟩

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def IsRegular (c : Cardinal) : Prop :=
  ω ≤ c ∧ c.ord.cof = c

theorem is_regular.pos {c : Cardinal} (H : c.is_regular) : 0 < c :=
  omega_pos.trans_le H.left

theorem is_regular.ord_pos {c : Cardinal} (H : c.is_regular) : 0 < c.ord :=
  by 
    rw [Cardinal.lt_ord]
    exact H.pos

theorem cof_is_regular {o : Ordinal} (h : o.is_limit) : IsRegular o.cof :=
  ⟨omega_le_cof.2 h, cof_cof _⟩

theorem omega_is_regular : IsRegular ω :=
  ⟨le_reflₓ _,
    by 
      simp ⟩

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem succ_is_regular {c : cardinal.{u}} (h : «expr ≤ »(exprω(), c)) : is_regular (succ c) :=
⟨le_trans h «expr $ »(le_of_lt, lt_succ_self _), begin
   refine [expr le_antisymm (cof_ord_le _) (succ_le.2 _)],
   cases [expr quotient.exists_rep (succ c)] ["with", ident α, ident αe],
   simp [] [] [] [] [] ["at", ident αe],
   rcases [expr ord_eq α, "with", "⟨", ident r, ",", ident wo, ",", ident re, "⟩"],
   resetI,
   have [] [] [":=", expr ord_is_limit «expr $ »(le_trans h, «expr $ »(le_of_lt, lt_succ_self _))],
   rw ["[", "<-", expr αe, ",", expr re, "]"] ["at", ident this, "⊢"],
   rcases [expr cof_eq' r this, "with", "⟨", ident S, ",", ident H, ",", ident Se, "⟩"],
   rw ["[", "<-", expr Se, "]"] [],
   apply [expr lt_imp_lt_of_le_imp_le (λ h : «expr ≤ »(«expr#»() S, c), mul_le_mul_right' h c)],
   rw ["[", expr mul_eq_self h, ",", "<-", expr succ_le, ",", "<-", expr αe, ",", "<-", expr sum_const', "]"] [],
   refine [expr le_trans _ (sum_le_sum (λ x : S, card (typein r x)) _ _)],
   { simp [] [] ["only"] ["[", "<-", expr card_typein, ",", "<-", expr mk_sigma, "]"] [] [],
     refine [expr ⟨embedding.of_surjective _ _⟩],
     { exact [expr λ x, x.2.1] },
     { exact [expr λ a, let ⟨b, h, ab⟩ := H a in ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩] } },
   { intro [ident i],
     rw ["[", "<-", expr lt_succ, ",", "<-", expr lt_ord, ",", "<-", expr αe, ",", expr re, "]"] [],
     apply [expr typein_lt_type] }
 end⟩

/--
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (w : # α < # β) (w' : ω ≤ # α) :
  ∃ a : α, # α < # (f ⁻¹' {a}) :=
  by 
    simpRw [←succ_le]
    exact
      Ordinal.infinite_pigeonhole_card f (# α).succ (succ_le.mpr w) (w'.trans (lt_succ_self _).le)
        ((lt_succ_self _).trans_le (succ_is_regular w').2.Ge)

/--
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type _} (f : β → α) (w : # α < # β) (w' : _root_.infinite α) :
  ∃ a : α, _root_.infinite (f ⁻¹' {a}) :=
  by 
    simpRw [Cardinal.infinite_iff]  at w'⊢
    cases' infinite_pigeonhole_card_lt f w w' with a ha 
    exact ⟨a, w'.trans ha.le⟩

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
theorem le_range_of_union_finset_eq_top
{α β : Type*}
[infinite β]
(f : α → finset β)
(w : «expr = »(«expr⋃ , »((a), (f a : set β)), «expr⊤»())) : «expr ≤ »(«expr#»() β, «expr#»() (range f)) :=
begin
  have [ident k] [":", expr _root_.infinite (range f)] [],
  { rw [expr infinite_coe_iff] [],
    apply [expr mt (union_finset_finite_of_range_finite f)],
    rw [expr w] [],
    exact [expr infinite_univ] },
  by_contradiction [ident h],
  simp [] [] ["only"] ["[", expr not_le, "]"] [] ["at", ident h],
  let [ident u] [":", expr ∀
   b, «expr∃ , »((a), «expr ∈ »(b, f a))] [":=", expr λ
   b, by simpa [] [] [] [] [] ["using", expr (w.ge : _) (set.mem_univ b)]],
  let [ident u'] [":", expr β → range f] [":=", expr λ b, ⟨f (u b).some, by simp [] [] [] [] [] []⟩],
  have [ident v'] [":", expr ∀ a, «expr ≤ »(«expr ⁻¹' »(u', {⟨f a, by simp [] [] [] [] [] []⟩}), f a)] [],
  begin
    rintros [ident a, ident p, ident m],
    simp [] [] [] [] [] ["at", ident m],
    rw ["<-", expr m] [],
    apply [expr λ b, (u b).some_spec]
  end,
  obtain ["⟨", "⟨", "-", ",", "⟨", ident a, ",", ident rfl, "⟩", "⟩", ",", ident p, "⟩", ":=", expr exists_infinite_fiber u' h k],
  exact [expr (@infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false]
end

theorem sup_lt_ord_of_is_regular {ι} (f : ι → Ordinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c.ord) :
  Ordinal.sup.{u, u} f < c.ord :=
  by 
    apply sup_lt_ord _ _ H2 
    rw [hc.2]
    exact H1

theorem sup_lt_of_is_regular {ι} (f : ι → Cardinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c) :
  sup.{u, u} f < c :=
  by 
    apply sup_lt _ _ H2 
    rwa [hc.2]

theorem sum_lt_of_is_regular {ι} (f : ι → Cardinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c) :
  Sum.{u, u} f < c :=
  lt_of_le_of_ltₓ (sum_le_sup _)$ mul_lt_of_lt hc.1 H1$ sup_lt_of_is_regular f hc H1 H2

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def is_inaccessible (c : Cardinal) :=
  ω < c ∧ IsRegular c ∧ is_strong_limit c

theorem is_inaccessible.mk {c} (h₁ : ω < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀ x _ : x < c, (2^x) < c) : is_inaccessible c :=
  ⟨h₁, ⟨le_of_ltₓ h₁, le_antisymmₓ (cof_ord_le _) h₂⟩, ne_of_gtₓ (lt_transₓ omega_pos h₁), h₃⟩

theorem univ_inaccessible : is_inaccessible univ.{u, v} :=
  is_inaccessible.mk
    (by 
      simpa using lift_lt_univ' ω)
    (by 
      simp )
    fun c h =>
      by 
        rcases lt_univ'.1 h with ⟨c, rfl⟩
        rw [←lift_two_power.{u, max (u + 1) v}]
        apply lift_lt_univ'

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_power_cof {c : cardinal.{u}} : «expr ≤ »(exprω(), c) → «expr < »(c, «expr ^ »(c, cof c.ord)) :=
«expr $ »(quotient.induction_on c, λ α h, begin
   rcases [expr ord_eq α, "with", "⟨", ident r, ",", ident wo, ",", ident re, "⟩"],
   resetI,
   have [] [] [":=", expr ord_is_limit h],
   rw ["[", expr mk_def, ",", expr re, "]"] ["at", ident this, "⊢"],
   rcases [expr cof_eq' r this, "with", "⟨", ident S, ",", ident H, ",", ident Se, "⟩"],
   have [] [] [":=", expr sum_lt_prod (λ a : S, «expr#»() {x // r x a}) (λ _, «expr#»() α) (λ i, _)],
   { simp [] [] ["only"] ["[", expr cardinal.prod_const, ",", expr cardinal.lift_id, ",", "<-", expr Se, ",", "<-", expr mk_sigma, ",", expr power_def, "]"] [] ["at", ident this, "⊢"],
     refine [expr lt_of_le_of_lt _ this],
     refine [expr ⟨embedding.of_surjective _ _⟩],
     { exact [expr λ x, x.2.1] },
     { exact [expr λ a, let ⟨b, h, ab⟩ := H a in ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩] } },
   { have [] [] [":=", expr typein_lt_type r i],
     rwa ["[", "<-", expr re, ",", expr lt_ord, "]"] ["at", ident this] }
 end)

-- error in SetTheory.Cofinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_cof_power
{a b : cardinal}
(ha : «expr ≤ »(exprω(), a))
(b1 : «expr < »(1, b)) : «expr < »(a, cof «expr ^ »(b, a).ord) :=
begin
  have [ident b0] [":", expr «expr ≠ »(b, 0)] [":=", expr ne_of_gt (lt_trans zero_lt_one b1)],
  apply [expr lt_imp_lt_of_le_imp_le «expr $ »(power_le_power_left, power_ne_zero a b0)],
  rw ["[", "<-", expr power_mul, ",", expr mul_eq_self ha, "]"] [],
  exact [expr lt_power_cof «expr $ »(le_trans ha, «expr $ »(le_of_lt, cantor' _ b1))]
end

end Cardinal

