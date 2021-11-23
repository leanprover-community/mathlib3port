import Mathbin.SetTheory.OrdinalArithmetic 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Logic.Small

/-!
# Cardinals and ordinals

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions

* The function `cardinal.aleph'` gives the cardinals listed by their ordinal
  index, and is the inverse of `cardinal.aleph_idx`.
  `aleph' n = n`, `aleph' ω = cardinal.omega = ℵ₀`, `aleph' (ω + 1) = ℵ₁`, etc.
  It is an order isomorphism between ordinals and cardinals.
* The function `cardinal.aleph` gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = cardinal.omega = ℵ₀`, `aleph 1 = ℵ₁` is the first
  uncountable cardinal, and so on.

## Main Statements

* `cardinal.mul_eq_max` and `cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `cardinal.mk_list_eq_mk` : when `α` is infinite, `α` and `list α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making `simp`
  able to prove inequalities about numeral cardinals.

## Tags

cardinal arithmetic (for infinite cardinals)
-/


noncomputable theory

open Function Cardinal Set Equiv

open_locale Classical Cardinal

universe u v w

namespace Cardinal

section UsingOrdinals

open Ordinal

theorem ord_is_limit {c} (co : ω ≤ c) : (ord c).IsLimit :=
  by 
    refine' ⟨fun h => omega_ne_zero _, fun a => lt_imp_lt_of_le_imp_le _⟩
    ·
      rw [←Ordinal.le_zero, ord_le] at h 
      simpa only [card_zero, nonpos_iff_eq_zero] using le_transₓ co h
    ·
      intro h 
      rw [ord_le] at h⊢
      rwa [←@add_one_of_omega_le (card a), ←card_succ]
      rw [←ord_le, ←le_succ_of_is_limit, ord_le]
      ·
        exact le_transₓ co h
      ·
        rw [ord_omega]
        exact omega_is_limit

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `aleph_idx`.
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def aleph_idx.initial_seg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def aleph_idx : Cardinal → Ordinal :=
  aleph_idx.initial_seg

@[simp]
theorem aleph_idx.initial_seg_coe : (aleph_idx.initial_seg : Cardinal → Ordinal) = aleph_idx :=
  rfl

@[simp]
theorem aleph_idx_lt {a b} : aleph_idx a < aleph_idx b ↔ a < b :=
  aleph_idx.initial_seg.toRelEmbedding.map_rel_iff

@[simp]
theorem aleph_idx_le {a b} : aleph_idx a ≤ aleph_idx b ↔ a ≤ b :=
  by 
    rw [←not_ltₓ, ←not_ltₓ, aleph_idx_lt]

theorem aleph_idx.init {a b} : b < aleph_idx a → ∃ c, aleph_idx c = b :=
  aleph_idx.initial_seg.init _ _

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `aleph_idx`. -/
def aleph_idx.rel_iso : @rel_iso cardinal.{u} ordinal.{u} ((«expr < »)) ((«expr < »)) :=
«expr $ »(@rel_iso.of_surjective cardinal.{u} ordinal.{u} ((«expr < »)) ((«expr < »)) aleph_idx.initial_seg.{u}, «expr $ »((initial_seg.eq_or_principal aleph_idx.initial_seg.{u}).resolve_right, λ
  ⟨o, e⟩, begin
    have [] [":", expr ∀ c, «expr < »(aleph_idx c, o)] [":=", expr λ c, (e _).2 ⟨_, rfl⟩],
    refine [expr ordinal.induction_on o _ this],
    introsI [ident α, ident r, "_", ident h],
    let [ident s] [] [":=", expr sup.{u, u} (λ a : α, inv_fun aleph_idx (ordinal.typein r a))],
    apply [expr not_le_of_gt (lt_succ_self s)],
    have [ident I] [":", expr injective aleph_idx] [":=", expr aleph_idx.initial_seg.to_embedding.injective],
    simpa [] [] ["only"] ["[", expr typein_enum, ",", expr left_inverse_inv_fun I (succ s), "]"] [] ["using", expr le_sup.{u, u} (λ
      a, inv_fun aleph_idx (ordinal.typein r a)) (ordinal.enum r _ (h (succ s)))]
  end))

@[simp]
theorem aleph_idx.rel_iso_coe : (aleph_idx.rel_iso : Cardinal → Ordinal) = aleph_idx :=
  rfl

@[simp]
theorem type_cardinal : @Ordinal.type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} :=
  by 
    rw [Ordinal.univ_id] <;> exact Quotientₓ.sound ⟨aleph_idx.rel_iso⟩

@[simp]
theorem mk_cardinal : # Cardinal = univ.{u, u + 1} :=
  by 
    simpa only [card_type, card_univ] using congr_argₓ card type_cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
def aleph'.rel_iso :=
  Cardinal.alephIdx.relIso.symm

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc. -/
def aleph' : Ordinal → Cardinal :=
  aleph'.rel_iso

@[simp]
theorem aleph'.rel_iso_coe : (aleph'.rel_iso : Ordinal → Cardinal) = aleph' :=
  rfl

@[simp]
theorem aleph'_lt {o₁ o₂ : Ordinal.{u}} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  aleph'.rel_iso.map_rel_iff

@[simp]
theorem aleph'_le {o₁ o₂ : Ordinal.{u}} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph'_lt

@[simp]
theorem aleph'_aleph_idx (c : Cardinal.{u}) : aleph' c.aleph_idx = c :=
  Cardinal.alephIdx.relIso.toEquiv.symm_apply_apply c

@[simp]
theorem aleph_idx_aleph' (o : Ordinal.{u}) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o

@[simp]
theorem aleph'_zero : aleph' 0 = 0 :=
  by 
    rw [←nonpos_iff_eq_zero, ←aleph'_aleph_idx 0, aleph'_le] <;> apply Ordinal.zero_le

@[simp]
theorem aleph'_succ {o : Ordinal.{u}} : aleph' o.succ = (aleph' o).succ :=
  le_antisymmₓ
    (Cardinal.aleph_idx_le.1$
      by 
        rw [aleph_idx_aleph', Ordinal.succ_le, ←aleph'_lt, aleph'_aleph_idx] <;> apply Cardinal.lt_succ_self)
    (Cardinal.succ_le.2$ aleph'_lt.2$ Ordinal.lt_succ_self _)

@[simp]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
| 0 => aleph'_zero
| n+1 =>
  show aleph' (Ordinal.succ n) = n.succ by 
    rw [aleph'_succ, aleph'_nat, nat_succ]

theorem aleph'_le_of_limit {o : Ordinal.{u}} (l : o.is_limit) {c} : aleph' o ≤ c ↔ ∀ o' _ : o' < o, aleph' o' ≤ c :=
  ⟨fun h o' h' => le_transₓ (aleph'_le.2$ le_of_ltₓ h') h,
    fun h =>
      by 
        rw [←aleph'_aleph_idx c, aleph'_le, Ordinal.limit_le l]
        intro x h' 
        rw [←aleph'_le, aleph'_aleph_idx]
        exact h _ h'⟩

@[simp]
theorem aleph'_omega : aleph' Ordinal.omega = ω :=
  eq_of_forall_ge_iff$
    fun c =>
      by 
        simp only [aleph'_le_of_limit omega_is_limit, Ordinal.lt_omega, exists_imp_distrib, omega_le]
        exact
          forall_swap.trans
            (forall_congrₓ$
              fun n =>
                by 
                  simp only [forall_eq, aleph'_nat])

/-- `aleph'` and `aleph_idx` form an equivalence between `ordinal` and `cardinal` -/
@[simp]
def aleph'_equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', aleph_idx, aleph_idx_aleph', aleph'_aleph_idx⟩

/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ω`, `aleph 1 = succ ω` is the first
  uncountable cardinal, and so on. -/
def aleph (o : Ordinal) : Cardinal :=
  aleph' (Ordinal.omega+o)

@[simp]
theorem aleph_lt {o₁ o₂ : Ordinal.{u}} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
  aleph'_lt.trans (Ordinal.add_lt_add_iff_left _)

@[simp]
theorem aleph_le {o₁ o₂ : Ordinal.{u}} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph_lt

@[simp]
theorem aleph_succ {o : Ordinal.{u}} : aleph o.succ = (aleph o).succ :=
  by 
    rw [aleph, Ordinal.add_succ, aleph'_succ] <;> rfl

@[simp]
theorem aleph_zero : aleph 0 = ω :=
  by 
    simp only [aleph, add_zeroₓ, aleph'_omega]

theorem omega_le_aleph' {o : Ordinal} : ω ≤ aleph' o ↔ Ordinal.omega ≤ o :=
  by 
    rw [←aleph'_omega, aleph'_le]

theorem omega_le_aleph (o : Ordinal) : ω ≤ aleph o :=
  by 
    rw [aleph, omega_le_aleph'] <;> apply Ordinal.le_add_right

theorem ord_aleph_is_limit (o : Ordinal) : is_limit (aleph o).ord :=
  ord_is_limit$ omega_le_aleph _

theorem exists_aleph {c : Cardinal} : ω ≤ c ↔ ∃ o, c = aleph o :=
  ⟨fun h =>
      ⟨aleph_idx c - Ordinal.omega,
        by 
          rw [aleph, Ordinal.add_sub_cancel_of_le, aleph'_aleph_idx] <;> rwa [←omega_le_aleph', aleph'_aleph_idx]⟩,
    fun ⟨o, e⟩ => e.symm ▸ omega_le_aleph _⟩

theorem aleph'_is_normal : is_normal (ord ∘ aleph') :=
  ⟨fun o => ord_lt_ord.2$ aleph'_lt.2$ Ordinal.lt_succ_self _,
    fun o l a =>
      by 
        simp only [ord_le, aleph'_le_of_limit l]⟩

theorem aleph_is_normal : is_normal (ord ∘ aleph) :=
  aleph'_is_normal.trans$ add_is_normal Ordinal.omega

theorem succ_omega : succ ω = aleph 1 :=
  by 
    rw [←aleph_zero, ←aleph_succ, Ordinal.succ_zero]

theorem countable_iff_lt_aleph_one {α : Type _} (s : Set α) : countable s ↔ # s < aleph 1 :=
  by 
    rw [←succ_omega, lt_succ, mk_set_le_omega]

/-! ### Properties of `mul` -/


-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : cardinal} (h : «expr ≤ »(exprω(), c)) : «expr = »(«expr * »(c, c), c) :=
begin
  refine [expr le_antisymm _ (by simpa [] [] ["only"] ["[", expr mul_one, "]"] [] ["using", expr mul_le_mul_left' (one_lt_omega.le.trans h) c])],
  refine [expr acc.rec_on (cardinal.wf.apply c) (λ c _, «expr $ »(quotient.induction_on c, λ α IH ol, _)) h],
  rcases [expr ord_eq α, "with", "⟨", ident r, ",", ident wo, ",", ident e, "⟩"],
  resetI,
  letI [] [] [":=", expr linear_order_of_STO' r],
  haveI [] [":", expr is_well_order α ((«expr < »))] [":=", expr wo],
  let [ident g] [":", expr «expr × »(α, α) → α] [":=", expr λ p, max p.1 p.2],
  let [ident f] [":", expr «expr ↪ »(«expr × »(α, α), «expr × »(ordinal, «expr × »(α, α)))] [":=", expr ⟨λ
    p : «expr × »(α, α), (typein ((«expr < »)) (g p), p), λ p q, congr_arg prod.snd⟩],
  let [ident s] [] [":=", expr «expr ⁻¹'o »(f, prod.lex ((«expr < »)) (prod.lex ((«expr < »)) ((«expr < »))))],
  haveI [] [":", expr is_well_order _ s] [":=", expr (rel_embedding.preimage _ _).is_well_order],
  suffices [] [":", expr «expr ≤ »(type s, type r)],
  { exact [expr card_le_card this] },
  refine [expr le_of_forall_lt (λ o h, _)],
  rcases [expr typein_surj s h, "with", "⟨", ident p, ",", ident rfl, "⟩"],
  rw ["[", "<-", expr e, ",", expr lt_ord, "]"] [],
  refine [expr lt_of_le_of_lt (_ : «expr ≤ »(_, «expr * »(card (typein ((«expr < »)) (g p)).succ, card (typein ((«expr < »)) (g p)).succ))) _],
  { have [] [":", expr «expr ⊆ »({q | s q p}, (insert (g p) {x | «expr < »(x, g p)}).prod (insert (g p) {x | «expr < »(x, g p)}))] [],
    { intros [ident q, ident h],
      simp [] [] ["only"] ["[", expr s, ",", expr embedding.coe_fn_mk, ",", expr order.preimage, ",", expr typein_lt_typein, ",", expr prod.lex_def, ",", expr typein_inj, "]"] [] ["at", ident h],
      exact [expr max_le_iff.1 «expr $ »(le_iff_lt_or_eq.2, h.imp_right and.left)] },
    suffices [ident H] [":", expr «expr ≃ »((insert (g p) {x | r x (g p)} : set α), «expr ⊕ »({x | r x (g p)}, punit))],
    { exact [expr ⟨(set.embedding_of_subset _ _ this).trans ((equiv.set.prod _ _).trans (H.prod_congr H)).to_embedding⟩] },
    refine [expr (equiv.set.insert _).trans ((equiv.refl _).sum_congr punit_equiv_punit)],
    apply [expr @irrefl _ r] },
  cases [expr lt_or_le (card (typein ((«expr < »)) (g p)).succ) exprω()] ["with", ident qo, ident qo],
  { exact [expr lt_of_lt_of_le (mul_lt_omega qo qo) ol] },
  { suffices [] [],
    { exact [expr lt_of_le_of_lt (IH _ this qo) this] },
    rw ["<-", expr lt_ord] [],
    apply [expr (ord_is_limit ol).2],
    rw ["[", expr mk_def, ",", expr e, "]"] [],
    apply [expr typein_lt_type] }
end

end UsingOrdinals

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : Cardinal} (ha : ω ≤ a) (hb : ω ≤ b) : (a*b) = max a b :=
  le_antisymmₓ (mul_eq_self (le_transₓ ha (le_max_leftₓ a b)) ▸ mul_le_mul' (le_max_leftₓ _ _) (le_max_rightₓ _ _))$
    max_leₓ
      (by 
        simpa only [mul_oneₓ] using mul_le_mul_left' (one_lt_omega.le.trans hb) a)
      (by 
        simpa only [one_mulₓ] using mul_le_mul_right' (one_lt_omega.le.trans ha) b)

@[simp]
theorem omega_mul_eq {a : Cardinal} (ha : ω ≤ a) : (ω*a) = a :=
  (mul_eq_max le_rfl ha).trans (max_eq_rightₓ ha)

@[simp]
theorem mul_omega_eq {a : Cardinal} (ha : ω ≤ a) : (a*ω) = a :=
  (mul_eq_max ha le_rfl).trans (max_eq_leftₓ ha)

theorem mul_lt_of_lt {a b c : Cardinal} (hc : ω ≤ c) (h1 : a < c) (h2 : b < c) : (a*b) < c :=
  lt_of_le_of_ltₓ (mul_le_mul' (le_max_leftₓ a b) (le_max_rightₓ a b))$
    (lt_or_leₓ (max a b) ω).elim (fun h => lt_of_lt_of_leₓ (mul_lt_omega h h) hc)
      fun h =>
        by 
          rw [mul_eq_self h] <;> exact max_ltₓ h1 h2

theorem mul_le_max_of_omega_le_left {a b : Cardinal} (h : ω ≤ a) : (a*b) ≤ max a b :=
  by 
    convert mul_le_mul' (le_max_leftₓ a b) (le_max_rightₓ a b)
    rw [mul_eq_self]
    refine' le_transₓ h (le_max_leftₓ a b)

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_eq_max_of_omega_le_left
{a b : cardinal}
(h : «expr ≤ »(exprω(), a))
(h' : «expr ≠ »(b, 0)) : «expr = »(«expr * »(a, b), max a b) :=
begin
  cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { exact [expr mul_eq_max h hb] },
  refine [expr (mul_le_max_of_omega_le_left h).antisymm _],
  have [] [":", expr «expr ≤ »(b, a)] [],
  from [expr hb.le.trans h],
  rw ["[", expr max_eq_left this, "]"] [],
  convert [] [expr mul_le_mul_left' (one_le_iff_ne_zero.mpr h') _] [],
  rw ["[", expr mul_one, "]"] []
end

theorem mul_le_max (a b : Cardinal) : (a*b) ≤ max (max a b) ω :=
  by 
    byCases' ha0 : a = 0
    ·
      simp [ha0]
    byCases' hb0 : b = 0
    ·
      simp [hb0]
    byCases' ha : ω ≤ a
    ·
      rw [mul_eq_max_of_omega_le_left ha hb0]
      exact le_max_leftₓ _ _
    ·
      byCases' hb : ω ≤ b
      ·
        rw [mul_commₓ, mul_eq_max_of_omega_le_left hb ha0, max_commₓ]
        exact le_max_leftₓ _ _
      ·
        exact le_max_of_le_right (le_of_ltₓ (mul_lt_omega (lt_of_not_geₓ ha) (lt_of_not_geₓ hb)))

theorem mul_eq_left {a b : Cardinal} (ha : ω ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : (a*b) = a :=
  by 
    rw [mul_eq_max_of_omega_le_left ha hb', max_eq_leftₓ hb]

theorem mul_eq_right {a b : Cardinal} (hb : ω ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : (a*b) = b :=
  by 
    rw [mul_commₓ, mul_eq_left hb ha ha']

theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b*a :=
  by 
    convert mul_le_mul_right' (one_le_iff_ne_zero.mpr h) _ 
    rw [one_mulₓ]

theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a*b :=
  by 
    rw [mul_commₓ]
    exact le_mul_left h

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_eq_left_iff
{a
 b : cardinal} : «expr ↔ »(«expr = »(«expr * »(a, b), a), «expr ∨ »(«expr ∧ »(«expr ≤ »(max exprω() b, a), «expr ≠ »(b, 0)), «expr ∨ »(«expr = »(b, 1), «expr = »(a, 0)))) :=
begin
  rw ["[", expr max_le_iff, "]"] [],
  split,
  { intro [ident h],
    cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha],
    { have [] [":", expr «expr ≠ »(a, 0)] [],
      { rintro [ident rfl],
        exact [expr not_lt_of_le ha omega_pos] },
      left,
      use [expr ha],
      { rw ["[", "<-", expr not_lt, "]"] [],
        intro [ident hb],
        apply [expr ne_of_gt _ h],
        refine [expr lt_of_lt_of_le hb (le_mul_left this)] },
      { rintro [ident rfl],
        apply [expr this],
        rw ["[", expr _root_.mul_zero, "]"] ["at", ident h],
        subst [expr h] } },
    right,
    by_cases [expr h2a, ":", expr «expr = »(a, 0)],
    { right,
      exact [expr h2a] },
    have [ident hb] [":", expr «expr ≠ »(b, 0)] [],
    { rintro [ident rfl],
      apply [expr h2a],
      rw ["[", expr mul_zero, "]"] ["at", ident h],
      subst [expr h] },
    left,
    rw ["[", "<-", expr h, ",", expr mul_lt_omega_iff, ",", expr lt_omega, ",", expr lt_omega, "]"] ["at", ident ha],
    rcases [expr ha, "with", ident rfl, "|", ident rfl, "|", "⟨", "⟨", ident n, ",", ident rfl, "⟩", ",", "⟨", ident m, ",", ident rfl, "⟩", "⟩"],
    contradiction,
    contradiction,
    rw ["[", "<-", expr ne, "]"] ["at", ident h2a],
    rw ["[", "<-", expr one_le_iff_ne_zero, "]"] ["at", ident h2a, ident hb],
    norm_cast ["at", ident h2a, ident hb, ident h, "⊢"],
    apply [expr le_antisymm _ hb],
    rw ["[", "<-", expr not_lt, "]"] [],
    intro [ident h2b],
    apply [expr ne_of_gt _ h],
    conv_lhs [] [] { rw ["[", "<-", expr mul_one n, "]"] },
    rwa ["[", expr mul_lt_mul_left, "]"] [],
    apply [expr nat.lt_of_succ_le h2a] },
  { rintro ["(", "⟨", "⟨", ident ha, ",", ident hab, "⟩", ",", ident hb, "⟩", "|", ident rfl, "|", ident rfl, ")"],
    { rw ["[", expr mul_eq_max_of_omega_le_left ha hb, ",", expr max_eq_left hab, "]"] [] },
    all_goals { simp [] [] [] [] [] [] } }
end

/-! ### Properties of `add` -/


/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : Cardinal} (h : ω ≤ c) : (c+c) = c :=
  le_antisymmₓ
    (by 
      simpa only [Nat.cast_bit0, Nat.cast_one, mul_eq_self h, two_mul] using
        mul_le_mul_right' ((nat_lt_omega 2).le.trans h) c)
    (self_le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : Cardinal} (ha : ω ≤ a) : (a+b) = max a b :=
  le_antisymmₓ (add_eq_self (le_transₓ ha (le_max_leftₓ a b)) ▸ add_le_add (le_max_leftₓ _ _) (le_max_rightₓ _ _))$
    max_leₓ (self_le_add_right _ _) (self_le_add_left _ _)

theorem add_le_max (a b : Cardinal) : (a+b) ≤ max (max a b) ω :=
  by 
    byCases' ha : ω ≤ a
    ·
      rw [add_eq_max ha]
      exact le_max_leftₓ _ _
    ·
      byCases' hb : ω ≤ b
      ·
        rw [add_commₓ, add_eq_max hb, max_commₓ]
        exact le_max_leftₓ _ _
      ·
        exact le_max_of_le_right (le_of_ltₓ (add_lt_omega (lt_of_not_geₓ ha) (lt_of_not_geₓ hb)))

theorem add_lt_of_lt {a b c : Cardinal} (hc : ω ≤ c) (h1 : a < c) (h2 : b < c) : (a+b) < c :=
  lt_of_le_of_ltₓ (add_le_add (le_max_leftₓ a b) (le_max_rightₓ a b))$
    (lt_or_leₓ (max a b) ω).elim (fun h => lt_of_lt_of_leₓ (add_lt_omega h h) hc)
      fun h =>
        by 
          rw [add_eq_self h] <;> exact max_ltₓ h1 h2

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_add_eq_of_omega_le
{a b c : cardinal}
(h : «expr = »(«expr + »(a, b), c))
(ha : «expr < »(a, c))
(hc : «expr ≤ »(exprω(), c)) : «expr = »(b, c) :=
begin
  apply [expr le_antisymm],
  { rw ["[", "<-", expr h, "]"] [],
    apply [expr self_le_add_left] },
  rw ["[", "<-", expr not_lt, "]"] [],
  intro [ident hb],
  have [] [":", expr «expr < »(«expr + »(a, b), c)] [":=", expr add_lt_of_lt hc ha hb],
  simpa [] [] [] ["[", expr h, ",", expr lt_irrefl, "]"] [] ["using", expr this]
end

theorem add_eq_left {a b : Cardinal} (ha : ω ≤ a) (hb : b ≤ a) : (a+b) = a :=
  by 
    rw [add_eq_max ha, max_eq_leftₓ hb]

theorem add_eq_right {a b : Cardinal} (hb : ω ≤ b) (ha : a ≤ b) : (a+b) = b :=
  by 
    rw [add_commₓ, add_eq_left hb ha]

theorem add_eq_left_iff {a b : Cardinal} : (a+b) = a ↔ max ω b ≤ a ∨ b = 0 :=
  by 
    rw [max_le_iff]
    split 
    ·
      intro h 
      cases' le_or_ltₓ ω a with ha ha
      ·
        left 
        use ha 
        rw [←not_ltₓ]
        intro hb 
        apply ne_of_gtₓ _ h 
        exact lt_of_lt_of_leₓ hb (self_le_add_left b a)
      right 
      rw [←h, add_lt_omega_iff, lt_omega, lt_omega] at ha 
      rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩
      normCast  at h⊢
      rw [←add_right_injₓ, h, add_zeroₓ]
    ·
      rintro (⟨h1, h2⟩ | h3)
      rw [add_eq_max h1, max_eq_leftₓ h2]
      rw [h3, add_zeroₓ]

theorem add_eq_right_iff {a b : Cardinal} : (a+b) = b ↔ max ω a ≤ b ∨ a = 0 :=
  by 
    rw [add_commₓ, add_eq_left_iff]

theorem add_one_eq {a : Cardinal} (ha : ω ≤ a) : (a+1) = a :=
  have  : 1 ≤ a := le_transₓ (le_of_ltₓ one_lt_omega) ha 
  add_eq_left ha this

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem eq_of_add_eq_add_left
{a b c : cardinal}
(h : «expr = »(«expr + »(a, b), «expr + »(a, c)))
(ha : «expr < »(a, exprω())) : «expr = »(b, c) :=
begin
  cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { have [] [":", expr «expr < »(a, b)] [":=", expr lt_of_lt_of_le ha hb],
    rw ["[", expr add_eq_right hb (le_of_lt this), ",", expr eq_comm, "]"] ["at", ident h],
    rw ["[", expr eq_of_add_eq_of_omega_le h this hb, "]"] [] },
  { have [ident hc] [":", expr «expr < »(c, exprω())] [],
    { rw ["[", "<-", expr not_le, "]"] [],
      intro [ident hc],
      apply [expr lt_irrefl exprω()],
      apply [expr lt_of_le_of_lt (le_trans hc (self_le_add_left _ a))],
      rw ["[", "<-", expr h, "]"] [],
      apply [expr add_lt_omega ha hb] },
    rw ["[", expr lt_omega, "]"] ["at", "*"],
    rcases [expr ha, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    rcases [expr hb, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr hc, "with", "⟨", ident k, ",", ident rfl, "⟩"],
    norm_cast ["at", ident h, "⊢"],
    apply [expr add_left_cancel h] }
end

protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : (a+b) = c+b) (hb : b < ω) : a = c :=
  by 
    rw [add_commₓ a b, add_commₓ c b] at h 
    exact Cardinal.eq_of_add_eq_add_left h hb

/-! ### Properties about power -/


theorem pow_le {κ μ : Cardinal.{u}} (H1 : ω ≤ κ) (H2 : μ < ω) : (κ^μ) ≤ κ :=
  let ⟨n, H3⟩ := lt_omega.1 H2 
  H3.symm ▸
    Quotientₓ.induction_on κ
      (fun α H1 =>
        Nat.recOn n
          (le_of_ltₓ$
            lt_of_lt_of_leₓ
              (by 
                rw [Nat.cast_zero, power_zero] <;> exact one_lt_omega)
              H1)
          fun n ih =>
            trans_rel_left _
              (by 
                rw [Nat.cast_succ, power_add, power_one] <;> exact mul_le_mul_right' ih _)
              (mul_eq_self H1))
      H1

theorem power_self_eq {c : Cardinal} (h : ω ≤ c) : (c^c) = (2^c) :=
  by 
    apply le_antisymmₓ
    ·
      apply le_transₓ (power_le_power_right$ le_of_ltₓ$ cantor c)
      rw [←power_mul, mul_eq_self h]
    ·
      convert power_le_power_right (le_transₓ (le_of_ltₓ$ nat_lt_omega 2) h)
      apply nat.cast_two.symm

theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
  (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} (# ι)) : Prod c = (2^lift.{v} (# ι)) :=
  by 
    rw [←lift_id' (Prod c), lift_prod, ←lift_two_power]
    apply le_antisymmₓ
    ·
      refine' (prod_le_prod _ _ h₂).trans_eq _ 
      rw [prod_const, lift_lift, ←lift_power, power_self_eq (omega_le_mk ι), lift_umax.{u, v}]
    ·
      rw [←prod_const', lift_prod]
      refine' prod_le_prod _ _ fun i => _ 
      rw [lift_two, ←lift_two.{u, v}, lift_le]
      exact h₁ i

theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ω ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) : (c₂^c₁) = (2^c₁) :=
  le_antisymmₓ (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)

theorem nat_power_eq {c : Cardinal.{u}} (h : ω ≤ c) {n : ℕ} (hn : 2 ≤ n) : ((n : Cardinal.{u})^c) = (2^c) :=
  power_eq_two_power h
    (by 
      assumptionModCast)
    ((nat_lt_omega n).le.trans h)

theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ω ≤ c) : (c^(n : Cardinal.{u})) ≤ c :=
  pow_le h (nat_lt_omega n)

theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : (c^(n : Cardinal.{u})) ≤ max c ω :=
  by 
    byCases' hc : ω ≤ c
    ·
      exact le_max_of_le_left (power_nat_le hc)
    ·
      exact le_max_of_le_right (le_of_ltₓ (power_lt_omega (lt_of_not_geₓ hc) (nat_lt_omega _)))

@[simp]
theorem powerlt_omega {c : Cardinal} (h : ω ≤ c) : c ^< ω = c :=
  by 
    apply le_antisymmₓ
    ·
      rw [powerlt_le]
      intro c' 
      rw [lt_omega]
      rintro ⟨n, rfl⟩
      apply power_nat_le h 
    convert le_powerlt one_lt_omega 
    rw [power_one]

theorem powerlt_omega_le (c : Cardinal) : c ^< ω ≤ max c ω :=
  by 
    cases le_or_ltₓ ω c
    ·
      rw [powerlt_omega h]
      apply le_max_leftₓ 
    rw [powerlt_le]
    intro c' hc' 
    refine' le_transₓ (le_of_ltₓ$ power_lt_omega h hc') (le_max_rightₓ _ _)

/-! ### Computing cardinality of various types -/


theorem mk_list_eq_mk (α : Type u) [Infinite α] : # (List α) = # α :=
  have H1 : ω ≤ # α := omega_le_mk α 
  Eq.symm$
    le_antisymmₓ ⟨⟨fun x => [x], fun x y H => (List.cons.injₓ H).1⟩⟩$
      calc # (List α) = Sum fun n : ℕ => # α^(n : Cardinal.{u}) := mk_list_eq_sum_pow α 
        _ ≤ Sum fun n : ℕ => # α := sum_le_sum _ _$ fun n => pow_le H1$ nat_lt_omega n 
        _ = # α :=
        by 
          simp [H1]
        

theorem mk_finset_eq_mk (α : Type u) [Infinite α] : # (Finset α) = # α :=
  Eq.symm$
    le_antisymmₓ (mk_le_of_injective fun x y => Finset.singleton_inj.1)$
      calc # (Finset α) ≤ # (List α) := mk_le_of_surjective List.to_finset_surjective 
        _ = # α := mk_list_eq_mk α
        

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mk_bounded_set_le_of_infinite
(α : Type u)
[infinite α]
(c : cardinal) : «expr ≤ »(«expr#»() {t : set α // «expr ≤ »(mk t, c)}, «expr ^ »(«expr#»() α, c)) :=
begin
  refine [expr le_trans _ (by rw ["[", "<-", expr add_one_eq (omega_le_mk α), "]"] [])],
  induction [expr c] ["using", ident cardinal.induction_on] ["with", ident β] [],
  fapply [expr mk_le_of_surjective],
  { intro [ident f],
    use [expr «expr ⁻¹' »(sum.inl, range f)],
    refine [expr le_trans (mk_preimage_of_injective _ _ (λ x y, sum.inl.inj)) _],
    apply [expr mk_range_le] },
  rintro ["⟨", ident s, ",", "⟨", ident g, "⟩", "⟩"],
  use [expr λ y, if h : «expr∃ , »((x : s), «expr = »(g x, y)) then sum.inl (classical.some h).val else sum.inr ⟨⟩],
  apply [expr subtype.eq],
  ext [] [] [],
  split,
  { rintro ["⟨", ident y, ",", ident h, "⟩"],
    dsimp ["only"] [] [] ["at", ident h],
    by_cases [expr h', ":", expr «expr∃ , »((z : s), «expr = »(g z, y))],
    { rw ["[", expr dif_pos h', "]"] ["at", ident h],
      cases [expr sum.inl.inj h] [],
      exact [expr (classical.some h').2] },
    { rw ["[", expr dif_neg h', "]"] ["at", ident h],
      cases [expr h] [] } },
  { intro [ident h],
    have [] [":", expr «expr∃ , »((z : s), «expr = »(g z, g ⟨x, h⟩))] [],
    exact [expr ⟨⟨x, h⟩, rfl⟩],
    use [expr g ⟨x, h⟩],
    dsimp ["only"] [] [] [],
    rw ["[", expr dif_pos this, "]"] [],
    congr' [] [],
    suffices [] [":", expr «expr = »(classical.some this, ⟨x, h⟩)],
    exact [expr congr_arg subtype.val this],
    apply [expr g.2],
    exact [expr classical.some_spec this] }
end

theorem mk_bounded_set_le (α : Type u) (c : Cardinal) : # { t : Set α // # t ≤ c } ≤ (max (# α) ω^c) :=
  by 
    trans # { t : Set (Sum (Ulift.{u} ℕ) α) // # t ≤ c }
    ·
      refine' ⟨embedding.subtype_map _ _⟩
      apply embedding.image 
      use Sum.inr 
      apply Sum.inr.injₓ 
      intro s hs 
      exact le_transₓ mk_image_le hs 
    refine' le_transₓ (mk_bounded_set_le_of_infinite (Sum (Ulift.{u} ℕ) α) c) _ 
    rw [max_commₓ, ←add_eq_max] <;> rfl

theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
  # { t : Set α // t ⊆ s ∧ # t ≤ c } ≤ (max (# s) ω^c) :=
  by 
    refine' le_transₓ _ (mk_bounded_set_le s c)
    refine' ⟨embedding.cod_restrict _ _ _⟩
    use fun t => coeₓ ⁻¹' t.1
    ·
      rintro ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h 
      apply Subtype.eq 
      dsimp only  at h⊢
      refine' (preimage_eq_preimage' _ _).1 h <;> rw [Subtype.range_coe] <;> assumption 
    rintro ⟨t, h1t, h2t⟩
    exact le_transₓ (mk_preimage_of_injective _ _ Subtype.val_injective) h2t

/-! ### Properties of `compl` -/


theorem mk_compl_of_infinite {α : Type _} [Infinite α] (s : Set α) (h2 : # s < # α) : # («expr ᶜ» s : Set α) = # α :=
  by 
    refine' eq_of_add_eq_of_omega_le _ h2 (omega_le_mk α)
    exact mk_sum_compl s

theorem mk_compl_finset_of_infinite {α : Type _} [Infinite α] (s : Finset α) :
  # («expr ᶜ» («expr↑ » s) : Set α) = # α :=
  by 
    apply mk_compl_of_infinite 
    exact (finset_card_lt_omega s).trans_le (omega_le_mk α)

theorem mk_compl_eq_mk_compl_infinite {α : Type _} [Infinite α] {s t : Set α} (hs : # s < # α) (ht : # t < # α) :
  # («expr ᶜ» s : Set α) = # («expr ᶜ» t : Set α) :=
  by 
    rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht]

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mk_compl_eq_mk_compl_finite_lift
{α : Type u}
{β : Type v}
[fintype α]
{s : set α}
{t : set β}
(h1 : «expr = »(lift.{max v w} («expr#»() α), lift.{max u w} («expr#»() β)))
(h2 : «expr = »(lift.{max v w} («expr#»() s), lift.{max u w} («expr#»() t))) : «expr = »(lift.{max v w} («expr#»() («expr ᶜ»(s) : set α)), lift.{max u w} («expr#»() («expr ᶜ»(t) : set β))) :=
begin
  rcases [expr lift_mk_eq.1 h1, "with", "⟨", ident e, "⟩"],
  letI [] [":", expr fintype β] [":=", expr fintype.of_equiv α e],
  replace [ident h1] [":", expr «expr = »(fintype.card α, fintype.card β)] [":=", expr (fintype.of_equiv_card _).symm],
  classical,
  lift [expr s] ["to", expr finset α] ["using", expr finite.of_fintype s] [],
  lift [expr t] ["to", expr finset β] ["using", expr finite.of_fintype t] [],
  simp [] [] ["only"] ["[", expr finset.coe_sort_coe, ",", expr mk_finset, ",", expr lift_nat_cast, ",", expr nat.cast_inj, "]"] [] ["at", ident h2],
  simp [] [] ["only"] ["[", "<-", expr finset.coe_compl, ",", expr finset.coe_sort_coe, ",", expr mk_finset, ",", expr finset.card_compl, ",", expr lift_nat_cast, ",", expr nat.cast_inj, ",", expr h1, ",", expr h2, "]"] [] []
end

theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Fintype α] {s : Set α} {t : Set β} (h1 : # α = # β)
  (h : # s = # t) : # («expr ᶜ» s : Set α) = # («expr ᶜ» t : Set β) :=
  by 
    rw [←lift_inj]
    apply mk_compl_eq_mk_compl_finite_lift <;> rwa [lift_inj]

theorem mk_compl_eq_mk_compl_finite_same {α : Type _} [Fintype α] {s t : Set α} (h : # s = # t) :
  # («expr ᶜ» s : Set α) = # («expr ᶜ» t : Set α) :=
  mk_compl_eq_mk_compl_finite rfl h

/-! ### Extending an injection to an equiv -/


-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem extend_function
{α β : Type*}
{s : set α}
(f : «expr ↪ »(s, β))
(h : nonempty «expr ≃ »((«expr ᶜ»(s) : set α), («expr ᶜ»(range f) : set β))) : «expr∃ , »((g : «expr ≃ »(α, β)), ∀
 x : s, «expr = »(g x, f x)) :=
begin
  intros [],
  have [] [] [":=", expr h],
  cases [expr this] ["with", ident g],
  let [ident h] [":", expr «expr ≃ »(α, β)] [":=", expr (set.sum_compl (s : set α)).symm.trans ((sum_congr (equiv.of_injective f f.2) g).trans (set.sum_compl (range f)))],
  refine [expr ⟨h, _⟩],
  rintro ["⟨", ident x, ",", ident hx, "⟩"],
  simp [] [] [] ["[", expr set.sum_compl_symm_apply_of_mem, ",", expr hx, "]"] [] []
end

theorem extend_function_finite {α β : Type _} [Fintype α] {s : Set α} (f : s ↪ β) (h : Nonempty (α ≃ β)) :
  ∃ g : α ≃ β, ∀ x : s, g x = f x :=
  by 
    apply extend_function f 
    cases' id h with g 
    rw [←lift_mk_eq] at h 
    rw [←lift_mk_eq, mk_compl_eq_mk_compl_finite_lift h]
    rw [mk_range_eq_lift]
    exact f.2

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem extend_function_of_lt
{α β : Type*}
{s : set α}
(f : «expr ↪ »(s, β))
(hs : «expr < »(«expr#»() s, «expr#»() α))
(h : nonempty «expr ≃ »(α, β)) : «expr∃ , »((g : «expr ≃ »(α, β)), ∀ x : s, «expr = »(g x, f x)) :=
begin
  casesI [expr fintype_or_infinite α] [],
  { exact [expr extend_function_finite f h] },
  { apply [expr extend_function f],
    cases [expr id h] ["with", ident g],
    haveI [] [] [":=", expr infinite.of_injective _ g.injective],
    rw ["[", "<-", expr lift_mk_eq', "]"] ["at", ident h, "⊢"],
    rwa ["[", expr mk_compl_of_infinite s hs, ",", expr mk_compl_of_infinite, "]"] [],
    rwa ["[", "<-", expr lift_lt, ",", expr mk_range_eq_of_injective f.injective, ",", "<-", expr h, ",", expr lift_lt, "]"] [] }
end

section Bit

/-!
This section proves inequalities for `bit0` and `bit1`, enabling `simp` to solve inequalities
for numeral cardinals. The complexity of the resulting algorithm is not good, as in some cases
`simp` reduces an inequality to a disjunction of two situations, depending on whether a cardinal
is finite or infinite. Since the evaluation of the branches is not lazy, this is bad. It is good
enough for practical situations, though.

For specific numbers, these inequalities could also be deduced from the corresponding
inequalities of natural numbers using `norm_cast`:
```
example : (37 : cardinal) < 42 :=
by { norm_cast, norm_num }
```
-/


theorem bit0_ne_zero (a : Cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 :=
  by 
    simp [bit0]

@[simp]
theorem bit1_ne_zero (a : Cardinal) : ¬bit1 a = 0 :=
  by 
    simp [bit1]

@[simp]
theorem zero_lt_bit0 (a : Cardinal) : 0 < bit0 a ↔ 0 < a :=
  by 
    rw [←not_iff_not]
    simp [bit0]

@[simp]
theorem zero_lt_bit1 (a : Cardinal) : 0 < bit1 a :=
  lt_of_lt_of_leₓ zero_lt_one (self_le_add_left _ _)

@[simp]
theorem one_le_bit0 (a : Cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
  ⟨fun h => (zero_lt_bit0 a).mp (lt_of_lt_of_leₓ zero_lt_one h),
    fun h => le_transₓ (one_le_iff_pos.mpr h) (self_le_add_left a a)⟩

@[simp]
theorem one_le_bit1 (a : Cardinal) : 1 ≤ bit1 a :=
  self_le_add_left _ _

theorem bit0_eq_self {c : Cardinal} (h : ω ≤ c) : bit0 c = c :=
  add_eq_self h

@[simp]
theorem bit0_lt_omega {c : Cardinal} : bit0 c < ω ↔ c < ω :=
  by 
    simp [bit0, add_lt_omega_iff]

@[simp]
theorem omega_le_bit0 {c : Cardinal} : ω ≤ bit0 c ↔ ω ≤ c :=
  by 
    rw [←not_iff_not]
    simp 

@[simp]
theorem bit1_eq_self_iff {c : Cardinal} : bit1 c = c ↔ ω ≤ c :=
  by 
    byCases' h : ω ≤ c
    ·
      simp only [bit1, bit0_eq_self h, h, eq_self_iff_true, add_one_of_omega_le]
    ·
      refine' iff_of_false (ne_of_gtₓ _) h 
      rcases lt_omega.1 (not_leₓ.1 h) with ⟨n, rfl⟩
      normCast 
      dsimp [bit1, bit0]
      linarith

@[simp]
theorem bit1_lt_omega {c : Cardinal} : bit1 c < ω ↔ c < ω :=
  by 
    simp [bit1, bit0, add_lt_omega_iff, one_lt_omega]

@[simp]
theorem omega_le_bit1 {c : Cardinal} : ω ≤ bit1 c ↔ ω ≤ c :=
  by 
    rw [←not_iff_not]
    simp 

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem bit0_le_bit0 {a b : cardinal} : «expr ↔ »(«expr ≤ »(bit0 a, bit0 b), «expr ≤ »(a, b)) :=
begin
  cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha]; cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { rw ["[", expr bit0_eq_self ha, ",", expr bit0_eq_self hb, "]"] [] },
  { rw [expr bit0_eq_self ha] [],
    refine [expr iff_of_false (λ h, _) (not_le_of_lt (hb.trans_le ha))],
    have [ident A] [":", expr «expr < »(bit0 b, exprω())] [],
    by simpa [] [] [] [] [] ["using", expr hb],
    exact [expr lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le A ha) h)] },
  { rw ["[", expr bit0_eq_self hb, "]"] [],
    exact [expr iff_of_true ((bit0_lt_omega.2 ha).le.trans hb) (ha.le.trans hb)] },
  { rcases [expr lt_omega.1 ha, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr lt_omega.1 hb, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    norm_cast [],
    exact [expr bit0_le_bit0] }
end

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem bit0_le_bit1 {a b : cardinal} : «expr ↔ »(«expr ≤ »(bit0 a, bit1 b), «expr ≤ »(a, b)) :=
begin
  cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha]; cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { rw ["[", expr bit0_eq_self ha, ",", expr bit1_eq_self_iff.2 hb, "]"] [] },
  { rw [expr bit0_eq_self ha] [],
    refine [expr iff_of_false (λ h, _) (not_le_of_lt (hb.trans_le ha))],
    have [ident A] [":", expr «expr < »(bit1 b, exprω())] [],
    by simpa [] [] [] [] [] ["using", expr hb],
    exact [expr lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le A ha) h)] },
  { rw ["[", expr bit1_eq_self_iff.2 hb, "]"] [],
    exact [expr iff_of_true ((bit0_lt_omega.2 ha).le.trans hb) (ha.le.trans hb)] },
  { rcases [expr lt_omega.1 ha, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr lt_omega.1 hb, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    norm_cast [],
    exact [expr nat.bit0_le_bit1_iff] }
end

@[simp]
theorem bit1_le_bit1 {a b : Cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b :=
  by 
    split 
    ·
      intro h 
      apply bit0_le_bit1.1 (le_transₓ (self_le_add_right (bit0 a) 1) h)
    ·
      intro h 
      calc ((a+a)+1) ≤ (a+b)+1 := add_le_add_right (add_le_add_left h a) 1_ ≤ (b+b)+1 :=
        add_le_add_right (add_le_add_right h b) 1

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem bit1_le_bit0
{a
 b : cardinal} : «expr ↔ »(«expr ≤ »(bit1 a, bit0 b), «expr ∨ »(«expr < »(a, b), «expr ∧ »(«expr ≤ »(a, b), «expr ≤ »(exprω(), a)))) :=
begin
  cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha]; cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { simp [] [] ["only"] ["[", expr bit1_eq_self_iff.mpr ha, ",", expr bit0_eq_self hb, ",", expr ha, ",", expr and_true, "]"] [] [],
    refine [expr ⟨λ h, or.inr h, λ h, _⟩],
    cases [expr h] [],
    { exact [expr le_of_lt h] },
    { exact [expr h] } },
  { rw [expr bit1_eq_self_iff.2 ha] [],
    refine [expr iff_of_false (λ h, _) (λ h, _)],
    { have [ident A] [":", expr «expr < »(bit0 b, exprω())] [],
      by simpa [] [] [] [] [] ["using", expr hb],
      exact [expr lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le A ha) h)] },
    { exact [expr not_le_of_lt (hb.trans_le ha) (h.elim le_of_lt and.left)] } },
  { rw ["[", expr bit0_eq_self hb, "]"] [],
    exact [expr iff_of_true ((bit1_lt_omega.2 ha).le.trans hb) «expr $ »(or.inl, ha.trans_le hb)] },
  { rcases [expr lt_omega.1 ha, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr lt_omega.1 hb, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    norm_cast [],
    simp [] [] [] ["[", expr not_le.mpr ha, "]"] [] [] }
end

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem bit0_lt_bit0 {a b : cardinal} : «expr ↔ »(«expr < »(bit0 a, bit0 b), «expr < »(a, b)) :=
begin
  cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha]; cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { rw ["[", expr bit0_eq_self ha, ",", expr bit0_eq_self hb, "]"] [] },
  { rw [expr bit0_eq_self ha] [],
    refine [expr iff_of_false (λ h, _) (not_lt_of_le (hb.le.trans ha))],
    have [ident A] [":", expr «expr < »(bit0 b, exprω())] [],
    by simpa [] [] [] [] [] ["using", expr hb],
    exact [expr lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h)] },
  { rw ["[", expr bit0_eq_self hb, "]"] [],
    exact [expr iff_of_true ((bit0_lt_omega.2 ha).trans_le hb) (ha.trans_le hb)] },
  { rcases [expr lt_omega.1 ha, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr lt_omega.1 hb, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    norm_cast [],
    exact [expr bit0_lt_bit0] }
end

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem bit1_lt_bit0 {a b : cardinal} : «expr ↔ »(«expr < »(bit1 a, bit0 b), «expr < »(a, b)) :=
begin
  cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha]; cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { rw ["[", expr bit1_eq_self_iff.2 ha, ",", expr bit0_eq_self hb, "]"] [] },
  { rw [expr bit1_eq_self_iff.2 ha] [],
    refine [expr iff_of_false (λ h, _) (not_lt_of_le (hb.le.trans ha))],
    have [ident A] [":", expr «expr < »(bit0 b, exprω())] [],
    by simpa [] [] [] [] [] ["using", expr hb],
    exact [expr lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h)] },
  { rw ["[", expr bit0_eq_self hb, "]"] [],
    exact [expr iff_of_true ((bit1_lt_omega.2 ha).trans_le hb) (ha.trans_le hb)] },
  { rcases [expr lt_omega.1 ha, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr lt_omega.1 hb, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    norm_cast [],
    exact [expr nat.bit1_lt_bit0_iff] }
end

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem bit1_lt_bit1 {a b : cardinal} : «expr ↔ »(«expr < »(bit1 a, bit1 b), «expr < »(a, b)) :=
begin
  cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha]; cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { rw ["[", expr bit1_eq_self_iff.2 ha, ",", expr bit1_eq_self_iff.2 hb, "]"] [] },
  { rw [expr bit1_eq_self_iff.2 ha] [],
    refine [expr iff_of_false (λ h, _) (not_lt_of_le (hb.le.trans ha))],
    have [ident A] [":", expr «expr < »(bit1 b, exprω())] [],
    by simpa [] [] [] [] [] ["using", expr hb],
    exact [expr lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h)] },
  { rw ["[", expr bit1_eq_self_iff.2 hb, "]"] [],
    exact [expr iff_of_true ((bit1_lt_omega.2 ha).trans_le hb) (ha.trans_le hb)] },
  { rcases [expr lt_omega.1 ha, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr lt_omega.1 hb, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    norm_cast [],
    exact [expr bit1_lt_bit1] }
end

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem bit0_lt_bit1
{a
 b : cardinal} : «expr ↔ »(«expr < »(bit0 a, bit1 b), «expr ∨ »(«expr < »(a, b), «expr ∧ »(«expr ≤ »(a, b), «expr < »(a, exprω())))) :=
begin
  cases [expr le_or_lt exprω() a] ["with", ident ha, ident ha]; cases [expr le_or_lt exprω() b] ["with", ident hb, ident hb],
  { simp [] [] [] ["[", expr bit0_eq_self ha, ",", expr bit1_eq_self_iff.2 hb, ",", expr not_lt.mpr ha, "]"] [] [] },
  { rw [expr bit0_eq_self ha] [],
    refine [expr iff_of_false (λ h, _) (λ h, _)],
    { have [ident A] [":", expr «expr < »(bit1 b, exprω())] [],
      by simpa [] [] [] [] [] ["using", expr hb],
      exact [expr lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h)] },
    { exact [expr not_le_of_lt (hb.trans_le ha) (h.elim le_of_lt and.left)] } },
  { rw ["[", expr bit1_eq_self_iff.2 hb, "]"] [],
    exact [expr iff_of_true ((bit0_lt_omega.2 ha).trans_le hb) «expr $ »(or.inl, ha.trans_le hb)] },
  { rcases [expr lt_omega.1 ha, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    rcases [expr lt_omega.1 hb, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    norm_cast [],
    simp [] [] ["only"] ["[", expr ha, ",", expr and_true, ",", expr nat.bit0_lt_bit1_iff, ",", expr or_iff_right_of_imp le_of_lt, "]"] [] [] }
end

theorem one_lt_two : (1 : Cardinal) < 2 :=
  by 
    normCast 
    normNum

@[simp]
theorem one_lt_bit0 {a : Cardinal} : 1 < bit0 a ↔ 0 < a :=
  by 
    simp [←bit1_zero]

@[simp]
theorem one_lt_bit1 (a : Cardinal) : 1 < bit1 a ↔ 0 < a :=
  by 
    simp [←bit1_zero]

@[simp]
theorem one_le_one : (1 : Cardinal) ≤ 1 :=
  le_reflₓ _

end Bit

end Cardinal

-- error in SetTheory.CardinalOrdinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem not_injective_of_ordinal {α : Type u} (f : ordinal.{u} → α) : «expr¬ »(function.injective f) :=
begin
  let [ident g] [":", expr ordinal.{u} → ulift.{u+1} α] [":=", expr λ o, ulift.up (f o)],
  suffices [] [":", expr «expr¬ »(function.injective g)],
  { intro [ident hf],
    exact [expr this (equiv.ulift.symm.injective.comp hf)] },
  intro [ident hg],
  replace [ident hg] [] [":=", expr cardinal.mk_le_of_injective hg],
  rw [expr cardinal.mk_ulift] ["at", ident hg],
  have [] [] [":=", expr hg.trans_lt (cardinal.lift_lt_univ _)],
  rw [expr cardinal.univ_id] ["at", ident this],
  exact [expr lt_irrefl _ this]
end

theorem not_injective_of_ordinal_of_small {α : Type v} [Small.{u} α] (f : Ordinal.{u} → α) : ¬Function.Injective f :=
  by 
    intro hf 
    apply not_injective_of_ordinal (equivShrink α ∘ f)
    exact (equivShrink _).Injective.comp hf

