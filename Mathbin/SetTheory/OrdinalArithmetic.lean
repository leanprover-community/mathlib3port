import Mathbin.SetTheory.Ordinal

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define correspondingly a subtraction, a division, a successor
function, a power function and a logarithm function.

We also define limit ordinals and prove the basic induction principle on ordinals separating
successor ordinals and limit ordinals, in `limit_rec_on`.

## Main definitions and results

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
* `o₁ - o₂` is the unique ordinal `o` such that `o₂ + o = o₁`, when `o₂ ≤ o₁`.
* `o₁ * o₂` is the lexicographic order on `o₂ × o₁`.
* `o₁ / o₂` is the ordinal `o` such that `o₁ = o₂ * o + o'` with `o' < o₂`. We also define the
  divisibility predicate, and a modulo operation.
* `succ o = o + 1` is the successor of `o`.
* `pred o` if the predecessor of `o`. If `o` is not a successor, we set `pred o = o`.

We also define the power function and the logarithm function on ordinals, and discuss the properties
of casts of natural numbers of and of `omega` with respect to these operations.

Some properties of the operations are also used to discuss general tools on ordinals:

* `is_limit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limit_rec_on` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.

* `is_normal`: a function `f : ordinal → ordinal` satisfies `is_normal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.
* `nfp f a`: the next fixed point of a function `f` on ordinals, above `a`. It behaves well
  for normal functions.

* `CNF b o` is the Cantor normal form of the ordinal `o` in base `b`.

* `sup`: the supremum of an indexed family of ordinals in `Type u`, as an ordinal in `Type u`.
* `bsup`: the supremum of a set of ordinals indexed by ordinals less than a given ordinal `o`.
-/


noncomputable theory

open Function Cardinal Set Equiv

open_locale Classical Cardinal

universe u v w

variable {α : Type _} {β : Type _} {γ : Type _} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

namespace Ordinal

/-! ### Further properties of addition on ordinals -/


@[simp]
theorem lift_add a b : lift (a+b) = lift a+lift b :=
  Quotientₓ.induction_on₂ a b$
    fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
      Quotientₓ.sound
        ⟨(RelIso.preimage Equiv.ulift _).trans
            (RelIso.sumLexCongr (RelIso.preimage Equiv.ulift _) (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]
theorem lift_succ a : lift (succ a) = succ (lift a) :=
  by 
    unfold succ <;> simp only [lift_add, lift_one]

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_le_add_iff_left
(a)
{b c : ordinal} : «expr ↔ »(«expr ≤ »(«expr + »(a, b), «expr + »(a, c)), «expr ≤ »(b, c)) :=
⟨«expr $ »(induction_on a, λ
  α
  r
  hr, «expr $ »(induction_on b, λ
   β₁
   s₁
   hs₁, «expr $ »(induction_on c, λ
    (β₂ s₂ hs₂)
    ⟨f⟩, ⟨have fl : ∀
     a, «expr = »(f (sum.inl a), sum.inl a) := λ
     a, by simpa [] [] ["only"] ["[", expr initial_seg.trans_apply, ",", expr initial_seg.le_add_apply, "]"] [] ["using", expr @initial_seg.eq _ _ _ _ (@sum.lex.is_well_order _ _ _ _ hr hs₂) ((initial_seg.le_add r s₁).trans f) (initial_seg.le_add r s₂) a],
     have ∀ b, {b' // «expr = »(f (sum.inr b), sum.inr b')}, begin
       intro [ident b],
       cases [expr e, ":", expr f (sum.inr b)] [],
       { rw ["<-", expr fl] ["at", ident e],
         have [] [] [":=", expr f.inj' e],
         contradiction },
       { exact [expr ⟨_, rfl⟩] }
     end,
     let g (b) := (this b).1 in
     have fr : ∀ b, «expr = »(f (sum.inr b), sum.inr (g b)), from λ b, (this b).2,
     ⟨⟨⟨g, λ
        x
        y
        h, by injection [expr f.inj' (by rw ["[", expr fr, ",", expr fr, ",", expr h, "]"] [] : «expr = »(f (sum.inr x), f (sum.inr y)))] []⟩, λ
       a
       b, by simpa [] [] ["only"] ["[", expr sum.lex_inr_inr, ",", expr fr, ",", expr rel_embedding.coe_fn_to_embedding, ",", expr initial_seg.coe_fn_to_rel_embedding, ",", expr function.embedding.coe_fn_mk, "]"] [] ["using", expr @rel_embedding.map_rel_iff _ _ _ _ f.to_rel_embedding (sum.inr a) (sum.inr b)]⟩, λ
      a b H, begin
        rcases [expr f.init' (by rw [expr fr] []; exact [expr sum.lex_inr_inr.2 H]), "with", "⟨", ident a', "|", ident a', ",", ident h, "⟩"],
        { rw [expr fl] ["at", ident h],
          cases [expr h] [] },
        { rw [expr fr] ["at", ident h],
          exact [expr ⟨a', sum.inr.inj h⟩] }
      end⟩⟩))), λ h, add_le_add_left h _⟩

theorem add_succ (o₁ o₂ : Ordinal) : (o₁+succ o₂) = succ (o₁+o₂) :=
  (add_assocₓ _ _ _).symm

@[simp]
theorem succ_zero : succ 0 = 1 :=
  zero_addₓ _

theorem one_le_iff_pos {o : Ordinal} : 1 ≤ o ↔ 0 < o :=
  by 
    rw [←succ_zero, succ_le]

theorem one_le_iff_ne_zero {o : Ordinal} : 1 ≤ o ↔ o ≠ 0 :=
  by 
    rw [one_le_iff_pos, Ordinal.pos_iff_ne_zero]

theorem succ_pos (o : Ordinal) : 0 < succ o :=
  lt_of_le_of_ltₓ (Ordinal.zero_le _) (lt_succ_self _)

theorem succ_ne_zero (o : Ordinal) : succ o ≠ 0 :=
  ne_of_gtₓ$ succ_pos o

@[simp]
theorem card_succ (o : Ordinal) : card (succ o) = card o+1 :=
  by 
    simp only [succ, card_add, card_one]

theorem nat_cast_succ (n : ℕ) : (succ n : Ordinal) = n.succ :=
  rfl

theorem add_left_cancelₓ a {b c : Ordinal} : ((a+b) = a+c) ↔ b = c :=
  by 
    simp only [le_antisymm_iffₓ, add_le_add_iff_left]

theorem lt_succ {a b : Ordinal} : a < succ b ↔ a ≤ b :=
  by 
    rw [←not_leₓ, succ_le, not_ltₓ]

theorem add_lt_add_iff_left a {b c : Ordinal} : ((a+b) < a+c) ↔ b < c :=
  by 
    rw [←not_leₓ, ←not_leₓ, add_le_add_iff_left]

theorem lt_of_add_lt_add_right {a b c : Ordinal} : ((a+b) < c+b) → a < c :=
  lt_imp_lt_of_le_imp_le fun h => add_le_add_right h _

@[simp]
theorem succ_lt_succ {a b : Ordinal} : succ a < succ b ↔ a < b :=
  by 
    rw [lt_succ, succ_le]

@[simp]
theorem succ_le_succ {a b : Ordinal} : succ a ≤ succ b ↔ a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 succ_lt_succ

theorem succ_inj {a b : Ordinal} : succ a = succ b ↔ a = b :=
  by 
    simp only [le_antisymm_iffₓ, succ_le_succ]

theorem add_le_add_iff_right {a b : Ordinal} (n : ℕ) : ((a+n) ≤ b+n) ↔ a ≤ b :=
  by 
    induction' n with n ih <;> [rw [Nat.cast_zero, add_zeroₓ, add_zeroₓ],
      rw [←nat_cast_succ, add_succ, add_succ, succ_le_succ, ih]]

theorem add_right_cancelₓ {a b : Ordinal} (n : ℕ) : ((a+n) = b+n) ↔ a = b :=
  by 
    simp only [le_antisymm_iffₓ, add_le_add_iff_right]

/-! ### The zero ordinal -/


@[simp]
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
  ⟨induction_on o$
      fun α r _ h =>
        by 
          refine' le_antisymmₓ (le_of_not_ltₓ$ fun hn => mk_ne_zero_iff.2 _ h) (Ordinal.zero_le _)
          rw [←succ_le, succ_zero] at hn 
          cases' hn with f 
          exact ⟨f PUnit.unit⟩,
    fun e =>
      by 
        simp only [e, card_zero]⟩

@[simp]
theorem type_eq_zero_of_empty [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  card_eq_zero.symm.mpr (mk_eq_zero _)

@[simp]
theorem type_eq_zero_iff_is_empty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α :=
  (@card_eq_zero (type r)).symm.trans mk_eq_zero_iff

theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r ≠ 0 ↔ Nonempty α :=
  (not_congr (@card_eq_zero (type r))).symm.trans mk_ne_zero_iff

protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
  type_ne_zero_iff_nonempty.2 ⟨PUnit.unit⟩

instance : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, Ordinal.one_ne_zero⟩⟩

theorem zero_lt_one : (0 : Ordinal) < 1 :=
  lt_iff_le_and_ne.2 ⟨Ordinal.zero_le _, Ne.symm$ Ordinal.one_ne_zero⟩

/-! ### The predecessor of an ordinal -/


/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : Ordinal.{u}) : Ordinal.{u} :=
  if h : ∃ a, o = succ a then Classical.some h else o

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem pred_succ (o) : «expr = »(pred (succ o), o) :=
by have [ident h] [":", expr «expr∃ , »((a), «expr = »(succ o, succ a))] [":=", expr ⟨_, rfl⟩]; simpa [] [] ["only"] ["[", expr pred, ",", expr dif_pos h, "]"] [] ["using", expr «expr $ »(succ_inj.1, classical.some_spec h).symm]

theorem pred_le_self o : pred o ≤ o :=
  if h : ∃ a, o = succ a then
    let ⟨a, e⟩ := h 
    by 
      rw [e, pred_succ] <;> exact le_of_ltₓ (lt_succ_self _)
  else
    by 
      rw [pred, dif_neg h]

theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬∃ a, o = succ a :=
  ⟨fun e ⟨a, e'⟩ =>
      by 
        rw [e', pred_succ] at e <;> exact ne_of_ltₓ (lt_succ_self _) e,
    fun h => dif_neg h⟩

theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a :=
  Iff.trans
    (by 
      simp only [le_antisymm_iffₓ, pred_le_self, true_andₓ, not_leₓ])
    (iff_not_comm.1 pred_eq_iff_not_succ).symm

theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a :=
  ⟨fun e => ⟨_, e.symm⟩,
    fun ⟨a, e⟩ =>
      by 
        simp only [e, pred_succ]⟩

theorem succ_lt_of_not_succ {o} (h : ¬∃ a, o = succ a) {b} : succ b < o ↔ b < o :=
  ⟨lt_transₓ (lt_succ_self _), fun l => lt_of_le_of_neₓ (succ_le.2 l) fun e => h ⟨_, e.symm⟩⟩

theorem lt_pred {a b} : a < pred b ↔ succ a < b :=
  if h : ∃ a, b = succ a then
    let ⟨c, e⟩ := h 
    by 
      rw [e, pred_succ, succ_lt_succ]
  else
    by 
      simp only [pred, dif_neg h, succ_lt_of_not_succ h]

theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b :=
  le_iff_le_iff_lt_iff_lt.2 lt_pred

@[simp]
theorem lift_is_succ {o} : (∃ a, lift o = succ a) ↔ ∃ a, o = succ a :=
  ⟨fun ⟨a, h⟩ =>
      let ⟨b, e⟩ := lift_down$ show a ≤ lift o from le_of_ltₓ$ h.symm ▸ lt_succ_self _
      ⟨b,
        lift_inj.1$
          by 
            rw [h, ←e, lift_succ]⟩,
    fun ⟨a, h⟩ =>
      ⟨lift a,
        by 
          simp only [h, lift_succ]⟩⟩

@[simp]
theorem lift_pred o : lift (pred o) = pred (lift o) :=
  if h : ∃ a, o = succ a then
    by 
      cases' h with a e <;> simp only [e, pred_succ, lift_succ]
  else
    by 
      rw [pred_eq_iff_not_succ.2 h, pred_eq_iff_not_succ.2 (mt lift_is_succ.1 h)]

/-! ### Limit ordinals -/


/-- A limit ordinal is an ordinal which is not zero and not a successor. -/
def is_limit (o : Ordinal) : Prop :=
  o ≠ 0 ∧ ∀ a _ : a < o, succ a < o

theorem not_zero_is_limit : ¬is_limit 0
| ⟨h, _⟩ => h rfl

theorem not_succ_is_limit o : ¬is_limit (succ o)
| ⟨_, h⟩ => lt_irreflₓ _ (h _ (lt_succ_self _))

theorem not_succ_of_is_limit {o} (h : is_limit o) : ¬∃ a, o = succ a
| ⟨a, e⟩ => not_succ_is_limit a (e ▸ h)

theorem succ_lt_of_is_limit {o} (h : is_limit o) {a} : succ a < o ↔ a < o :=
  ⟨lt_transₓ (lt_succ_self _), h.2 _⟩

theorem le_succ_of_is_limit {o} (h : is_limit o) {a} : o ≤ succ a ↔ o ≤ a :=
  le_iff_le_iff_lt_iff_lt.2$ succ_lt_of_is_limit h

theorem limit_le {o} (h : is_limit o) {a} : o ≤ a ↔ ∀ x _ : x < o, x ≤ a :=
  ⟨fun h x l => le_transₓ (le_of_ltₓ l) h,
    fun H => (le_succ_of_is_limit h).1$ le_of_not_ltₓ$ fun hn => not_lt_of_le (H _ hn) (lt_succ_self _)⟩

theorem lt_limit {o} (h : is_limit o) {a} : a < o ↔ ∃ (x : _)(_ : x < o), a < x :=
  by 
    simpa only [not_ball, not_leₓ] using not_congr (@limit_le _ h a)

@[simp]
theorem lift_is_limit o : is_limit (lift o) ↔ is_limit o :=
  and_congr
    (not_congr$
      by 
        simpa only [lift_zero] using @lift_inj o 0)
    ⟨fun H a h =>
        lift_lt.1$
          by 
            simpa only [lift_succ] using H _ (lift_lt.2 h),
      fun H a h =>
        let ⟨a', e⟩ := lift_down (le_of_ltₓ h)
        by 
          rw [←e, ←lift_succ, lift_lt] <;> rw [←e, lift_lt] at h <;> exact H a' h⟩

theorem is_limit.pos {o : Ordinal} (h : is_limit o) : 0 < o :=
  lt_of_le_of_neₓ (Ordinal.zero_le _) h.1.symm

theorem is_limit.one_lt {o : Ordinal} (h : is_limit o) : 1 < o :=
  by 
    simpa only [succ_zero] using h.2 _ h.pos

theorem is_limit.nat_lt {o : Ordinal} (h : is_limit o) : ∀ n : ℕ, (n : Ordinal) < o
| 0 => h.pos
| n+1 => h.2 _ (is_limit.nat_lt n)

theorem zero_or_succ_or_limit (o : Ordinal) : o = 0 ∨ (∃ a, o = succ a) ∨ is_limit o :=
  if o0 : o = 0 then Or.inl o0 else
    if h : ∃ a, o = succ a then Or.inr (Or.inl h) else Or.inr$ Or.inr ⟨o0, fun a => (succ_lt_of_not_succ h).2⟩

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_eliminator]
def limit_rec_on {C : Ordinal → Sort _} (o : Ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
  (H₃ : ∀ o, is_limit o → (∀ o' _ : o' < o, C o') → C o) : C o :=
  wf.fix
    (fun o IH =>
      if o0 : o = 0 then
        by 
          rw [o0] <;> exact H₁
      else
        if h : ∃ a, o = succ a then
          by 
            rw [←succ_pred_iff_is_succ.2 h] <;> exact H₂ _ (IH _$ pred_lt_iff_is_succ.2 h)
        else H₃ _ ⟨o0, fun a => (succ_lt_of_not_succ h).2⟩ IH)
    o

@[simp]
theorem limit_rec_on_zero {C} H₁ H₂ H₃ : @limit_rec_on C 0 H₁ H₂ H₃ = H₁ :=
  by 
    rw [limit_rec_on, WellFounded.fix_eq, dif_pos rfl] <;> rfl

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem limit_rec_on_succ
{C}
(o H₁ H₂ H₃) : «expr = »(@limit_rec_on C (succ o) H₁ H₂ H₃, H₂ o (@limit_rec_on C o H₁ H₂ H₃)) :=
begin
  have [ident h] [":", expr «expr∃ , »((a), «expr = »(succ o, succ a))] [":=", expr ⟨_, rfl⟩],
  rw ["[", expr limit_rec_on, ",", expr well_founded.fix_eq, ",", expr dif_neg (succ_ne_zero o), ",", expr dif_pos h, "]"] [],
  generalize [] [":"] [expr «expr = »(limit_rec_on._proof_2 (succ o) h, h₂)],
  generalize [] [":"] [expr «expr = »(limit_rec_on._proof_3 (succ o) h, h₃)],
  revert [ident h₂, ident h₃],
  generalize [ident e] [":"] [expr «expr = »(pred (succ o), o')],
  intros [],
  rw [expr pred_succ] ["at", ident e],
  subst [expr o'],
  refl
end

@[simp]
theorem limit_rec_on_limit {C} o H₁ H₂ H₃ h :
  @limit_rec_on C o H₁ H₂ H₃ = H₃ o h fun x h => @limit_rec_on C x H₁ H₂ H₃ :=
  by 
    rw [limit_rec_on, WellFounded.fix_eq, dif_neg h.1, dif_neg (not_succ_of_is_limit h)] <;> rfl

theorem has_succ_of_is_limit {α} {r : α → α → Prop} [wo : IsWellOrder α r] (h : (type r).IsLimit) (x : α) :
  ∃ y, r x y :=
  by 
    use enum r (typein r x).succ (h.2 _ (typein_lt_type r x))
    convert (enum_lt (typein_lt_type r x) _).mpr (lt_succ_self _)
    rw [enum_typein]

theorem type_subrel_lt (o : Ordinal.{u}) : type (Subrel (· < ·) { o':Ordinal | o' < o }) = Ordinal.lift.{u + 1} o :=
  by 
    refine' Quotientₓ.induction_on o _ 
    rintro ⟨α, r, wo⟩
    skip 
    apply Quotientₓ.sound 
    constructor 
    symm 
    refine' (RelIso.preimage Equiv.ulift r).trans (typein_iso r)

theorem mk_initial_seg (o : Ordinal.{u}) : # { o':Ordinal | o' < o } = Cardinal.lift.{u + 1} o.card :=
  by 
    rw [lift_card, ←type_subrel_lt, card_type]

/-! ### Normal ordinal functions -/


/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.  -/
def is_normal (f : Ordinal → Ordinal) : Prop :=
  (∀ o, f o < f (succ o)) ∧ ∀ o, is_limit o → ∀ a, f o ≤ a ↔ ∀ b _ : b < o, f b ≤ a

theorem is_normal.limit_le {f} (H : is_normal f) : ∀ {o}, is_limit o → ∀ {a}, f o ≤ a ↔ ∀ b _ : b < o, f b ≤ a :=
  H.2

theorem is_normal.limit_lt {f} (H : is_normal f) {o} (h : is_limit o) {a} : a < f o ↔ ∃ (b : _)(_ : b < o), a < f b :=
  not_iff_not.1$
    by 
      simpa only [exists_prop, not_exists, not_and, not_ltₓ] using H.2 _ h a

theorem is_normal.lt_iff {f} (H : is_normal f) {a b} : f a < f b ↔ a < b :=
  StrictMono.lt_iff_lt$
    fun a b =>
      limit_rec_on b (Not.elim (not_lt_of_le$ Ordinal.zero_le _))
        (fun b IH h => (lt_or_eq_of_leₓ (lt_succ.1 h)).elim (fun h => lt_transₓ (IH h) (H.1 _)) fun e => e ▸ H.1 _)
        fun b l IH h => lt_of_lt_of_leₓ (H.1 a) ((H.2 _ l _).1 (le_reflₓ _) _ (l.2 _ h))

theorem is_normal.le_iff {f} (H : is_normal f) {a b} : f a ≤ f b ↔ a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.lt_iff

theorem is_normal.inj {f} (H : is_normal f) {a b} : f a = f b ↔ a = b :=
  by 
    simp only [le_antisymm_iffₓ, H.le_iff]

theorem is_normal.le_self {f} (H : is_normal f) a : a ≤ f a :=
  limit_rec_on a (Ordinal.zero_le _) (fun a IH => succ_le.2$ lt_of_le_of_ltₓ IH (H.1 _))
    fun a l IH => (limit_le l).2$ fun b h => le_transₓ (IH b h)$ H.le_iff.2$ le_of_ltₓ h

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_normal.le_set
{f}
(H : is_normal f)
(p : ordinal → exprProp())
(p0 : «expr∃ , »((x), p x))
(S)
(H₂ : ∀ o, «expr ↔ »(«expr ≤ »(S, o), ∀ a, p a → «expr ≤ »(a, o)))
{o} : «expr ↔ »(«expr ≤ »(f S, o), ∀ a, p a → «expr ≤ »(f a, o)) :=
⟨λ h a pa, le_trans (H.le_iff.2 ((H₂ _).1 (le_refl _) _ pa)) h, λ h, begin
   revert [ident H₂],
   apply [expr limit_rec_on S],
   { intro [ident H₂],
     cases [expr p0] ["with", ident x, ident px],
     have [] [] [":=", expr ordinal.le_zero.1 ((H₂ _).1 (ordinal.zero_le _) _ px)],
     rw [expr this] ["at", ident px],
     exact [expr h _ px] },
   { intros [ident S, "_", ident H₂],
     rcases [expr not_ball.1 «expr $ »(mt (H₂ S).2, «expr $ »(not_le_of_lt, lt_succ_self _)), "with", "⟨", ident a, ",", ident h₁, ",", ident h₂, "⟩"],
     exact [expr le_trans «expr $ »(H.le_iff.2, «expr $ »(succ_le.2, not_le.1 h₂)) (h _ h₁)] },
   { intros [ident S, ident L, "_", ident H₂],
     apply [expr (H.2 _ L _).2],
     intros [ident a, ident h'],
     rcases [expr not_ball.1 (mt (H₂ a).2 (not_le.2 h')), "with", "⟨", ident b, ",", ident h₁, ",", ident h₂, "⟩"],
     exact [expr le_trans «expr $ »(H.le_iff.2, «expr $ »(le_of_lt, not_le.1 h₂)) (h _ h₁)] }
 end⟩

theorem is_normal.le_set' {f} (H : is_normal f) (p : α → Prop) (g : α → Ordinal) (p0 : ∃ x, p x) S
  (H₂ : ∀ o, S ≤ o ↔ ∀ a, p a → g a ≤ o) {o} : f S ≤ o ↔ ∀ a, p a → f (g a) ≤ o :=
  (H.le_set (fun x => ∃ y, p y ∧ x = g y)
        (let ⟨x, px⟩ := p0
        ⟨_, _, px, rfl⟩)
        _ fun o => (H₂ o).trans ⟨fun H a ⟨y, h1, h2⟩ => h2.symm ▸ H y h1, fun H a h1 => H (g a) ⟨a, h1, rfl⟩⟩).trans
    ⟨fun H a h => H (g a) ⟨a, h, rfl⟩, fun H a ⟨y, h1, h2⟩ => h2.symm ▸ H y h1⟩

theorem is_normal.refl : is_normal id :=
  ⟨fun x => lt_succ_self _, fun o l a => limit_le l⟩

theorem is_normal.trans {f g} (H₁ : is_normal f) (H₂ : is_normal g) : is_normal fun x => f (g x) :=
  ⟨fun x => H₁.lt_iff.2 (H₂.1 _), fun o l a => H₁.le_set' (· < o) g ⟨_, l.pos⟩ _ fun c => H₂.2 _ l _⟩

theorem is_normal.is_limit {f} (H : is_normal f) {o} (l : is_limit o) : is_limit (f o) :=
  ⟨ne_of_gtₓ$ lt_of_le_of_ltₓ (Ordinal.zero_le _)$ H.lt_iff.2 l.pos,
    fun a h =>
      let ⟨b, h₁, h₂⟩ := (H.limit_lt l).1 h 
      lt_of_le_of_ltₓ (succ_le.2 h₂) (H.lt_iff.2 h₁)⟩

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_le_of_limit
{a b c : ordinal.{u}}
(h : is_limit b) : «expr ↔ »(«expr ≤ »(«expr + »(a, b), c), ∀ b' «expr < » b, «expr ≤ »(«expr + »(a, b'), c)) :=
⟨λ
 h
 b'
 l, le_trans (add_le_add_left (le_of_lt l) _) h, λ
 H, «expr $ »(le_of_not_lt, induction_on a (λ
   α
   r
   _, «expr $ »(induction_on b, λ β s _ h H l, begin
      resetI,
      suffices [] [":", expr ∀ x : β, sum.lex r s (sum.inr x) (enum _ _ l)],
      { cases [expr enum _ _ l] ["with", ident x, ident x],
        { cases [expr this (enum s 0 h.pos)] [] },
        { exact [expr irrefl _ (this _)] } },
      intros [ident x],
      rw ["[", "<-", expr typein_lt_typein (sum.lex r s), ",", expr typein_enum, "]"] [],
      have [] [] [":=", expr H _ (h.2 _ (typein_lt_type s x))],
      rw ["[", expr add_succ, ",", expr succ_le, "]"] ["at", ident this],
      refine [expr lt_of_le_of_lt (type_le'.2 ⟨rel_embedding.of_monotone (λ a, _) (λ a b, _)⟩) this],
      { rcases [expr a, "with", "⟨", ident a, "|", ident b, ",", ident h, "⟩"],
        { exact [expr sum.inl a] },
        { exact [expr sum.inr ⟨b, by cases [expr h] []; assumption⟩] } },
      { rcases [expr a, "with", "⟨", ident a, "|", ident a, ",", ident h₁, "⟩"]; rcases [expr b, "with", "⟨", ident b, "|", ident b, ",", ident h₂, "⟩"]; cases [expr h₁] []; cases [expr h₂] []; rintro ["⟨", "⟩"]; constructor; assumption }
    end)) h H)⟩

theorem add_is_normal (a : Ordinal) : is_normal ((·+·) a) :=
  ⟨fun b => (add_lt_add_iff_left a).2 (lt_succ_self _), fun b l c => add_le_of_limit l⟩

theorem add_is_limit a {b} : is_limit b → is_limit (a+b) :=
  (add_is_normal a).IsLimit

/-! ### Subtraction on ordinals-/


/-- `a - b` is the unique ordinal satisfying
  `b + (a - b) = a` when `b ≤ a`. -/
def sub (a b : Ordinal.{u}) : Ordinal.{u} :=
  omin { o | a ≤ b+o } ⟨a, le_add_left _ _⟩

instance : Sub Ordinal :=
  ⟨sub⟩

theorem le_add_sub (a b : Ordinal) : a ≤ b+a - b :=
  omin_mem { o | a ≤ b+o } _

theorem sub_le {a b c : Ordinal} : a - b ≤ c ↔ a ≤ b+c :=
  ⟨fun h => le_transₓ (le_add_sub a b) (add_le_add_left h _), fun h => omin_le h⟩

theorem lt_sub {a b c : Ordinal} : a < b - c ↔ (c+a) < b :=
  lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a b : Ordinal) : (a+b) - a = b :=
  le_antisymmₓ (sub_le.2$ le_reflₓ _) ((add_le_add_iff_left a).1$ le_add_sub _ _)

theorem sub_eq_of_add_eq {a b c : Ordinal} (h : (a+b) = c) : c - a = b :=
  h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : Ordinal) : a - b ≤ a :=
  sub_le.2$ le_add_left _ _

protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b ≤ a) : (b+a - b) = a :=
  le_antisymmₓ
    (by 
      rcases zero_or_succ_or_limit (a - b) with (e | ⟨c, e⟩ | l)
      ·
        simp only [e, add_zeroₓ, h]
      ·
        rw [e, add_succ, succ_le, ←lt_sub, e]
        apply lt_succ_self
      ·
        exact (add_le_of_limit l).2 fun c l => le_of_ltₓ (lt_sub.1 l))
    (le_add_sub _ _)

@[simp]
theorem sub_zero (a : Ordinal) : a - 0 = a :=
  by 
    simpa only [zero_addₓ] using add_sub_cancel 0 a

@[simp]
theorem zero_sub (a : Ordinal) : 0 - a = 0 :=
  by 
    rw [←Ordinal.le_zero] <;> apply sub_le_self

@[simp]
theorem sub_self (a : Ordinal) : a - a = 0 :=
  by 
    simpa only [add_zeroₓ] using add_sub_cancel a 0

protected theorem sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h =>
      by 
        simpa only [h, add_zeroₓ] using le_add_sub a b,
    fun h =>
      by 
        rwa [←Ordinal.le_zero, sub_le, add_zeroₓ]⟩

theorem sub_sub (a b c : Ordinal) : a - b - c = a - b+c :=
  eq_of_forall_ge_iff$
    fun d =>
      by 
        rw [sub_le, sub_le, sub_le, add_assocₓ]

theorem add_sub_add_cancel (a b c : Ordinal) : ((a+b) - a+c) = b - c :=
  by 
    rw [←sub_sub, add_sub_cancel]

theorem sub_is_limit {a b} (l : is_limit a) (h : b < a) : is_limit (a - b) :=
  ⟨ne_of_gtₓ$
      lt_sub.2$
        by 
          rwa [add_zeroₓ],
    fun c h =>
      by 
        rw [lt_sub, add_succ] <;> exact l.2 _ (lt_sub.1 h)⟩

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem one_add_omega : «expr = »(«expr + »(1, omega.{u}), omega) :=
begin
  refine [expr le_antisymm _ (le_add_left _ _)],
  rw ["[", expr omega, ",", expr one_eq_lift_type_unit, ",", "<-", expr lift_add, ",", expr lift_le, ",", expr type_add, "]"] [],
  have [] [":", expr is_well_order unit empty_relation] [":=", expr by apply_instance],
  refine [expr ⟨rel_embedding.collapse (rel_embedding.of_monotone _ _)⟩],
  { apply [expr sum.rec],
    exact [expr λ _, 0],
    exact [expr nat.succ] },
  { intros [ident a, ident b],
    cases [expr a] []; cases [expr b] []; intro [ident H]; cases [expr H] ["with", "_", "_", ident H, "_", "_", ident H]; [cases [expr H] [], exact [expr nat.succ_pos _], exact [expr nat.succ_lt_succ H]] }
end

@[simp]
theorem one_add_of_omega_le {o} (h : omega ≤ o) : (1+o) = o :=
  by 
    rw [←Ordinal.add_sub_cancel_of_le h, ←add_assocₓ, one_add_omega]

/-! ### Multiplication of ordinals-/


/-- The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
`o₂ × o₁`. -/
instance : Monoidₓ Ordinal.{u} :=
  { mul :=
      fun a b =>
        Quotientₓ.liftOn₂ a b
            (fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ =>
              «expr⟦ ⟧»
                ⟨β × α, Prod.Lex s r,
                  by 
                    exact Prod.Lex.is_well_order⟩ :
            WellOrder → WellOrder → Ordinal)$
          fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.prodLexCongr g f⟩,
    one := 1,
    mul_assoc :=
      fun a b c =>
        Quotientₓ.induction_on₃ a b c$
          fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
            Eq.symm$
              Quotientₓ.sound
                ⟨⟨prod_assoc _ _ _,
                    fun a b =>
                      by 
                        rcases a with ⟨⟨a₁, a₂⟩, a₃⟩
                        rcases b with ⟨⟨b₁, b₂⟩, b₃⟩
                        simp [Prod.lex_def, and_or_distrib_left, or_assoc, and_assoc]⟩⟩,
    mul_one :=
      fun a =>
        induction_on a$
          fun α r _ =>
            Quotientₓ.sound
              ⟨⟨punit_prod _,
                  fun a b =>
                    by 
                      rcases a with ⟨⟨⟨⟩⟩, a⟩ <;>
                        rcases b with ⟨⟨⟨⟩⟩, b⟩ <;>
                          simp only [Prod.lex_def, EmptyRelation, false_orₓ] <;>
                            simp only [eq_self_iff_true, true_andₓ] <;> rfl⟩⟩,
    one_mul :=
      fun a =>
        induction_on a$
          fun α r _ =>
            Quotientₓ.sound
              ⟨⟨prod_punit _,
                  fun a b =>
                    by 
                      rcases a with ⟨a, ⟨⟨⟩⟩⟩ <;>
                        rcases b with ⟨b, ⟨⟨⟩⟩⟩ <;>
                          simp only [Prod.lex_def, EmptyRelation, and_falseₓ, or_falseₓ] <;> rfl⟩⟩ }

@[simp]
theorem type_mul {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s] :
  (type r*type s) = type (Prod.Lex s r) :=
  rfl

@[simp]
theorem lift_mul a b : lift (a*b) = lift a*lift b :=
  Quotientₓ.induction_on₂ a b$
    fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
      Quotientₓ.sound
        ⟨(RelIso.preimage Equiv.ulift _).trans
            (RelIso.prodLexCongr (RelIso.preimage Equiv.ulift _) (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]
theorem card_mul a b : card (a*b) = card a*card b :=
  Quotientₓ.induction_on₂ a b$ fun ⟨α, r, _⟩ ⟨β, s, _⟩ => mul_commₓ (mk β) (mk α)

@[simp]
theorem mul_zero (a : Ordinal) : (a*0) = 0 :=
  induction_on a$
    fun α _ _ =>
      by 
        exact type_eq_zero_of_empty

@[simp]
theorem zero_mul (a : Ordinal) : (0*a) = 0 :=
  induction_on a$
    fun α _ _ =>
      by 
        exact type_eq_zero_of_empty

theorem mul_addₓ (a b c : Ordinal) : (a*b+c) = (a*b)+a*c :=
  Quotientₓ.induction_on₃ a b c$
    fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Quotientₓ.sound
        ⟨⟨sum_prod_distrib _ _ _,
            by 
              rintro ⟨a₁ | a₁, a₂⟩ ⟨b₁ | b₁, b₂⟩ <;>
                simp only [Prod.lex_def, Sum.lex_inl_inl, Sum.Lex.sep, Sum.lex_inr_inl, Sum.lex_inr_inr,
                    sum_prod_distrib_apply_left, sum_prod_distrib_apply_right] <;>
                  simp only [Sum.inl.inj_iff, true_orₓ, false_andₓ, false_orₓ]⟩⟩

@[simp]
theorem mul_add_one (a b : Ordinal) : (a*b+1) = (a*b)+a :=
  by 
    simp only [mul_addₓ, mul_oneₓ]

@[simp]
theorem mul_succ (a b : Ordinal) : (a*succ b) = (a*b)+a :=
  mul_add_one _ _

theorem mul_le_mul_left {a b} (c : Ordinal) : a ≤ b → (c*a) ≤ c*b :=
  Quotientₓ.induction_on₃ a b c$
    fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ =>
      by 
        skip 
        refine' type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => (f a.1, a.2)) fun a b h => _⟩
        clear_ 
        cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
        ·
          exact Prod.Lex.left _ _ (f.to_rel_embedding.map_rel_iff.2 h')
        ·
          exact Prod.Lex.right _ h'

theorem mul_le_mul_right {a b} (c : Ordinal) : a ≤ b → (a*c) ≤ b*c :=
  Quotientₓ.induction_on₃ a b c$
    fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ =>
      by 
        skip 
        refine' type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => (a.1, f a.2)) fun a b h => _⟩
        cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
        ·
          exact Prod.Lex.left _ _ h'
        ·
          exact Prod.Lex.right _ (f.to_rel_embedding.map_rel_iff.2 h')

theorem mul_le_mul {a b c d : Ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) : (a*b) ≤ c*d :=
  le_transₓ (mul_le_mul_left _ h₂) (mul_le_mul_right _ h₁)

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem mul_le_of_limit_aux
{α β r s}
[is_well_order α r]
[is_well_order β s]
{c}
(h : is_limit (type s))
(H : ∀ b' «expr < » type s, «expr ≤ »(«expr * »(type r, b'), c))
(l : «expr < »(c, «expr * »(type r, type s))) : false :=
begin
  suffices [] [":", expr ∀ a b, prod.lex s r (b, a) (enum _ _ l)],
  { cases [expr enum _ _ l] ["with", ident b, ident a],
    exact [expr irrefl _ (this _ _)] },
  intros [ident a, ident b],
  rw ["[", "<-", expr typein_lt_typein (prod.lex s r), ",", expr typein_enum, "]"] [],
  have [] [] [":=", expr H _ (h.2 _ (typein_lt_type s b))],
  rw ["[", expr mul_succ, "]"] ["at", ident this],
  have [] [] [":=", expr lt_of_lt_of_le ((add_lt_add_iff_left _).2 (typein_lt_type _ a)) this],
  refine [expr lt_of_le_of_lt _ this],
  refine [expr type_le'.2 _],
  constructor,
  refine [expr rel_embedding.of_monotone (λ a, _) (λ a b, _)],
  { rcases [expr a, "with", "⟨", "⟨", ident b', ",", ident a', "⟩", ",", ident h, "⟩"],
    by_cases [expr e, ":", expr «expr = »(b, b')],
    { refine [expr sum.inr ⟨a', _⟩],
      subst [expr e],
      cases [expr h] ["with", "_", "_", "_", "_", ident h, "_", "_", "_", ident h],
      { exact [expr (irrefl _ h).elim] },
      { exact [expr h] } },
    { refine [expr sum.inl (⟨b', _⟩, a')],
      cases [expr h] ["with", "_", "_", "_", "_", ident h, "_", "_", "_", ident h],
      { exact [expr h] },
      { exact [expr (e rfl).elim] } } },
  { rcases [expr a, "with", "⟨", "⟨", ident b₁, ",", ident a₁, "⟩", ",", ident h₁, "⟩"],
    rcases [expr b, "with", "⟨", "⟨", ident b₂, ",", ident a₂, "⟩", ",", ident h₂, "⟩"],
    intro [ident h],
    by_cases [expr e₁, ":", expr «expr = »(b, b₁)]; by_cases [expr e₂, ":", expr «expr = »(b, b₂)],
    { substs [ident b₁, ident b₂],
      simpa [] [] ["only"] ["[", expr subrel_val, ",", expr prod.lex_def, ",", expr @irrefl _ s _ b, ",", expr true_and, ",", expr false_or, ",", expr eq_self_iff_true, ",", expr dif_pos, ",", expr sum.lex_inr_inr, "]"] [] ["using", expr h] },
    { subst [expr b₁],
      simp [] [] ["only"] ["[", expr subrel_val, ",", expr prod.lex_def, ",", expr e₂, ",", expr prod.lex_def, ",", expr dif_pos, ",", expr subrel_val, ",", expr eq_self_iff_true, ",", expr or_false, ",", expr dif_neg, ",", expr not_false_iff, ",", expr sum.lex_inr_inl, ",", expr false_and, "]"] [] ["at", ident h, "⊢"],
      cases [expr h₂] []; [exact [expr asymm h h₂_h], exact [expr e₂ rfl]] },
    { simp [] [] ["only"] ["[", expr e₂, ",", expr dif_pos, ",", expr eq_self_iff_true, ",", expr dif_neg e₁, ",", expr not_false_iff, ",", expr sum.lex.sep, "]"] [] [] },
    { simpa [] [] ["only"] ["[", expr dif_neg e₁, ",", expr dif_neg e₂, ",", expr prod.lex_def, ",", expr subrel_val, ",", expr subtype.mk_eq_mk, ",", expr sum.lex_inl_inl, "]"] [] ["using", expr h] } }
end

theorem mul_le_of_limit {a b c : Ordinal.{u}} (h : is_limit b) : (a*b) ≤ c ↔ ∀ b' _ : b' < b, (a*b') ≤ c :=
  ⟨fun h b' l => le_transₓ (mul_le_mul_left _ (le_of_ltₓ l)) h,
    fun H =>
      le_of_not_ltₓ$
        induction_on a
          (fun α r _ =>
            induction_on b$
              fun β s _ =>
                by 
                  exact mul_le_of_limit_aux)
          h H⟩

theorem mul_is_normal {a : Ordinal} (h : 0 < a) : is_normal ((·*·) a) :=
  ⟨fun b =>
      by 
        rw [mul_succ] <;> simpa only [add_zeroₓ] using (add_lt_add_iff_left (a*b)).2 h,
    fun b l c => mul_le_of_limit l⟩

theorem lt_mul_of_limit {a b c : Ordinal.{u}} (h : is_limit c) : (a < b*c) ↔ ∃ (c' : _)(_ : c' < c), a < b*c' :=
  by 
    simpa only [not_ball, not_leₓ] using not_congr (@mul_le_of_limit b c a h)

theorem mul_lt_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : ((a*b) < a*c) ↔ b < c :=
  (mul_is_normal a0).lt_iff

theorem mul_le_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : ((a*b) ≤ a*c) ↔ b ≤ c :=
  (mul_is_normal a0).le_iff

theorem mul_lt_mul_of_pos_left {a b c : Ordinal} (h : a < b) (c0 : 0 < c) : (c*a) < c*b :=
  (mul_lt_mul_iff_left c0).2 h

theorem mul_pos {a b : Ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a*b :=
  by 
    simpa only [mul_zero] using mul_lt_mul_of_pos_left h₂ h₁

theorem mul_ne_zero {a b : Ordinal} : a ≠ 0 → b ≠ 0 → (a*b) ≠ 0 :=
  by 
    simpa only [Ordinal.pos_iff_ne_zero] using mul_pos

theorem le_of_mul_le_mul_left {a b c : Ordinal} (h : (c*a) ≤ c*b) (h0 : 0 < c) : a ≤ b :=
  le_imp_le_of_lt_imp_ltₓ (fun h' => mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_injₓ {a b c : Ordinal} (a0 : 0 < a) : ((a*b) = a*c) ↔ b = c :=
  (mul_is_normal a0).inj

theorem mul_is_limit {a b : Ordinal} (a0 : 0 < a) : is_limit b → is_limit (a*b) :=
  (mul_is_normal a0).IsLimit

theorem mul_is_limit_left {a b : Ordinal} (l : is_limit a) (b0 : 0 < b) : is_limit (a*b) :=
  by 
    rcases zero_or_succ_or_limit b with (rfl | ⟨b, rfl⟩ | lb)
    ·
      exact (lt_irreflₓ _).elim b0
    ·
      rw [mul_succ]
      exact add_is_limit _ l
    ·
      exact mul_is_limit l.pos lb

/-! ### Division on ordinals -/


protected theorem div_aux (a b : Ordinal.{u}) (h : b ≠ 0) : Set.Nonempty { o | a < b*succ o } :=
  ⟨a,
    succ_le.1$
      by 
        simpa only [succ_zero, one_mulₓ] using mul_le_mul_right (succ a) (succ_le.2 (Ordinal.pos_iff_ne_zero.2 h))⟩

/-- `a / b` is the unique ordinal `o` satisfying
  `a = b * o + o'` with `o' < b`. -/
protected def div (a b : Ordinal.{u}) : Ordinal.{u} :=
  if h : b = 0 then 0 else omin { o | a < b*succ o } (Ordinal.div_aux a b h)

instance : Div Ordinal :=
  ⟨Ordinal.div⟩

@[simp]
theorem div_zero (a : Ordinal) : a / 0 = 0 :=
  dif_pos rfl

theorem div_def a {b : Ordinal} (h : b ≠ 0) : a / b = omin { o | a < b*succ o } (Ordinal.div_aux a b h) :=
  dif_neg h

theorem lt_mul_succ_div a {b : Ordinal} (h : b ≠ 0) : a < b*succ (a / b) :=
  by 
    rw [div_def a h] <;> exact omin_mem { o | a < b*succ o } _

theorem lt_mul_div_add a {b : Ordinal} (h : b ≠ 0) : a < (b*a / b)+b :=
  by 
    simpa only [mul_succ] using lt_mul_succ_div a h

theorem div_le {a b c : Ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b*succ c :=
  ⟨fun h => lt_of_lt_of_leₓ (lt_mul_succ_div a b0) (mul_le_mul_left _$ succ_le_succ.2 h),
    fun h =>
      by 
        rw [div_def a b0] <;> exact omin_le h⟩

theorem lt_div {a b c : Ordinal} (c0 : c ≠ 0) : a < b / c ↔ (c*succ a) ≤ b :=
  by 
    rw [←not_leₓ, div_le c0, not_ltₓ]

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_div
{a b c : ordinal}
(c0 : «expr ≠ »(c, 0)) : «expr ↔ »(«expr ≤ »(a, «expr / »(b, c)), «expr ≤ »(«expr * »(c, a), b)) :=
begin
  apply [expr limit_rec_on a],
  { simp [] [] ["only"] ["[", expr mul_zero, ",", expr ordinal.zero_le, "]"] [] [] },
  { intros [],
    rw ["[", expr succ_le, ",", expr lt_div c0, "]"] [] },
  { simp [] [] ["only"] ["[", expr mul_le_of_limit, ",", expr limit_le, ",", expr iff_self, ",", expr forall_true_iff, "]"] [] [] { contextual := tt } }
end

theorem div_lt {a b c : Ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b*c :=
  lt_iff_lt_of_le_iff_le$ le_div b0

theorem div_le_of_le_mul {a b c : Ordinal} (h : a ≤ b*c) : a / b ≤ c :=
  if b0 : b = 0 then
    by 
      simp only [b0, div_zero, Ordinal.zero_le]
  else (div_le b0).2$ lt_of_le_of_ltₓ h$ mul_lt_mul_of_pos_left (lt_succ_self _) (Ordinal.pos_iff_ne_zero.2 b0)

theorem mul_lt_of_lt_div {a b c : Ordinal} : a < b / c → (c*a) < b :=
  lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]
theorem zero_div (a : Ordinal) : 0 / a = 0 :=
  Ordinal.le_zero.1$ div_le_of_le_mul$ Ordinal.zero_le _

theorem mul_div_le (a b : Ordinal) : (b*a / b) ≤ a :=
  if b0 : b = 0 then
    by 
      simp only [b0, zero_mul, Ordinal.zero_le]
  else (le_div b0).1 (le_reflₓ _)

theorem mul_add_div a {b : Ordinal} (b0 : b ≠ 0) c : ((b*a)+c) / b = a+c / b :=
  by 
    apply le_antisymmₓ
    ·
      apply (div_le b0).2
      rw [mul_succ, mul_addₓ, add_assocₓ, add_lt_add_iff_left]
      apply lt_mul_div_add _ b0
    ·
      rw [le_div b0, mul_addₓ, add_le_add_iff_left]
      apply mul_div_le

theorem div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0 :=
  by 
    rw [←Ordinal.le_zero, div_le$ Ordinal.pos_iff_ne_zero.1$ lt_of_le_of_ltₓ (Ordinal.zero_le _) h]
    simpa only [succ_zero, mul_oneₓ] using h

@[simp]
theorem mul_div_cancel a {b : Ordinal} (b0 : b ≠ 0) : (b*a) / b = a :=
  by 
    simpa only [add_zeroₓ, zero_div] using mul_add_div a b0 0

@[simp]
theorem div_one (a : Ordinal) : a / 1 = a :=
  by 
    simpa only [one_mulₓ] using mul_div_cancel a Ordinal.one_ne_zero

@[simp]
theorem div_self {a : Ordinal} (h : a ≠ 0) : a / a = 1 :=
  by 
    simpa only [mul_oneₓ] using mul_div_cancel 1 h

theorem mul_sub (a b c : Ordinal) : (a*b - c) = (a*b) - a*c :=
  if a0 : a = 0 then
    by 
      simp only [a0, zero_mul, sub_self]
  else
    eq_of_forall_ge_iff$
      fun d =>
        by 
          rw [sub_le, ←le_div a0, sub_le, ←le_div a0, mul_add_div _ a0]

theorem is_limit_add_iff {a b} : is_limit (a+b) ↔ is_limit b ∨ b = 0 ∧ is_limit a :=
  by 
    split  <;> intro h
    ·
      byCases' h' : b = 0
      ·
        rw [h', add_zeroₓ] at h 
        right 
        exact ⟨h', h⟩
      left 
      rw [←add_sub_cancel a b]
      apply sub_is_limit h 
      suffices  : (a+0) < a+b 
      simpa only [add_zeroₓ]
      rwa [add_lt_add_iff_left, Ordinal.pos_iff_ne_zero]
    rcases h with (h | ⟨rfl, h⟩)
    exact add_is_limit a h 
    simpa only [add_zeroₓ]

theorem dvd_add_iff : ∀ {a b c : Ordinal}, a ∣ b → ((a ∣ b+c) ↔ a ∣ c)
| a, _, c, ⟨b, rfl⟩ =>
  ⟨fun ⟨d, e⟩ =>
      ⟨d - b,
        by 
          rw [mul_sub, ←e, add_sub_cancel]⟩,
    fun ⟨d, e⟩ =>
      by 
        rw [e, ←mul_addₓ]
        apply dvd_mul_right⟩

theorem dvd_add {a b c : Ordinal} (h₁ : a ∣ b) : a ∣ c → a ∣ b+c :=
  (dvd_add_iff h₁).2

theorem dvd_zero (a : Ordinal) : a ∣ 0 :=
  ⟨_, (mul_zero _).symm⟩

theorem zero_dvd {a : Ordinal} : 0 ∣ a ↔ a = 0 :=
  ⟨fun ⟨h, e⟩ =>
      by 
        simp only [e, zero_mul],
    fun e => e.symm ▸ dvd_zero _⟩

theorem one_dvd (a : Ordinal) : 1 ∣ a :=
  ⟨a, (one_mulₓ _).symm⟩

theorem div_mul_cancel : ∀ {a b : Ordinal}, a ≠ 0 → a ∣ b → (a*b / a) = b
| a, _, a0, ⟨b, rfl⟩ =>
  by 
    rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : Ordinal}, b ≠ 0 → a ∣ b → a ≤ b
| a, _, b0, ⟨b, rfl⟩ =>
  by 
    simpa only [mul_oneₓ] using
      mul_le_mul_left a
        (one_le_iff_ne_zero.2
          fun h : b = 0 =>
            by 
              simpa only [h, mul_zero] using b0)

theorem dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
  if a0 : a = 0 then
    by 
      subst a <;> exact (zero_dvd.1 h₁).symm
  else
    if b0 : b = 0 then
      by 
        subst b <;> exact zero_dvd.1 h₂
    else le_antisymmₓ (le_of_dvd b0 h₁) (le_of_dvd a0 h₂)

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance : Mod Ordinal :=
  ⟨fun a b => a - b*a / b⟩

theorem mod_def (a b : Ordinal) : a % b = a - b*a / b :=
  rfl

@[simp]
theorem mod_zero (a : Ordinal) : a % 0 = a :=
  by 
    simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a :=
  by 
    simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[simp]
theorem zero_mod (b : Ordinal) : 0 % b = 0 :=
  by 
    simp only [mod_def, zero_div, mul_zero, sub_self]

theorem div_add_mod (a b : Ordinal) : ((b*a / b)+a % b) = a :=
  Ordinal.add_sub_cancel_of_le$ mul_div_le _ _

theorem mod_lt a {b : Ordinal} (h : b ≠ 0) : a % b < b :=
  (add_lt_add_iff_left (b*a / b)).1$
    by 
      rw [div_add_mod] <;> exact lt_mul_div_add a h

@[simp]
theorem mod_self (a : Ordinal) : a % a = 0 :=
  if a0 : a = 0 then
    by 
      simp only [a0, zero_mod]
  else
    by 
      simp only [mod_def, div_self a0, mul_oneₓ, sub_self]

@[simp]
theorem mod_one (a : Ordinal) : a % 1 = 0 :=
  by 
    simp only [mod_def, div_one, one_mulₓ, sub_self]

/-! ### Supremum of a family of ordinals -/


/-- The supremum of a family of ordinals -/
def sup {ι} (f : ι → Ordinal) : Ordinal :=
  omin { c | ∀ i, f i ≤ c }
    ⟨(sup (Cardinal.succ ∘ card ∘ f)).ord,
      fun i => le_of_ltₓ$ Cardinal.lt_ord.2 (lt_of_lt_of_leₓ (Cardinal.lt_succ_self _) (le_sup _ _))⟩

theorem le_sup {ι} (f : ι → Ordinal) : ∀ i, f i ≤ sup f :=
  omin_mem { c | ∀ i, f i ≤ c } _

theorem sup_le {ι} {f : ι → Ordinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
  ⟨fun h i => le_transₓ (le_sup _ _) h, fun h => omin_le h⟩

theorem lt_sup {ι} {f : ι → Ordinal} {a} : a < sup f ↔ ∃ i, a < f i :=
  by 
    simpa only [not_forall, not_leₓ] using not_congr (@sup_le _ f a)

theorem is_normal.sup {f} (H : is_normal f) {ι} {g : ι → Ordinal} (h : Nonempty ι) : f (sup g) = sup (f ∘ g) :=
  eq_of_forall_ge_iff$
    fun a =>
      by 
        rw [sup_le, comp,
            H.le_set' (fun _ : ι => True) g
              (let ⟨i⟩ := h
              ⟨i, ⟨⟩⟩)] <;>
          intros  <;> simp only [sup_le, true_implies_iff]

theorem sup_ord {ι} (f : ι → Cardinal) : (sup fun i => (f i).ord) = (Cardinal.sup f).ord :=
  eq_of_forall_ge_iff$
    fun a =>
      by 
        simp only [sup_le, Cardinal.ord_le, Cardinal.sup_le]

theorem sup_succ {ι} (f : ι → Ordinal) : (sup fun i => succ (f i)) ≤ succ (sup f) :=
  by 
    rw [Ordinal.sup_le]
    intro i 
    rw [Ordinal.succ_le_succ]
    apply Ordinal.le_sup

theorem unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
  (h : type r ≤ sup.{u, u} (typein r ∘ f)) : Unbounded r (range f) :=
  by 
    apply (not_bounded_iff _).mp 
    rintro ⟨x, hx⟩
    apply not_lt_of_geₓ h 
    refine' lt_of_le_of_ltₓ _ (typein_lt_type r x)
    rw [sup_le]
    intro y 
    apply le_of_ltₓ 
    rw [typein_lt_typein]
    apply hx 
    apply mem_range_self

/-- The supremum of a family of ordinals indexed by the set
  of ordinals less than some `o : ordinal.{u}`.
  (This is not a special case of `sup` over the subtype,
  because `{a // a < o} : Type (u+1)` and `sup` only works over
  families in `Type u`.) -/
def bsup (o : Ordinal.{u}) : (∀ a _ : a < o, Ordinal.{max u v}) → Ordinal.{max u v} :=
  match o, o.out, o.out_eq with 
  | _, ⟨α, r, _⟩, rfl, f =>
    by 
      exact sup fun a => f (typein r a) (typein_lt_type _ _)

theorem bsup_le {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
  match o, o.out, o.out_eq, f with 
  | _, ⟨α, r, _⟩, rfl, f =>
    by 
      rw [bsup._match_1, sup_le] <;>
        exact
          ⟨fun H i h =>
              by 
                simpa only [typein_enum] using H (enum r i h),
            fun H b => H _ _⟩

theorem bsup_type (r : α → α → Prop) [IsWellOrder α r] f :
  bsup (type r) f = sup fun a => f (typein r a) (typein_lt_type _ _) :=
  eq_of_forall_ge_iff$
    fun o =>
      by 
        rw [bsup_le, sup_le] <;>
          exact
            ⟨fun H b => H _ _,
              fun H i h =>
                by 
                  simpa only [typein_enum] using H (enum r i h)⟩

theorem le_bsup {o} (f : ∀ a _ : a < o, Ordinal) i h : f i h ≤ bsup o f :=
  bsup_le.1 (le_reflₓ _) _ _

theorem lt_bsup {o : Ordinal} {f : ∀ a _ : a < o, Ordinal}
  (hf : ∀ {a a'} ha : a < o ha' : a' < o, a < a' → f a ha < f a' ha') (ho : o.is_limit) i h : f i h < bsup o f :=
  lt_of_lt_of_leₓ (hf _ _$ lt_succ_self i) (le_bsup f i.succ$ ho.2 _ h)

theorem bsup_id {o} (ho : is_limit o) : (bsup.{u, u} o fun x _ => x) = o :=
  by 
    apply le_antisymmₓ 
    rw [bsup_le]
    intro i 
    apply le_of_ltₓ 
    rw [←not_ltₓ]
    intro h 
    apply lt_irreflₓ (bsup.{u, u} o fun x _ => x)
    apply lt_of_le_of_ltₓ _ (lt_bsup _ ho _ h)
    rfl 
    intros 
    assumption

theorem is_normal.bsup {f} (H : is_normal f) {o : Ordinal} :
  ∀ g : ∀ a _ : a < o, Ordinal h : o ≠ 0, f (bsup o g) = bsup o fun a h => f (g a h) :=
  induction_on o$
    fun α r _ g h =>
      by 
        skip <;> rw [bsup_type, H.sup (type_ne_zero_iff_nonempty.1 h), bsup_type]

theorem is_normal.bsup_eq {f} (H : is_normal f) {o : Ordinal} (h : is_limit o) : (bsup.{u} o fun x _ => f x) = f o :=
  by 
    rw [←is_normal.bsup.{u, u} H (fun x _ => x) h.1, bsup_id h]

/-! ### Ordinal exponential -/


/-- The ordinal exponential, defined by transfinite recursion. -/
def power (a b : Ordinal) : Ordinal :=
  if a = 0 then 1 - b else limit_rec_on b 1 (fun _ IH => IH*a) fun b _ => bsup.{u, u} b

instance : Pow Ordinal Ordinal :=
  ⟨power⟩

local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

theorem zero_power' (a : Ordinal) : (0^a) = 1 - a :=
  by 
    simp only [pow, power, if_pos rfl]

@[simp]
theorem zero_power {a : Ordinal} (a0 : a ≠ 0) : (0^a) = 0 :=
  by 
    rwa [zero_power', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]
theorem power_zero (a : Ordinal) : (a^0) = 1 :=
  by 
    byCases' a = 0 <;> [simp only [pow, power, if_pos h, sub_zero], simp only [pow, power, if_neg h, limit_rec_on_zero]]

@[simp]
theorem power_succ (a b : Ordinal) : (a^succ b) = (a^b)*a :=
  if h : a = 0 then
    by 
      subst a <;> simp only [zero_power (succ_ne_zero _), mul_zero]
  else
    by 
      simp only [pow, power, limit_rec_on_succ, if_neg h]

theorem power_limit {a b : Ordinal} (a0 : a ≠ 0) (h : is_limit b) : (a^b) = bsup.{u, u} b fun c _ => a^c :=
  by 
    simp only [pow, power, if_neg a0] <;> rw [limit_rec_on_limit _ _ _ _ h] <;> rfl

theorem power_le_of_limit {a b c : Ordinal} (a0 : a ≠ 0) (h : is_limit b) : (a^b) ≤ c ↔ ∀ b' _ : b' < b, (a^b') ≤ c :=
  by 
    rw [power_limit a0 h, bsup_le]

theorem lt_power_of_limit {a b c : Ordinal} (b0 : b ≠ 0) (h : is_limit c) :
  a < (b^c) ↔ ∃ (c' : _)(_ : c' < c), a < (b^c') :=
  by 
    rw [←not_iff_not, not_exists] <;> simp only [not_ltₓ, power_le_of_limit b0 h, exists_prop, not_and]

@[simp]
theorem power_one (a : Ordinal) : (a^1) = a :=
  by 
    rw [←succ_zero, power_succ] <;> simp only [power_zero, one_mulₓ]

@[simp]
theorem one_power (a : Ordinal) : (1^a) = 1 :=
  by 
    apply limit_rec_on a
    ·
      simp only [power_zero]
    ·
      intro _ ih 
      simp only [power_succ, ih, mul_oneₓ]
    refine' fun b l IH => eq_of_forall_ge_iff fun c => _ 
    rw [power_le_of_limit Ordinal.one_ne_zero l]
    exact
      ⟨fun H =>
          by 
            simpa only [power_zero] using H 0 l.pos,
        fun H b' h =>
          by 
            rwa [IH _ h]⟩

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem power_pos {a : ordinal} (b) (a0 : «expr < »(0, a)) : «expr < »(0, «expr ^ »(a, b)) :=
begin
  have [ident h0] [":", expr «expr < »(0, «expr ^ »(a, 0))] [],
  { simp [] [] ["only"] ["[", expr power_zero, ",", expr zero_lt_one, "]"] [] [] },
  apply [expr limit_rec_on b],
  { exact [expr h0] },
  { intros [ident b, ident IH],
    rw ["[", expr power_succ, "]"] [],
    exact [expr mul_pos IH a0] },
  { exact [expr λ b l _, (lt_power_of_limit (ordinal.pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩] }
end

theorem power_ne_zero {a : Ordinal} b (a0 : a ≠ 0) : (a^b) ≠ 0 :=
  Ordinal.pos_iff_ne_zero.1$ power_pos b$ Ordinal.pos_iff_ne_zero.2 a0

theorem power_is_normal {a : Ordinal} (h : 1 < a) : is_normal ((·^·) a) :=
  have a0 : 0 < a := lt_transₓ zero_lt_one h
  ⟨fun b =>
      by 
        simpa only [mul_oneₓ, power_succ] using (mul_lt_mul_iff_left (power_pos b a0)).2 h,
    fun b l c => power_le_of_limit (ne_of_gtₓ a0) l⟩

theorem power_lt_power_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) < (a^c) ↔ b < c :=
  (power_is_normal a1).lt_iff

theorem power_le_power_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) ≤ (a^c) ↔ b ≤ c :=
  (power_is_normal a1).le_iff

theorem power_right_inj {a b c : Ordinal} (a1 : 1 < a) : (a^b) = (a^c) ↔ b = c :=
  (power_is_normal a1).inj

theorem power_is_limit {a b : Ordinal} (a1 : 1 < a) : is_limit b → is_limit (a^b) :=
  (power_is_normal a1).IsLimit

theorem power_is_limit_left {a b : Ordinal} (l : is_limit a) (hb : b ≠ 0) : is_limit (a^b) :=
  by 
    rcases zero_or_succ_or_limit b with (e | ⟨b, rfl⟩ | l')
    ·
      exact absurd e hb
    ·
      rw [power_succ]
      exact mul_is_limit (power_pos _ l.pos) l
    ·
      exact power_is_limit l.one_lt l'

theorem power_le_power_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : (a^b) ≤ (a^c) :=
  by 
    cases' lt_or_eq_of_leₓ (one_le_iff_pos.2 h₁) with h₁ h₁
    ·
      exact (power_le_power_iff_right h₁).2 h₂
    ·
      subst a 
      simp only [one_power]

theorem power_le_power_left {a b : Ordinal} c (ab : a ≤ b) : (a^c) ≤ (b^c) :=
  by 
    byCases' a0 : a = 0
    ·
      subst a 
      byCases' c0 : c = 0
      ·
        subst c 
        simp only [power_zero]
      ·
        simp only [zero_power c0, Ordinal.zero_le]
    ·
      apply limit_rec_on c
      ·
        simp only [power_zero]
      ·
        intro c IH 
        simpa only [power_succ] using mul_le_mul IH ab
      ·
        exact
          fun c l IH =>
            (power_le_of_limit a0 l).2
              fun b' h =>
                le_transₓ (IH _ h)
                  (power_le_power_right (lt_of_lt_of_leₓ (Ordinal.pos_iff_ne_zero.2 a0) ab) (le_of_ltₓ h))

theorem le_power_self {a : Ordinal} b (a1 : 1 < a) : b ≤ (a^b) :=
  (power_is_normal a1).le_self _

theorem power_lt_power_left_of_succ {a b c : Ordinal} (ab : a < b) : (a^succ c) < (b^succ c) :=
  by 
    rw [power_succ, power_succ] <;>
      exact
        lt_of_le_of_ltₓ (mul_le_mul_right _$ power_le_power_left _$ le_of_ltₓ ab)
          (mul_lt_mul_of_pos_left ab (power_pos _ (lt_of_le_of_ltₓ (Ordinal.zero_le _) ab)))

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem power_add
(a b c : ordinal) : «expr = »(«expr ^ »(a, «expr + »(b, c)), «expr * »(«expr ^ »(a, b), «expr ^ »(a, c))) :=
begin
  by_cases [expr a0, ":", expr «expr = »(a, 0)],
  { subst [expr a],
    by_cases [expr c0, ":", expr «expr = »(c, 0)],
    { simp [] [] ["only"] ["[", expr c0, ",", expr add_zero, ",", expr power_zero, ",", expr mul_one, "]"] [] [] },
    have [] [":", expr «expr ≠ »(«expr + »(b, c), 0)] [":=", expr ne_of_gt (lt_of_lt_of_le (ordinal.pos_iff_ne_zero.2 c0) (le_add_left _ _))],
    simp [] [] ["only"] ["[", expr zero_power c0, ",", expr zero_power this, ",", expr mul_zero, "]"] [] [] },
  cases [expr eq_or_lt_of_le (one_le_iff_ne_zero.2 a0)] ["with", ident a1, ident a1],
  { subst [expr a1],
    simp [] [] ["only"] ["[", expr one_power, ",", expr mul_one, "]"] [] [] },
  apply [expr limit_rec_on c],
  { simp [] [] ["only"] ["[", expr add_zero, ",", expr power_zero, ",", expr mul_one, "]"] [] [] },
  { intros [ident c, ident IH],
    rw ["[", expr add_succ, ",", expr power_succ, ",", expr IH, ",", expr power_succ, ",", expr mul_assoc, "]"] [] },
  { intros [ident c, ident l, ident IH],
    refine [expr eq_of_forall_ge_iff (λ d, (((power_is_normal a1).trans (add_is_normal b)).limit_le l).trans _)],
    simp [] [] ["only"] ["[", expr IH, "]"] [] [] { contextual := tt },
    exact [expr ((«expr $ »(mul_is_normal, power_pos b (ordinal.pos_iff_ne_zero.2 a0)).trans (power_is_normal a1)).limit_le l).symm] }
end

theorem power_dvd_power a {b c : Ordinal} (h : b ≤ c) : (a^b) ∣ (a^c) :=
  by 
    rw [←Ordinal.add_sub_cancel_of_le h, power_add]
    apply dvd_mul_right

theorem power_dvd_power_iff {a b c : Ordinal} (a1 : 1 < a) : (a^b) ∣ (a^c) ↔ b ≤ c :=
  ⟨fun h =>
      le_of_not_ltₓ$
        fun hn =>
          not_le_of_lt ((power_lt_power_iff_right a1).2 hn)$
            le_of_dvd (power_ne_zero _$ one_le_iff_ne_zero.1$ le_of_ltₓ a1) h,
    power_dvd_power _⟩

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem power_mul (a b c : ordinal) : «expr = »(«expr ^ »(a, «expr * »(b, c)), «expr ^ »(«expr ^ »(a, b), c)) :=
begin
  by_cases [expr b0, ":", expr «expr = »(b, 0)],
  { simp [] [] ["only"] ["[", expr b0, ",", expr zero_mul, ",", expr power_zero, ",", expr one_power, "]"] [] [] },
  by_cases [expr a0, ":", expr «expr = »(a, 0)],
  { subst [expr a],
    by_cases [expr c0, ":", expr «expr = »(c, 0)],
    { simp [] [] ["only"] ["[", expr c0, ",", expr mul_zero, ",", expr power_zero, "]"] [] [] },
    simp [] [] ["only"] ["[", expr zero_power b0, ",", expr zero_power c0, ",", expr zero_power (mul_ne_zero b0 c0), "]"] [] [] },
  cases [expr eq_or_lt_of_le (one_le_iff_ne_zero.2 a0)] ["with", ident a1, ident a1],
  { subst [expr a1],
    simp [] [] ["only"] ["[", expr one_power, "]"] [] [] },
  apply [expr limit_rec_on c],
  { simp [] [] ["only"] ["[", expr mul_zero, ",", expr power_zero, "]"] [] [] },
  { intros [ident c, ident IH],
    rw ["[", expr mul_succ, ",", expr power_add, ",", expr IH, ",", expr power_succ, "]"] [] },
  { intros [ident c, ident l, ident IH],
    refine [expr eq_of_forall_ge_iff (λ
      d, (((power_is_normal a1).trans (mul_is_normal (ordinal.pos_iff_ne_zero.2 b0))).limit_le l).trans _)],
    simp [] [] ["only"] ["[", expr IH, "]"] [] [] { contextual := tt },
    exact [expr (power_le_of_limit (power_ne_zero _ a0) l).symm] }
end

/-! ### Ordinal logarithm -/


/-- The ordinal logarithm is the solution `u` to the equation
  `x = b ^ u * v + w` where `v < b` and `w < b`. -/
def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if h : 1 < b then pred$ omin { o | x < (b^o) } ⟨succ x, succ_le.1 (le_power_self _ h)⟩ else 0

@[simp]
theorem log_not_one_lt {b : Ordinal} (b1 : ¬1 < b) (x : Ordinal) : log b x = 0 :=
  by 
    simp only [log, dif_neg b1]

theorem log_def {b : Ordinal} (b1 : 1 < b) (x : Ordinal) :
  log b x = pred (omin { o | x < (b^o) } (log._proof_1 b x b1)) :=
  by 
    simp only [log, dif_pos b1]

@[simp]
theorem log_zero (b : Ordinal) : log b 0 = 0 :=
  if b1 : 1 < b then
    by 
      rw [log_def b1, ←Ordinal.le_zero, pred_le] <;>
        apply omin_le <;> change 0 < (b^succ 0) <;> rw [succ_zero, power_one] <;> exact lt_transₓ zero_lt_one b1
  else
    by 
      simp only [log_not_one_lt b1]

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem succ_log_def
{b x : ordinal}
(b1 : «expr < »(1, b))
(x0 : «expr < »(0, x)) : «expr = »(succ (log b x), omin {o | «expr < »(x, «expr ^ »(b, o))} (log._proof_1 b x b1)) :=
begin
  let [ident t] [] [":=", expr omin {o | «expr < »(x, «expr ^ »(b, o))} (log._proof_1 b x b1)],
  have [] [":", expr «expr < »(x, «expr ^ »(b, t))] [":=", expr omin_mem {o | «expr < »(x, «expr ^ »(b, o))} _],
  rcases [expr zero_or_succ_or_limit t, "with", ident h, "|", ident h, "|", ident h],
  { refine [expr (not_lt_of_le (one_le_iff_pos.2 x0) _).elim],
    simpa [] [] ["only"] ["[", expr h, ",", expr power_zero, "]"] [] [] },
  { rw ["[", expr show «expr = »(log b x, pred t), from log_def b1 x, ",", expr succ_pred_iff_is_succ.2 h, "]"] [] },
  { rcases [expr (lt_power_of_limit «expr $ »(ne_of_gt, lt_trans zero_lt_one b1) h).1 this, "with", "⟨", ident a, ",", ident h₁, ",", ident h₂, "⟩"],
    exact [expr (not_le_of_lt h₁).elim (le_omin.1 (le_refl t) a h₂)] }
end

theorem lt_power_succ_log {b : Ordinal} (b1 : 1 < b) (x : Ordinal) : x < (b^succ (log b x)) :=
  by 
    cases' lt_or_eq_of_leₓ (Ordinal.zero_le x) with x0 x0
    ·
      rw [succ_log_def b1 x0]
      exact omin_mem { o | x < (b^o) } _
    ·
      subst x 
      apply power_pos _ (lt_transₓ zero_lt_one b1)

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem power_log_le (b) {x : ordinal} (x0 : «expr < »(0, x)) : «expr ≤ »(«expr ^ »(b, log b x), x) :=
begin
  by_cases [expr b0, ":", expr «expr = »(b, 0)],
  { rw ["[", expr b0, ",", expr zero_power', "]"] [],
    refine [expr le_trans (sub_le_self _ _) (one_le_iff_pos.2 x0)] },
  cases [expr lt_or_eq_of_le (one_le_iff_ne_zero.2 b0)] ["with", ident b1, ident b1],
  { refine [expr le_of_not_lt (λ h, not_le_of_lt (lt_succ_self (log b x)) _)],
    have [] [] [":=", expr @omin_le {o | «expr < »(x, «expr ^ »(b, o))} _ _ h],
    rwa ["<-", expr succ_log_def b1 x0] ["at", ident this] },
  { rw ["[", "<-", expr b1, ",", expr one_power, "]"] [],
    exact [expr one_le_iff_pos.2 x0] }
end

theorem le_log {b x c : Ordinal} (b1 : 1 < b) (x0 : 0 < x) : c ≤ log b x ↔ (b^c) ≤ x :=
  ⟨fun h => le_transₓ ((power_le_power_iff_right b1).2 h) (power_log_le b x0),
    fun h =>
      le_of_not_ltₓ$
        fun hn => not_le_of_lt (lt_power_succ_log b1 x)$ le_transₓ ((power_le_power_iff_right b1).2 (succ_le.2 hn)) h⟩

theorem log_lt {b x c : Ordinal} (b1 : 1 < b) (x0 : 0 < x) : log b x < c ↔ x < (b^c) :=
  lt_iff_lt_of_le_iff_le (le_log b1 x0)

theorem log_le_log b {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y :=
  if x0 : x = 0 then
    by 
      simp only [x0, log_zero, Ordinal.zero_le]
  else
    have x0 : 0 < x := Ordinal.pos_iff_ne_zero.2 x0 
    if b1 : 1 < b then (le_log b1 (lt_of_lt_of_leₓ x0 xy)).2$ le_transₓ (power_log_le _ x0) xy else
      by 
        simp only [log_not_one_lt b1, Ordinal.zero_le]

theorem log_le_self (b x : Ordinal) : log b x ≤ x :=
  if x0 : x = 0 then
    by 
      simp only [x0, log_zero, Ordinal.zero_le]
  else
    if b1 : 1 < b then le_transₓ (le_power_self _ b1) (power_log_le b (Ordinal.pos_iff_ne_zero.2 x0)) else
      by 
        simp only [log_not_one_lt b1, Ordinal.zero_le]

/-! ### The Cantor normal form -/


theorem CNF_aux {b o : Ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) : o % (b^log b o) < o :=
  lt_of_lt_of_leₓ (mod_lt _$ power_ne_zero _ b0) (power_log_le _$ Ordinal.pos_iff_ne_zero.2 o0)

/-- Proving properties of ordinals by induction over their Cantor normal form. -/
@[elab_as_eliminator]
noncomputable def CNF_rec {b : Ordinal} (b0 : b ≠ 0) {C : Ordinal → Sort _} (H0 : C 0)
  (H : ∀ o, o ≠ 0 → o % (b^log b o) < o → C (o % (b^log b o)) → C o) : ∀ o, C o
| o =>
  if o0 : o = 0 then
    by 
      rw [o0] <;> exact H0
  else
    have  := CNF_aux b0 o0 
    H o o0 this (CNF_rec (o % (b^log b o)))

@[simp]
theorem CNF_rec_zero {b} b0 {C H0 H} : @CNF_rec b b0 C H0 H 0 = H0 :=
  by 
    rw [CNF_rec, dif_pos rfl] <;> rfl

@[simp]
theorem CNF_rec_ne_zero {b} b0 {C H0 H o} o0 :
  @CNF_rec b b0 C H0 H o = H o o0 (CNF_aux b0 o0) (@CNF_rec b b0 C H0 H _) :=
  by 
    rw [CNF_rec, dif_neg o0]

/-- The Cantor normal form of an ordinal is the list of coefficients
  in the base-`b` expansion of `o`.

    CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)] -/
noncomputable def CNF (b := omega) (o : Ordinal) : List (Ordinal × Ordinal) :=
  if b0 : b = 0 then [] else CNF_rec b0 [] (fun o o0 h IH => (log b o, o / (b^log b o)) :: IH) o

@[simp]
theorem zero_CNF o : CNF 0 o = [] :=
  dif_pos rfl

@[simp]
theorem CNF_zero b : CNF b 0 = [] :=
  if b0 : b = 0 then dif_pos b0 else (dif_neg b0).trans$ CNF_rec_zero _

theorem CNF_ne_zero {b o : Ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
  CNF b o = (log b o, o / (b^log b o)) :: CNF b (o % (b^log b o)) :=
  by 
    unfold CNF <;> rw [dif_neg b0, dif_neg b0, CNF_rec_ne_zero b0 o0]

theorem one_CNF {o : Ordinal} (o0 : o ≠ 0) : CNF 1 o = [(0, o)] :=
  by 
    rw [CNF_ne_zero Ordinal.one_ne_zero o0, log_not_one_lt (lt_irreflₓ _), power_zero, mod_one, CNF_zero, div_one]

theorem CNF_foldr {b : Ordinal} (b0 : b ≠ 0) o : (CNF b o).foldr (fun p r => ((b^p.1)*p.2)+r) 0 = o :=
  CNF_rec b0
    (by 
      rw [CNF_zero] <;> rfl)
    (fun o o0 h IH =>
      by 
        rw [CNF_ne_zero b0 o0, List.foldr_cons, IH, div_add_mod])
    o

theorem CNF_pairwise_aux (b := omega) o :
  (∀ p _ : p ∈ CNF b o, Prod.fst p ≤ log b o) ∧ (CNF b o).Pairwise fun p q => q.1 < p.1 :=
  by 
    byCases' b0 : b = 0
    ·
      simp only [b0, zero_CNF, List.Pairwise.nil, and_trueₓ]
      exact fun _ => False.elim 
    cases' lt_or_eq_of_leₓ (one_le_iff_ne_zero.2 b0) with b1 b1
    ·
      refine' CNF_rec b0 _ _ o
      ·
        simp only [CNF_zero, List.Pairwise.nil, and_trueₓ]
        exact fun _ => False.elim 
      intro o o0 H IH 
      cases' IH with IH₁ IH₂ 
      simp only [CNF_ne_zero b0 o0, List.forall_mem_consₓ, List.pairwise_consₓ, IH₂, and_trueₓ]
      refine' ⟨⟨le_reflₓ _, fun p m => _⟩, fun p m => _⟩
      ·
        exact le_transₓ (IH₁ p m) (log_le_log _$ le_of_ltₓ H)
      ·
        refine' lt_of_le_of_ltₓ (IH₁ p m) ((log_lt b1 _).2 _)
        ·
          rw [Ordinal.pos_iff_ne_zero]
          intro e 
          rw [e] at m 
          simpa only [CNF_zero] using m
        ·
          exact mod_lt _ (power_ne_zero _ b0)
    ·
      byCases' o0 : o = 0
      ·
        simp only [o0, CNF_zero, List.Pairwise.nil, and_trueₓ]
        exact fun _ => False.elim 
      rw [←b1, one_CNF o0]
      simp only [List.mem_singleton, log_not_one_lt (lt_irreflₓ _), forall_eq, le_reflₓ, true_andₓ,
        List.pairwise_singleton]

theorem CNF_pairwise (b := omega) o : (CNF b o).Pairwise fun p q => Prod.fst q < p.1 :=
  (CNF_pairwise_aux _ _).2

theorem CNF_fst_le_log (b := omega) o : ∀ p _ : p ∈ CNF b o, Prod.fst p ≤ log b o :=
  (CNF_pairwise_aux _ _).1

theorem CNF_fst_le (b := omega) o p (_ : p ∈ CNF b o) : Prod.fst p ≤ o :=
  le_transₓ (CNF_fst_le_log _ _ p H) (log_le_self _ _)

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem CNF_snd_lt {b : ordinal} (b1 : «expr < »(1, b)) (o) : ∀ p «expr ∈ » CNF b o, «expr < »(prod.snd p, b) :=
begin
  have [ident b0] [] [":=", expr ne_of_gt (lt_trans zero_lt_one b1)],
  refine [expr CNF_rec b0 (λ _, by rw ["[", expr CNF_zero, "]"] []; exact [expr false.elim]) _ o],
  intros [ident o, ident o0, ident H, ident IH],
  simp [] [] ["only"] ["[", expr CNF_ne_zero b0 o0, ",", expr list.mem_cons_iff, ",", expr forall_eq_or_imp, ",", expr iff_true_intro IH, ",", expr and_true, "]"] [] [],
  rw ["[", expr div_lt (power_ne_zero _ b0), ",", "<-", expr power_succ, "]"] [],
  exact [expr lt_power_succ_log b1 _]
end

theorem CNF_sorted (b := omega) o : ((CNF b o).map Prod.fst).Sorted (· > ·) :=
  by 
    rw [List.Sorted, List.pairwise_map] <;> exact CNF_pairwise b o

/-! ### Casting naturals into ordinals, compatibility with operations -/


@[simp]
theorem nat_cast_mul {m n : ℕ} : ((m*n : ℕ) : Ordinal) = m*n :=
  by 
    induction' n with n IH <;> [simp only [Nat.cast_zero, Nat.mul_zero, mul_zero],
      rw [Nat.mul_succ, Nat.cast_add, IH, Nat.cast_succ, mul_add_one]]

@[simp]
theorem nat_cast_power {m n : ℕ} : ((pow m n : ℕ) : Ordinal) = (m^n) :=
  by 
    induction' n with n IH <;> [simp only [pow_zeroₓ, Nat.cast_zero, power_zero, Nat.cast_one],
      rw [pow_succ'ₓ, nat_cast_mul, IH, Nat.cast_succ, ←succ_eq_add_one, power_succ]]

@[simp]
theorem nat_cast_le {m n : ℕ} : (m : Ordinal) ≤ n ↔ m ≤ n :=
  by 
    rw [←Cardinal.ord_nat, ←Cardinal.ord_nat, Cardinal.ord_le_ord, Cardinal.nat_cast_le]

@[simp]
theorem nat_cast_lt {m n : ℕ} : (m : Ordinal) < n ↔ m < n :=
  by 
    simp only [lt_iff_le_not_leₓ, nat_cast_le]

@[simp]
theorem nat_cast_inj {m n : ℕ} : (m : Ordinal) = n ↔ m = n :=
  by 
    simp only [le_antisymm_iffₓ, nat_cast_le]

@[simp]
theorem nat_cast_eq_zero {n : ℕ} : (n : Ordinal) = 0 ↔ n = 0 :=
  @nat_cast_inj n 0

theorem nat_cast_ne_zero {n : ℕ} : (n : Ordinal) ≠ 0 ↔ n ≠ 0 :=
  not_congr nat_cast_eq_zero

@[simp]
theorem nat_cast_pos {n : ℕ} : (0 : Ordinal) < n ↔ 0 < n :=
  @nat_cast_lt 0 n

@[simp]
theorem nat_cast_sub {m n : ℕ} : ((m - n : ℕ) : Ordinal) = m - n :=
  (_root_.le_total m n).elim
    (fun h =>
      by 
        rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (nat_cast_le.2 h)] <;> rfl)
    fun h =>
      (add_left_cancelₓ n).1$
        by 
          rw [←Nat.cast_add, add_tsub_cancel_of_le h, Ordinal.add_sub_cancel_of_le (nat_cast_le.2 h)]

@[simp]
theorem nat_cast_div {m n : ℕ} : ((m / n : ℕ) : Ordinal) = m / n :=
  if n0 : n = 0 then
    by 
      simp only [n0, Nat.div_zeroₓ, Nat.cast_zero, div_zero]
  else
    have n0' := nat_cast_ne_zero.2 n0 
    le_antisymmₓ
      (by 
        rw [le_div n0', ←nat_cast_mul, nat_cast_le, mul_commₓ] <;> apply Nat.div_mul_le_selfₓ)
      (by 
        rw [div_le n0', succ, ←Nat.cast_succ, ←nat_cast_mul, nat_cast_lt, mul_commₓ,
            ←Nat.div_lt_iff_lt_mulₓ _ _ (Nat.pos_of_ne_zeroₓ n0)] <;>
          apply Nat.lt_succ_selfₓ)

@[simp]
theorem nat_cast_mod {m n : ℕ} : ((m % n : ℕ) : Ordinal) = m % n :=
  by 
    rw [←add_left_cancelₓ (n*m / n), div_add_mod, ←nat_cast_div, ←nat_cast_mul, ←Nat.cast_add, Nat.div_add_mod]

@[simp]
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o :=
  ⟨fun h =>
      by 
        rwa [←Cardinal.ord_le, Cardinal.ord_nat] at h,
    fun h => card_nat n ▸ card_le_card h⟩

@[simp]
theorem nat_lt_card {o} {n : ℕ} : (n : Cardinal) < card o ↔ (n : Ordinal) < o :=
  by 
    rw [←succ_le, ←Cardinal.succ_le, ←Cardinal.nat_succ, nat_le_card] <;> rfl

@[simp]
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card

@[simp]
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]
theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n :=
  by 
    simp only [le_antisymm_iffₓ, card_le_nat, nat_le_card]

@[simp]
theorem type_fin (n : ℕ) : @type (Finₓ n) (· < ·) _ = n :=
  by 
    rw [←card_eq_nat, card_type, mk_fin]

@[simp]
theorem lift_nat_cast (n : ℕ) : lift n = n :=
  by 
    induction' n with n ih <;> [simp only [Nat.cast_zero, lift_zero], simp only [Nat.cast_succ, lift_add, ih, lift_one]]

theorem lift_type_fin (n : ℕ) : lift (@type (Finₓ n) (· < ·) _) = n :=
  by 
    simp only [type_fin, lift_nat_cast]

theorem type_fintype (r : α → α → Prop) [IsWellOrder α r] [Fintype α] : type r = Fintype.card α :=
  by 
    rw [←card_eq_nat, card_type, mk_fintype]

end Ordinal

/-! ### Properties of `omega` -/


namespace Cardinal

open Ordinal

@[simp]
theorem ord_omega : ord.{u} omega = Ordinal.omega :=
  le_antisymmₓ (ord_le.2$ le_reflₓ _)$
    le_of_forall_lt$
      fun o h =>
        by 
          rcases Ordinal.lt_lift_iff.1 h with ⟨o, rfl, h'⟩
          rw [lt_ord, ←lift_card, ←lift_omega.{0, u}, lift_lt, ←typein_enum (· < ·) h']
          exact lt_omega_iff_fintype.2 ⟨Set.fintypeLtNat _⟩

@[simp]
theorem add_one_of_omega_le {c} (h : omega ≤ c) : (c+1) = c :=
  by 
    rw [add_commₓ, ←card_ord c, ←card_one, ←card_add, one_add_of_omega_le] <;> rwa [←ord_omega, ord_le_ord]

end Cardinal

namespace Ordinal

theorem lt_omega {o : Ordinal.{u}} : o < omega ↔ ∃ n : ℕ, o = n :=
  by 
    rw [←Cardinal.ord_omega, Cardinal.lt_ord, lt_omega] <;> simp only [card_eq_nat]

theorem nat_lt_omega (n : ℕ) : (n : Ordinal) < omega :=
  lt_omega.2 ⟨_, rfl⟩

theorem omega_pos : 0 < omega :=
  nat_lt_omega 0

theorem omega_ne_zero : omega ≠ 0 :=
  ne_of_gtₓ omega_pos

theorem one_lt_omega : 1 < omega :=
  by 
    simpa only [Nat.cast_one] using nat_lt_omega 1

theorem omega_is_limit : is_limit omega :=
  ⟨omega_ne_zero,
    fun o h =>
      let ⟨n, e⟩ := lt_omega.1 h 
      by 
        rw [e] <;> exact nat_lt_omega (n+1)⟩

theorem omega_le {o : Ordinal.{u}} : omega ≤ o ↔ ∀ n : ℕ, (n : Ordinal) ≤ o :=
  ⟨fun h n => le_transₓ (le_of_ltₓ (nat_lt_omega _)) h,
    fun H =>
      le_of_forall_lt$
        fun a h =>
          let ⟨n, e⟩ := lt_omega.1 h 
          by 
            rw [e, ←succ_le] <;> exact H (n+1)⟩

theorem nat_lt_limit {o} (h : is_limit o) : ∀ n : ℕ, (n : Ordinal) < o
| 0 => lt_of_le_of_neₓ (Ordinal.zero_le o) h.1.symm
| n+1 => h.2 _ (nat_lt_limit n)

theorem omega_le_of_is_limit {o} (h : is_limit o) : omega ≤ o :=
  omega_le.2$ fun n => le_of_ltₓ$ nat_lt_limit h n

theorem add_omega {a : Ordinal} (h : a < omega) : (a+omega) = omega :=
  by 
    rcases lt_omega.1 h with ⟨n, rfl⟩
    clear h 
    induction' n with n IH
    ·
      rw [Nat.cast_zero, zero_addₓ]
    ·
      rw [Nat.cast_succ, add_assocₓ, one_add_of_omega_le (le_reflₓ _), IH]

theorem add_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : (a+b) < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with 
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ =>
    by 
      rw [←Nat.cast_add] <;> apply nat_lt_omega

theorem mul_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : (a*b) < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with 
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ =>
    by 
      rw [←nat_cast_mul] <;> apply nat_lt_omega

theorem is_limit_iff_omega_dvd {a : Ordinal} : is_limit a ↔ a ≠ 0 ∧ omega ∣ a :=
  by 
    refine' ⟨fun l => ⟨l.1, ⟨a / omega, le_antisymmₓ _ (mul_div_le _ _)⟩⟩, fun h => _⟩
    ·
      refine' (limit_le l).2 fun x hx => le_of_ltₓ _ 
      rw [←div_lt omega_ne_zero, ←succ_le, le_div omega_ne_zero, mul_succ, add_le_of_limit omega_is_limit]
      intro b hb 
      rcases lt_omega.1 hb with ⟨n, rfl⟩
      exact le_transₓ (add_le_add_right (mul_div_le _ _) _) (le_of_ltₓ$ lt_sub.1$ nat_lt_limit (sub_is_limit l hx) _)
    ·
      rcases h with ⟨a0, b, rfl⟩
      refine' mul_is_limit_left omega_is_limit (Ordinal.pos_iff_ne_zero.2$ mt _ a0)
      intro e 
      simp only [e, mul_zero]

local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

theorem power_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : (a^b) < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with 
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ =>
    by 
      rw [←nat_cast_power] <;> apply nat_lt_omega

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_omega_power
{a b : ordinal}
(h : «expr < »(a, «expr ^ »(omega, b))) : «expr = »(«expr + »(a, «expr ^ »(omega, b)), «expr ^ »(omega, b)) :=
begin
  refine [expr le_antisymm _ (le_add_left _ _)],
  revert [ident h],
  apply [expr limit_rec_on b],
  { intro [ident h],
    rw ["[", expr power_zero, ",", "<-", expr succ_zero, ",", expr lt_succ, ",", expr ordinal.le_zero, "]"] ["at", ident h],
    rw ["[", expr h, ",", expr zero_add, "]"] [] },
  { intros [ident b, "_", ident h],
    rw ["[", expr power_succ, "]"] ["at", ident h],
    rcases [expr (lt_mul_of_limit omega_is_limit).1 h, "with", "⟨", ident x, ",", ident xo, ",", ident ax, "⟩"],
    refine [expr le_trans (add_le_add_right (le_of_lt ax) _) _],
    rw ["[", expr power_succ, ",", "<-", expr mul_add, ",", expr add_omega xo, "]"] [] },
  { intros [ident b, ident l, ident IH, ident h],
    rcases [expr (lt_power_of_limit omega_ne_zero l).1 h, "with", "⟨", ident x, ",", ident xb, ",", ident ax, "⟩"],
    refine [expr (((add_is_normal a).trans (power_is_normal one_lt_omega)).limit_le l).2 (λ y yb, _)],
    let [ident z] [] [":=", expr max x y],
    have [] [] [":=", expr IH z (max_lt xb yb) «expr $ »(lt_of_lt_of_le ax, power_le_power_right omega_pos (le_max_left _ _))],
    exact [expr le_trans (add_le_add_left (power_le_power_right omega_pos (le_max_right _ _)) _) (le_trans this «expr $ »(power_le_power_right omega_pos, «expr $ »(le_of_lt, max_lt xb yb)))] }
end

theorem add_lt_omega_power {a b c : Ordinal} (h₁ : a < (omega^c)) (h₂ : b < (omega^c)) : (a+b) < (omega^c) :=
  by 
    rwa [←add_omega_power h₁, add_lt_add_iff_left]

theorem add_absorp {a b c : Ordinal} (h₁ : a < (omega^b)) (h₂ : (omega^b) ≤ c) : (a+c) = c :=
  by 
    rw [←Ordinal.add_sub_cancel_of_le h₂, ←add_assocₓ, add_omega_power h₁]

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_absorp_iff
{o : ordinal}
(o0 : «expr < »(0, o)) : «expr ↔ »(∀
 a «expr < » o, «expr = »(«expr + »(a, o), o), «expr∃ , »((a), «expr = »(o, «expr ^ »(omega, a)))) :=
⟨λ
 H, ⟨log omega o, begin
    refine [expr «expr $ »((lt_or_eq_of_le (power_log_le _ o0)).resolve_left, λ h, _).symm],
    have [] [] [":=", expr H _ h],
    have [] [] [":=", expr lt_power_succ_log one_lt_omega o],
    rw ["[", expr power_succ, ",", expr lt_mul_of_limit omega_is_limit, "]"] ["at", ident this],
    rcases [expr this, "with", "⟨", ident a, ",", ident ao, ",", ident h', "⟩"],
    rcases [expr lt_omega.1 ao, "with", "⟨", ident n, ",", ident rfl, "⟩"],
    clear [ident ao],
    revert [ident h'],
    apply [expr not_lt_of_le],
    suffices [ident e] [":", expr «expr = »(«expr + »(«expr * »(«expr ^ »(omega, log omega o), «expr↑ »(n)), o), o)],
    { simpa [] [] ["only"] ["[", expr e, "]"] [] ["using", expr le_add_right «expr * »(«expr ^ »(omega, log omega o), «expr↑ »(n)) o] },
    induction [expr n] [] ["with", ident n, ident IH] [],
    { simp [] [] ["only"] ["[", expr nat.cast_zero, ",", expr mul_zero, ",", expr zero_add, "]"] [] [] },
    simp [] [] ["only"] ["[", expr nat.cast_succ, ",", expr mul_add_one, ",", expr add_assoc, ",", expr this, ",", expr IH, "]"] [] []
  end⟩, λ ⟨b, e⟩, «expr ▸ »(e.symm, λ a, add_omega_power)⟩

theorem add_mul_limit_aux {a b c : Ordinal} (ba : (b+a) = a) (l : is_limit c)
  (IH : ∀ c' _ : c' < c, ((a+b)*succ c') = (a*succ c')+b) : ((a+b)*c) = a*c :=
  le_antisymmₓ
    ((mul_le_of_limit l).2$
      fun c' h =>
        by 
          apply le_transₓ (mul_le_mul_left _ (le_of_ltₓ$ lt_succ_self _))
          rw [IH _ h]
          apply le_transₓ (add_le_add_left _ _)
          ·
            rw [←mul_succ]
            exact mul_le_mul_left _ (succ_le.2$ l.2 _ h)
          ·
            rw [←ba]
            exact le_add_right _ _)
    (mul_le_mul_right _ (le_add_right _ _))

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_mul_succ
{a b : ordinal}
(c)
(ba : «expr = »(«expr + »(b, a), a)) : «expr = »(«expr * »(«expr + »(a, b), succ c), «expr + »(«expr * »(a, succ c), b)) :=
begin
  apply [expr limit_rec_on c],
  { simp [] [] ["only"] ["[", expr succ_zero, ",", expr mul_one, "]"] [] [] },
  { intros [ident c, ident IH],
    rw ["[", expr mul_succ, ",", expr IH, ",", "<-", expr add_assoc, ",", expr add_assoc _ b, ",", expr ba, ",", "<-", expr mul_succ, "]"] [] },
  { intros [ident c, ident l, ident IH],
    have [] [] [":=", expr add_mul_limit_aux ba l IH],
    rw ["[", expr mul_succ, ",", expr add_mul_limit_aux ba l IH, ",", expr mul_succ, ",", expr add_assoc, "]"] [] }
end

theorem add_mul_limit {a b c : Ordinal} (ba : (b+a) = a) (l : is_limit c) : ((a+b)*c) = a*c :=
  add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

theorem mul_omega {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : (a*omega) = omega :=
  le_antisymmₓ ((mul_le_of_limit omega_is_limit).2$ fun b hb => le_of_ltₓ (mul_lt_omega ha hb))
    (by 
      simpa only [one_mulₓ] using mul_le_mul_right omega (one_le_iff_pos.2 a0))

theorem mul_lt_omega_power {a b c : Ordinal} (c0 : 0 < c) (ha : a < (omega^c)) (hb : b < omega) : (a*b) < (omega^c) :=
  if b0 : b = 0 then
    by 
      simp only [b0, mul_zero, power_pos _ omega_pos]
  else
    by 
      rcases zero_or_succ_or_limit c with (rfl | ⟨c, rfl⟩ | l)
      ·
        exact (lt_irreflₓ _).elim c0
      ·
        rw [power_succ] at ha 
        rcases((mul_is_normal$ power_pos _ omega_pos).limit_lt omega_is_limit).1 ha with ⟨n, hn, an⟩
        refine' lt_of_le_of_ltₓ (mul_le_mul_right _ (le_of_ltₓ an)) _ 
        rw [power_succ, mul_assocₓ, mul_lt_mul_iff_left (power_pos _ omega_pos)]
        exact mul_lt_omega hn hb
      ·
        rcases((power_is_normal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩
        refine' lt_of_le_of_ltₓ (mul_le_mul (le_of_ltₓ ax) (le_of_ltₓ hb)) _ 
        rw [←power_succ, power_lt_power_iff_right one_lt_omega]
        exact l.2 _ hx

theorem mul_omega_dvd {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → (a*b) = b
| _, ⟨b, rfl⟩ =>
  by 
    rw [←mul_assocₓ, mul_omega a0 ha]

theorem mul_omega_power_power {a b : Ordinal} (a0 : 0 < a) (h : a < (omega^omega^b)) :
  (a*omega^omega^b) = (omega^omega^b) :=
  by 
    byCases' b0 : b = 0
    ·
      rw [b0, power_zero, power_one] at h⊢
      exact mul_omega a0 h 
    refine'
      le_antisymmₓ _
        (by 
          simpa only [one_mulₓ] using mul_le_mul_right (omega^omega^b) (one_le_iff_pos.2 a0))
    rcases(lt_power_of_limit omega_ne_zero (power_is_limit_left omega_is_limit b0)).1 h with ⟨x, xb, ax⟩
    refine' le_transₓ (mul_le_mul_right _ (le_of_ltₓ ax)) _ 
    rw [←power_add, add_omega_power xb]

theorem power_omega {a : Ordinal} (a1 : 1 < a) (h : a < omega) : (a^omega) = omega :=
  le_antisymmₓ
    ((power_le_of_limit (one_le_iff_ne_zero.1$ le_of_ltₓ a1) omega_is_limit).2
      fun b hb => le_of_ltₓ (power_lt_omega h hb))
    (le_power_self _ a1)

/-! ### Fixed points of normal functions -/


/-- The next fixed point function, the least fixed point of the
  normal function `f` above `a`. -/
def nfp (f : Ordinal → Ordinal) (a : Ordinal) :=
  sup fun n : ℕ => (f^[n]) a

theorem iterate_le_nfp f a n : (f^[n]) a ≤ nfp f a :=
  le_sup _ n

theorem le_nfp_self f a : a ≤ nfp f a :=
  iterate_le_nfp f a 0

theorem is_normal.lt_nfp {f} (H : is_normal f) {a b} : f b < nfp f a ↔ b < nfp f a :=
  lt_sup.trans$
    Iff.trans
      (by 
        exact
          ⟨fun ⟨n, h⟩ => ⟨n, lt_of_le_of_ltₓ (H.le_self _) h⟩,
            fun ⟨n, h⟩ =>
              ⟨n+1,
                by 
                  rw [iterate_succ'] <;> exact H.lt_iff.2 h⟩⟩)
      lt_sup.symm

theorem is_normal.nfp_le {f} (H : is_normal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.lt_nfp

theorem is_normal.nfp_le_fp {f} (H : is_normal f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  sup_le.2$
    fun i =>
      by 
        induction' i with i IH generalizing a
        ·
          exact ab 
        exact IH (le_transₓ (H.le_iff.2 ab) h)

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_normal.nfp_fp {f} (H : is_normal f) (a) : «expr = »(f (nfp f a), nfp f a) :=
begin
  refine [expr le_antisymm _ (H.le_self _)],
  cases [expr le_or_lt (f a) a] ["with", ident aa, ident aa],
  { rwa [expr le_antisymm (H.nfp_le_fp (le_refl _) aa) (le_nfp_self _ _)] [] },
  rcases [expr zero_or_succ_or_limit (nfp f a), "with", ident e, "|", "⟨", ident b, ",", ident e, "⟩", "|", ident l],
  { refine [expr @le_trans _ _ _ (f a) _ (H.le_iff.2 _) (iterate_le_nfp f a 1)],
    simp [] [] ["only"] ["[", expr e, ",", expr ordinal.zero_le, "]"] [] [] },
  { have [] [":", expr «expr < »(f b, nfp f a)] [":=", expr H.lt_nfp.2 (by simp [] [] ["only"] ["[", expr e, ",", expr lt_succ_self, "]"] [] [])],
    rw ["[", expr e, ",", expr lt_succ, "]"] ["at", ident this],
    have [ident ab] [":", expr «expr ≤ »(a, b)] [],
    { rw ["[", "<-", expr lt_succ, ",", "<-", expr e, "]"] [],
      exact [expr lt_of_lt_of_le aa (iterate_le_nfp f a 1)] },
    refine [expr le_trans (H.le_iff.2 (H.nfp_le_fp ab this)) (le_trans this (le_of_lt _))],
    simp [] [] ["only"] ["[", expr e, ",", expr lt_succ_self, "]"] [] [] },
  { exact [expr (H.2 _ l _).2 (λ b h, le_of_lt (H.lt_nfp.2 h))] }
end

theorem is_normal.le_nfp {f} (H : is_normal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨le_transₓ (H.le_self _),
    fun h =>
      by 
        simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : Ordinal → Ordinal} {a} (h : f a = a) : nfp f a = a :=
  le_antisymmₓ
    (sup_le.mpr$
      fun i =>
        by 
          rw [iterate_fixed h])
    (le_nfp_self f a)

/-- The derivative of a normal function `f` is
  the sequence of fixed points of `f`. -/
def deriv (f : Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limit_rec_on o (nfp f 0) (fun a IH => nfp f (succ IH)) fun a l => bsup.{u, u} a

@[simp]
theorem deriv_zero f : deriv f 0 = nfp f 0 :=
  limit_rec_on_zero _ _ _

@[simp]
theorem deriv_succ f o : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  limit_rec_on_succ _ _ _ _

theorem deriv_limit f {o} : is_limit o → deriv f o = bsup.{u, u} o fun a _ => deriv f a :=
  limit_rec_on_limit _ _ _ _

theorem deriv_is_normal f : is_normal (deriv f) :=
  ⟨fun o =>
      by 
        rw [deriv_succ, ←succ_le] <;> apply le_nfp_self,
    fun o l a =>
      by 
        rw [deriv_limit _ l, bsup_le]⟩

-- error in SetTheory.OrdinalArithmetic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_normal.deriv_fp {f} (H : is_normal f) (o) : «expr = »(f (deriv.{u} f o), deriv f o) :=
begin
  apply [expr limit_rec_on o],
  { rw ["[", expr deriv_zero, ",", expr H.nfp_fp, "]"] [] },
  { intros [ident o, ident ih],
    rw ["[", expr deriv_succ, ",", expr H.nfp_fp, "]"] [] },
  intros [ident o, ident l, ident IH],
  rw ["[", expr deriv_limit _ l, ",", expr is_normal.bsup.{u, u, u} H _ l.1, "]"] [],
  refine [expr eq_of_forall_ge_iff (λ c, _)],
  simp [] [] ["only"] ["[", expr bsup_le, ",", expr IH, "]"] [] [] { contextual := tt }
end

theorem is_normal.fp_iff_deriv {f} (H : is_normal f) {a} : f a ≤ a ↔ ∃ o, a = deriv f o :=
  ⟨fun ha =>
      by 
        suffices  : ∀ o _ : a ≤ deriv f o, ∃ o, a = deriv f o 
        exact this a ((deriv_is_normal _).le_self _)
        intro o 
        apply limit_rec_on o
        ·
          intro h₁ 
          refine' ⟨0, le_antisymmₓ h₁ _⟩
          rw [deriv_zero]
          exact H.nfp_le_fp (Ordinal.zero_le _) ha
        ·
          intro o IH h₁ 
          cases le_or_ltₓ a (deriv f o)
          ·
            exact IH h 
          refine' ⟨succ o, le_antisymmₓ h₁ _⟩
          rw [deriv_succ]
          exact H.nfp_le_fp (succ_le.2 h) ha
        ·
          intro o l IH h₁ 
          cases eq_or_lt_of_le h₁
          ·
            exact ⟨_, h⟩
          rw [deriv_limit _ l, ←not_leₓ, bsup_le, not_ball] at h 
          exact
            let ⟨o', h, hl⟩ := h 
            IH o' h (le_of_not_leₓ hl),
    fun ⟨o, e⟩ => e.symm ▸ le_of_eqₓ (H.deriv_fp _)⟩

end Ordinal

