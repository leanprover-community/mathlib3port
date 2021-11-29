import Mathbin.Data.Set.Basic

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `well_founded.min`, `well_founded.sup`, and `well_founded.succ`.
-/


variable{α : Type _}

namespace WellFounded

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : WellFounded r) (s : Set α) :
  s.nonempty → ∃ (a : _)(_ : a ∈ s), ∀ x (_ : x ∈ s), ¬r x a
| ⟨a, ha⟩ =>
  (Acc.recOnₓ (H.apply a)$ fun x _ IH => not_imp_not.1$ fun hne hx => hne$ ⟨x, hx, fun y hy hyx => hne$ IH y hyx hy⟩) ha

/-- A minimal element of a nonempty set in a well-founded order -/
noncomputable def min {α} {r : α → α → Prop} (H : WellFounded r) (p : Set α) (h : p.nonempty) : α :=
  Classical.some (H.has_min p h)

theorem min_mem {α} {r : α → α → Prop} (H : WellFounded r) (p : Set α) (h : p.nonempty) : H.min p h ∈ p :=
  let ⟨h, _⟩ := Classical.some_spec (H.has_min p h)
  h

theorem not_lt_min {α} {r : α → α → Prop} (H : WellFounded r) (p : Set α) (h : p.nonempty) {x} (xp : x ∈ p) :
  ¬r x (H.min p h) :=
  let ⟨_, h'⟩ := Classical.some_spec (H.has_min p h)
  h' _ xp

theorem well_founded_iff_has_min {α} {r : α → α → Prop} :
  WellFounded r ↔ ∀ (p : Set α), p.nonempty → ∃ (m : _)(_ : m ∈ p), ∀ x (_ : x ∈ p), ¬r x m :=
  by 
    classical 
    split 
    ·
      exact has_min
    ·
      set counterexamples := { x:α | ¬Acc r x }
      intro exists_max 
      fconstructor 
      intro x 
      byContra hx 
      obtain ⟨m, m_mem, hm⟩ := exists_max counterexamples ⟨x, hx⟩
      refine' m_mem (Acc.intro _ fun y y_gt_m => _)
      byContra hy 
      exact hm y hy y_gt_m

theorem eq_iff_not_lt_of_le {α} [PartialOrderₓ α] {x y : α} : x ≤ y → y = x ↔ ¬x < y :=
  by 
    split 
    ·
      intro xle nge 
      cases le_not_le_of_ltₓ nge 
      rw [xle left] at nge 
      exact lt_irreflₓ x nge
    ·
      intro ngt xle 
      contrapose! ngt 
      exact lt_of_le_of_neₓ xle (Ne.symm ngt)

theorem well_founded_iff_has_max' [PartialOrderₓ α] :
  WellFounded (· > · : α → α → Prop) ↔
    ∀ (p : Set α), p.nonempty → ∃ (m : _)(_ : m ∈ p), ∀ x (_ : x ∈ p), m ≤ x → x = m :=
  by 
    simp only [eq_iff_not_lt_of_le, well_founded_iff_has_min]

theorem well_founded_iff_has_min' [PartialOrderₓ α] :
  WellFounded (LT.lt : α → α → Prop) ↔
    ∀ (p : Set α), p.nonempty → ∃ (m : _)(_ : m ∈ p), ∀ x (_ : x ∈ p), x ≤ m → x = m :=
  @well_founded_iff_has_max' (OrderDual α) _

open Set

/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {α} {r : α → α → Prop} (wf : WellFounded r) (s : Set α) (h : Bounded r s) : α :=
  wf.min { x | ∀ a (_ : a ∈ s), r a x } h

protected theorem lt_sup {α} {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x} (hx : x ∈ s) :
  r x (wf.sup s h) :=
  min_mem wf { x | ∀ a (_ : a ∈ s), r a x } h x hx

section 

open_locale Classical

/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ {α} {r : α → α → Prop} (wf : WellFounded r) (x : α) : α :=
  if h : ∃ y, r x y then wf.min { y | r x y } h else x

protected theorem lt_succ {α} {r : α → α → Prop} (wf : WellFounded r) {x : α} (h : ∃ y, r x y) : r x (wf.succ x) :=
  by 
    rw [WellFounded.succ, dif_pos h]
    apply min_mem

end 

-- error in Order.WellFounded: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem lt_succ_iff
{α}
{r : α → α → exprProp()}
[wo : is_well_order α r]
{x : α}
(h : «expr∃ , »((y), r x y))
(y : α) : «expr ↔ »(r y (wo.wf.succ x), «expr ∨ »(r y x, «expr = »(y, x))) :=
begin
  split,
  { intro [ident h'],
    have [] [":", expr «expr¬ »(r x y)] [],
    { intro [ident hy],
      rw ["[", expr well_founded.succ, ",", expr dif_pos, "]"] ["at", ident h'],
      exact [expr wo.wf.not_lt_min _ h hy h'] },
    rcases [expr trichotomous_of r x y, "with", ident hy, "|", ident hy, "|", ident hy],
    exfalso,
    exact [expr this hy],
    right,
    exact [expr hy.symm],
    left,
    exact [expr hy] },
  rintro ["(", ident hy, "|", ident rfl, ")"],
  exact [expr trans hy (wo.wf.lt_succ h)],
  exact [expr wo.wf.lt_succ h]
end

end WellFounded

namespace Function

variable{β : Type _}(f : α → β)

section LT

variable[LT β](h : WellFounded (· < · : β → β → Prop))

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `function.not_lt_argmin`. -/
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wfₓ f h) Set.Univ Set.univ_nonempty

theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f h) :=
  WellFounded.not_lt_min (InvImage.wfₓ f h) _ _ (Set.mem_univ a)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`function.not_lt_argmin_on`. -/
noncomputable def argmin_on (s : Set α) (hs : s.nonempty) : α :=
  WellFounded.min (InvImage.wfₓ f h) s hs

@[simp]
theorem argmin_on_mem (s : Set α) (hs : s.nonempty) : argmin_on f h s hs ∈ s :=
  WellFounded.min_mem _ _ _

@[simp]
theorem not_lt_argmin_on (s : Set α) {a : α} (ha : a ∈ s) (hs : s.nonempty := Set.nonempty_of_mem ha) :
  ¬f a < f (argmin_on f h s hs) :=
  WellFounded.not_lt_min (InvImage.wfₓ f h) s hs ha

end LT

section LinearOrderₓ

variable[LinearOrderₓ β](h : WellFounded (· < · : β → β → Prop))

@[simp]
theorem argmin_le (a : α) [Nonempty α] : f (argmin f h) ≤ f a :=
  not_ltₓ.mp$ not_lt_argmin f h a

@[simp]
theorem argmin_on_le (s : Set α) {a : α} (ha : a ∈ s) (hs : s.nonempty := Set.nonempty_of_mem ha) :
  f (argmin_on f h s hs) ≤ f a :=
  not_ltₓ.mp$ not_lt_argmin_on f h s ha hs

end LinearOrderₓ

end Function

