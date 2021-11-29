import Mathbin.Data.Set.Intervals.OrdConnected

/-!
# Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset s
has a least upper bound and a greatest lower bound, denoted below by Sup s and Inf s.
Typical examples are real, nat, int with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates bdd_above and bdd_below to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of Sup and Inf
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix Inf and Sup in the statements by c, giving cInf and cSup. For instance,
Inf_le is a statement in complete lattices ensuring Inf s ≤ x, while cInf_le is the same
statement in conditionally complete lattices with an additional assumption that s is
bounded below.
-/


open Set

variable{α β : Type _}{ι : Sort _}

section 

/-!
Extension of Sup and Inf from a preorder `α` to `with_top α` and `with_bot α`
-/


open_locale Classical

noncomputable instance  {α : Type _} [Preorderₓ α] [HasSupₓ α] : HasSupₓ (WithTop α) :=
  ⟨fun S => if ⊤ ∈ S then ⊤ else if BddAbove (coeₓ ⁻¹' S : Set α) then «expr↑ » (Sup (coeₓ ⁻¹' S : Set α)) else ⊤⟩

noncomputable instance  {α : Type _} [HasInfₓ α] : HasInfₓ (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} then ⊤ else «expr↑ » (Inf (coeₓ ⁻¹' S : Set α))⟩

noncomputable instance  {α : Type _} [HasSupₓ α] : HasSupₓ (WithBot α) :=
  ⟨(@WithTop.hasInf (OrderDual α) _).inf⟩

noncomputable instance  {α : Type _} [Preorderₓ α] [HasInfₓ α] : HasInfₓ (WithBot α) :=
  ⟨(@WithTop.hasSup (OrderDual α) _ _).sup⟩

@[simp]
theorem WithTop.cInf_empty {α : Type _} [HasInfₓ α] : Inf (∅ : Set (WithTop α)) = ⊤ :=
  if_pos$ Set.empty_subset _

@[simp]
theorem WithBot.cSup_empty {α : Type _} [HasSupₓ α] : Sup (∅ : Set (WithBot α)) = ⊥ :=
  if_pos$ Set.empty_subset _

end 

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLattice(α : Type _) extends Lattice α, HasSupₓ α, HasInfₓ α where 
  le_cSup : ∀ s a, BddAbove s → a ∈ s → a ≤ Sup s 
  cSup_le : ∀ s a, Set.Nonempty s → a ∈ UpperBounds s → Sup s ≤ a 
  cInf_le : ∀ s a, BddBelow s → a ∈ s → Inf s ≤ a 
  le_cInf : ∀ s a, Set.Nonempty s → a ∈ LowerBounds s → a ≤ Inf s

/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrder(α : Type _) extends ConditionallyCompleteLattice α, LinearOrderₓ α

/-- A conditionally complete linear order with `bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
@[ancestor ConditionallyCompleteLinearOrder HasBot]
class ConditionallyCompleteLinearOrderBot(α : Type _) extends ConditionallyCompleteLinearOrder α, HasBot α where 
  bot_le : ∀ (x : α), ⊥ ≤ x 
  cSup_empty : Sup ∅ = ⊥

instance (priority := 100)ConditionallyCompleteLinearOrderBot.toOrderBot [h : ConditionallyCompleteLinearOrderBot α] :
  OrderBot α :=
  { h with  }

/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/
instance (priority := 100)conditionallyCompleteLatticeOfCompleteLattice [CompleteLattice α] :
  ConditionallyCompleteLattice α :=
  { ‹CompleteLattice α› with
    le_cSup :=
      by 
        intros  <;> apply le_Sup <;> assumption,
    cSup_le :=
      by 
        intros  <;> apply Sup_le <;> assumption,
    cInf_le :=
      by 
        intros  <;> apply Inf_le <;> assumption,
    le_cInf :=
      by 
        intros  <;> apply le_Inf <;> assumption }

instance (priority := 100)conditionallyCompleteLinearOrderOfCompleteLinearOrder [CompleteLinearOrder α] :
  ConditionallyCompleteLinearOrder α :=
  { conditionallyCompleteLatticeOfCompleteLattice, ‹CompleteLinearOrder α› with  }

section 

open_locale Classical

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible]
noncomputable
def well_founded.conditionally_complete_linear_order_with_bot
{α : Type*}
[i : linear_order α]
(h : well_founded ((«expr < ») : α → α → exprProp()))
(c : α)
(hc : «expr = »(c, h.min set.univ ⟨c, mem_univ c⟩)) : conditionally_complete_linear_order_bot α :=
{ sup := max,
  le_sup_left := le_max_left,
  le_sup_right := le_max_right,
  sup_le := λ a b c, max_le,
  inf := min,
  inf_le_left := min_le_left,
  inf_le_right := min_le_right,
  le_inf := λ a b c, le_min,
  Inf := λ s, if hs : s.nonempty then h.min s hs else c,
  cInf_le := begin
    assume [binders (s a hs has)],
    have [ident s_ne] [":", expr s.nonempty] [":=", expr ⟨a, has⟩],
    simpa [] [] [] ["[", expr s_ne, "]"] [] ["using", expr not_lt.1 (h.not_lt_min s s_ne has)]
  end,
  le_cInf := begin
    assume [binders (s a hs has)],
    simp [] [] ["only"] ["[", expr hs, ",", expr dif_pos, "]"] [] [],
    exact [expr has (h.min_mem s hs)]
  end,
  Sup := λ s, if hs : (upper_bounds s).nonempty then h.min _ hs else c,
  le_cSup := begin
    assume [binders (s a hs has)],
    have [ident h's] [":", expr (upper_bounds s).nonempty] [":=", expr hs],
    simp [] [] ["only"] ["[", expr h's, ",", expr dif_pos, "]"] [] [],
    exact [expr h.min_mem _ h's has]
  end,
  cSup_le := begin
    assume [binders (s a hs has)],
    have [ident h's] [":", expr (upper_bounds s).nonempty] [":=", expr ⟨a, has⟩],
    simp [] [] ["only"] ["[", expr h's, ",", expr dif_pos, "]"] [] [],
    simpa [] [] [] [] [] ["using", expr h.not_lt_min _ h's has]
  end,
  bot := c,
  bot_le := λ x, by convert [] [expr not_lt.1 (h.not_lt_min set.univ ⟨c, mem_univ c⟩ (mem_univ x))] [],
  cSup_empty := begin
    have [] [":", expr (set.univ : set α).nonempty] [":=", expr ⟨c, mem_univ c⟩],
    simp [] [] ["only"] ["[", expr this, ",", expr dif_pos, ",", expr upper_bounds_empty, "]"] [] [],
    exact [expr hc.symm]
  end,
  ..i }

end 

section OrderDual

instance  (α : Type _) [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (OrderDual α) :=
  { OrderDual.hasInfₓ α, OrderDual.hasSupₓ α, OrderDual.lattice α with
    le_cSup := @ConditionallyCompleteLattice.cInf_le α _, cSup_le := @ConditionallyCompleteLattice.le_cInf α _,
    le_cInf := @ConditionallyCompleteLattice.cSup_le α _, cInf_le := @ConditionallyCompleteLattice.le_cSup α _ }

instance  (α : Type _) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder (OrderDual α) :=
  { OrderDual.conditionallyCompleteLattice α, OrderDual.linearOrder α with  }

end OrderDual

section ConditionallyCompleteLattice

variable[ConditionallyCompleteLattice α]{s t : Set α}{a b : α}

theorem le_cSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ Sup s :=
  ConditionallyCompleteLattice.le_cSup s a h₁ h₂

theorem cSup_le (h₁ : s.nonempty) (h₂ : ∀ b (_ : b ∈ s), b ≤ a) : Sup s ≤ a :=
  ConditionallyCompleteLattice.cSup_le s a h₁ h₂

theorem cInf_le (h₁ : BddBelow s) (h₂ : a ∈ s) : Inf s ≤ a :=
  ConditionallyCompleteLattice.cInf_le s a h₁ h₂

theorem le_cInf (h₁ : s.nonempty) (h₂ : ∀ b (_ : b ∈ s), a ≤ b) : a ≤ Inf s :=
  ConditionallyCompleteLattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le (_ : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
  le_transₓ h (le_cSup ‹BddAbove s› hb)

theorem cInf_le_of_le (_ : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
  le_transₓ (cInf_le ‹BddBelow s› hb) h

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem cSup_le_cSup (_ : bdd_above t) (_ : s.nonempty) (h : «expr ⊆ »(s, t)) : «expr ≤ »(Sup s, Sup t) :=
cSup_le «expr‹ ›»(_) (assume (a) (ha : «expr ∈ »(a, s)), le_cSup «expr‹ ›»(bdd_above t) (h ha))

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem cInf_le_cInf (_ : bdd_below t) (_ : s.nonempty) (h : «expr ⊆ »(s, t)) : «expr ≤ »(Inf t, Inf s) :=
le_cInf «expr‹ ›»(_) (assume (a) (ha : «expr ∈ »(a, s)), cInf_le «expr‹ ›»(bdd_below t) (h ha))

theorem is_lub_cSup (ne : s.nonempty) (H : BddAbove s) : IsLub s (Sup s) :=
  ⟨fun x => le_cSup H, fun x => cSup_le Ne⟩

theorem is_lub_csupr [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) : IsLub (range f) (⨆i, f i) :=
  is_lub_cSup (range_nonempty f) H

theorem is_lub_csupr_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.nonempty) :
  IsLub (f '' s) (⨆i : s, f i) :=
  by 
    rw [←Sup_image']
    exact is_lub_cSup (Hne.image _) H

theorem is_glb_cInf (ne : s.nonempty) (H : BddBelow s) : IsGlb s (Inf s) :=
  ⟨fun x => cInf_le H, fun x => le_cInf Ne⟩

theorem is_glb_cinfi [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) : IsGlb (range f) (⨅i, f i) :=
  is_glb_cInf (range_nonempty f) H

theorem is_glb_cinfi_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.nonempty) :
  IsGlb (f '' s) (⨅i : s, f i) :=
  @is_lub_csupr_set (OrderDual α) _ _ _ _ H Hne

theorem IsLub.cSup_eq (H : IsLub s a) (ne : s.nonempty) : Sup s = a :=
  (is_lub_cSup Ne ⟨a, H.1⟩).unique H

theorem IsLub.csupr_eq [Nonempty ι] {f : ι → α} (H : IsLub (range f) a) : (⨆i, f i) = a :=
  H.cSup_eq (range_nonempty f)

theorem IsLub.csupr_set_eq {s : Set β} {f : β → α} (H : IsLub (f '' s) a) (Hne : s.nonempty) : (⨆i : s, f i) = a :=
  IsLub.cSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.cSup_eq (H : IsGreatest s a) : Sup s = a :=
  H.is_lub.cSup_eq H.nonempty

theorem IsGreatest.Sup_mem (H : IsGreatest s a) : Sup s ∈ s :=
  H.cSup_eq.symm ▸ H.1

theorem IsGlb.cInf_eq (H : IsGlb s a) (ne : s.nonempty) : Inf s = a :=
  (is_glb_cInf Ne ⟨a, H.1⟩).unique H

theorem IsGlb.cinfi_eq [Nonempty ι] {f : ι → α} (H : IsGlb (range f) a) : (⨅i, f i) = a :=
  H.cInf_eq (range_nonempty f)

theorem IsGlb.cinfi_set_eq {s : Set β} {f : β → α} (H : IsGlb (f '' s) a) (Hne : s.nonempty) : (⨅i : s, f i) = a :=
  IsGlb.cInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.cInf_eq (H : IsLeast s a) : Inf s = a :=
  H.is_glb.cInf_eq H.nonempty

theorem IsLeast.Inf_mem (H : IsLeast s a) : Inf s ∈ s :=
  H.cInf_eq.symm ▸ H.1

theorem subset_Icc_cInf_cSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (Inf s) (Sup s) :=
  fun x hx => ⟨cInf_le hb hx, le_cSup ha hx⟩

theorem cSup_le_iff (hb : BddAbove s) (ne : s.nonempty) : Sup s ≤ a ↔ ∀ b (_ : b ∈ s), b ≤ a :=
  is_lub_le_iff (is_lub_cSup Ne hb)

theorem le_cInf_iff (hb : BddBelow s) (ne : s.nonempty) : a ≤ Inf s ↔ ∀ b (_ : b ∈ s), a ≤ b :=
  le_is_glb_iff (is_glb_cInf Ne hb)

theorem cSup_lower_bounds_eq_cInf {s : Set α} (h : BddBelow s) (hs : s.nonempty) : Sup (LowerBounds s) = Inf s :=
  (is_lub_cSup h$ hs.mono$ fun x hx y hy => hy hx).unique (is_glb_cInf hs h).IsLub

theorem cInf_upper_bounds_eq_cSup {s : Set α} (h : BddAbove s) (hs : s.nonempty) : Inf (UpperBounds s) = Sup s :=
  (is_glb_cInf h$ hs.mono$ fun x hx y hy => hy hx).unique (is_lub_cSup hs h).IsGlb

theorem not_mem_of_lt_cInf {x : α} {s : Set α} (h : x < Inf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irreflₓ _ (h.trans_le (cInf_le hs hx))

theorem not_mem_of_cSup_lt {x : α} {s : Set α} (h : Sup s < x) (hs : BddAbove s) : x ∉ s :=
  @not_mem_of_lt_cInf (OrderDual α) _ x s h hs

/--Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `Sup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem cSup_eq_of_forall_le_of_forall_lt_exists_gt (_ : s.nonempty) (_ : ∀ a (_ : a ∈ s), a ≤ b)
  (H : ∀ w, w < b → ∃ (a : _)(_ : a ∈ s), w < a) : Sup s = b :=
  have  : BddAbove s :=
    ⟨b,
      by 
        assumption⟩
  have  : Sup s < b ∨ Sup s = b := lt_or_eq_of_leₓ (cSup_le ‹_› ‹∀ a (_ : a ∈ s), a ≤ b›)
  have  : ¬Sup s < b :=
    fun this : Sup s < b =>
      let ⟨a, _, _⟩ := H (Sup s) ‹Sup s < b›
      have  : Sup s < Sup s := lt_of_lt_of_leₓ ‹Sup s < a› (le_cSup ‹BddAbove s› ‹a ∈ s›)
      show False by 
        finish [lt_irreflₓ (Sup s)]
  show Sup s = b by 
    finish

/--Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `Inf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cInf_eq_of_forall_ge_of_forall_gt_exists_lt (_ : s.nonempty) (_ : ∀ a (_ : a ∈ s), b ≤ a)
  (H : ∀ w, b < w → ∃ (a : _)(_ : a ∈ s), a < w) : Inf s = b :=
  @cSup_eq_of_forall_le_of_forall_lt_exists_gt (OrderDual α) _ _ _ ‹_› ‹_› ‹_›

/--b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem lt_cSup_of_lt (_ : BddAbove s) (_ : a ∈ s) (_ : b < a) : b < Sup s :=
  lt_of_lt_of_leₓ ‹b < a› (le_cSup ‹BddAbove s› ‹a ∈ s›)

/--Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem cInf_lt_of_lt (_ : BddBelow s) (_ : a ∈ s) (_ : a < b) : Inf s < b :=
  @lt_cSup_of_lt (OrderDual α) _ _ _ _ ‹_› ‹_› ‹_›

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.nonempty) (tne : t.nonempty) (hst : ∀ x (_ : x ∈ s) y (_ : y ∈ t), x ≤ y) :
  (UpperBounds s ∩ LowerBounds t).Nonempty :=
  ⟨Inf t, fun x hx => le_cInf tne$ hst x hx, fun y hy => cInf_le (sne.mono hst) hy⟩

/--The supremum of a singleton is the element of the singleton-/
@[simp]
theorem cSup_singleton (a : α) : Sup {a} = a :=
  is_greatest_singleton.cSup_eq

/--The infimum of a singleton is the element of the singleton-/
@[simp]
theorem cInf_singleton (a : α) : Inf {a} = a :=
  is_least_singleton.cInf_eq

/--If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup (hb : BddBelow s) (ha : BddAbove s) (ne : s.nonempty) : Inf s ≤ Sup s :=
  is_glb_le_is_lub (is_glb_cInf Ne hb) (is_lub_cSup Ne ha) Ne

/--The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union (hs : BddAbove s) (sne : s.nonempty) (ht : BddAbove t) (tne : t.nonempty) :
  Sup (s ∪ t) = Sup s⊔Sup t :=
  ((is_lub_cSup sne hs).union (is_lub_cSup tne ht)).cSup_eq sne.inl

/--The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union (hs : BddBelow s) (sne : s.nonempty) (ht : BddBelow t) (tne : t.nonempty) :
  Inf (s ∪ t) = Inf s⊓Inf t :=
  @cSup_union (OrderDual α) _ _ _ hs sne ht tne

/--The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (_ : BddAbove s) (_ : BddAbove t) (hst : (s ∩ t).Nonempty) : Sup (s ∩ t) ≤ Sup s⊓Sup t :=
  by 
    apply cSup_le hst 
    simp only [le_inf_iff, and_imp, Set.mem_inter_eq]
    intro b _ _ 
    split 
    apply le_cSup ‹BddAbove s› ‹b ∈ s›
    apply le_cSup ‹BddAbove t› ‹b ∈ t›

/--The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter (_ : BddBelow s) (_ : BddBelow t) (hst : (s ∩ t).Nonempty) : Inf s⊔Inf t ≤ Inf (s ∩ t) :=
  @cSup_inter_le (OrderDual α) _ _ _ ‹_› ‹_› hst

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (hs : BddAbove s) (sne : s.nonempty) : Sup (insert a s) = a⊔Sup s :=
  ((is_lub_cSup sne hs).insert a).cSup_eq (insert_nonempty a s)

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (hs : BddBelow s) (sne : s.nonempty) : Inf (insert a s) = a⊓Inf s :=
  @cSup_insert (OrderDual α) _ _ _ hs sne

@[simp]
theorem cInf_Icc (h : a ≤ b) : Inf (Icc a b) = a :=
  (is_glb_Icc h).cInf_eq (nonempty_Icc.2 h)

@[simp]
theorem cInf_Ici : Inf (Ici a) = a :=
  is_least_Ici.cInf_eq

@[simp]
theorem cInf_Ico (h : a < b) : Inf (Ico a b) = a :=
  (is_glb_Ico h).cInf_eq (nonempty_Ico.2 h)

@[simp]
theorem cInf_Ioc [DenselyOrdered α] (h : a < b) : Inf (Ioc a b) = a :=
  (is_glb_Ioc h).cInf_eq (nonempty_Ioc.2 h)

@[simp]
theorem cInf_Ioi [NoTopOrder α] [DenselyOrdered α] : Inf (Ioi a) = a :=
  cInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_ltₓ)
    fun w hw =>
      by 
        simpa using exists_between hw

@[simp]
theorem cInf_Ioo [DenselyOrdered α] (h : a < b) : Inf (Ioo a b) = a :=
  (is_glb_Ioo h).cInf_eq (nonempty_Ioo.2 h)

@[simp]
theorem cSup_Icc (h : a ≤ b) : Sup (Icc a b) = b :=
  (is_lub_Icc h).cSup_eq (nonempty_Icc.2 h)

@[simp]
theorem cSup_Ico [DenselyOrdered α] (h : a < b) : Sup (Ico a b) = b :=
  (is_lub_Ico h).cSup_eq (nonempty_Ico.2 h)

@[simp]
theorem cSup_Iic : Sup (Iic a) = a :=
  is_greatest_Iic.cSup_eq

@[simp]
theorem cSup_Iio [NoBotOrder α] [DenselyOrdered α] : Sup (Iio a) = a :=
  cSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_ltₓ)
    fun w hw =>
      by 
        simpa [and_comm] using exists_between hw

@[simp]
theorem cSup_Ioc (h : a < b) : Sup (Ioc a b) = b :=
  (is_lub_Ioc h).cSup_eq (nonempty_Ioc.2 h)

@[simp]
theorem cSup_Ioo [DenselyOrdered α] (h : a < b) : Sup (Ioo a b) = b :=
  (is_lub_Ioo h).cSup_eq (nonempty_Ioo.2 h)

/--The indexed supremum of a function is bounded above by a uniform bound-/
theorem csupr_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : supr f ≤ c :=
  cSup_le (range_nonempty f)
    (by 
      rwa [forall_range_iff])

/--The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_csupr {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ supr f :=
  le_cSup H (mem_range_self _)

theorem le_csupr_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ supr f :=
  le_transₓ h (le_csupr H c)

/--The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem csupr_le_csupr {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) : supr f ≤ supr g :=
  by 
    cases' is_empty_or_nonempty ι
    ·
      rw [supr_of_empty', supr_of_empty']
    ·
      exact csupr_le fun x => le_csupr_of_le B x (H x)

/--The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem cinfi_le_cinfi {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : infi f ≤ infi g :=
  @csupr_le_csupr (OrderDual α) _ _ _ _ B H

/--The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_cinfi [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ infi f :=
  @csupr_le (OrderDual α) _ _ _ _ _ H

/--The indexed infimum of a function is bounded above by the value taken at one point-/
theorem cinfi_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : infi f ≤ f c :=
  @le_csupr (OrderDual α) _ _ _ H c

theorem cinfi_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : infi f ≤ a :=
  @le_csupr_of_le (OrderDual α) _ _ _ _ H c h

@[simp]
theorem csupr_const [hι : Nonempty ι] {a : α} : (⨆b : ι, a) = a :=
  by 
    rw [supr, range_const, cSup_singleton]

@[simp]
theorem cinfi_const [hι : Nonempty ι] {a : α} : (⨅b : ι, a) = a :=
  @csupr_const (OrderDual α) _ _ _ _

theorem supr_unique [Unique ι] {s : ι → α} : (⨆i, s i) = s (default ι) :=
  have  : ∀ i, s i = s (default ι) := fun i => congr_argₓ s (Unique.eq_default i)
  by 
    simp only [this, csupr_const]

theorem infi_unique [Unique ι] {s : ι → α} : (⨅i, s i) = s (default ι) :=
  @supr_unique (OrderDual α) _ _ _ _

@[simp]
theorem supr_unit {f : Unit → α} : (⨆x, f x) = f () :=
  by 
    convert supr_unique 
    infer_instance

@[simp]
theorem infi_unit {f : Unit → α} : (⨅x, f x) = f () :=
  @supr_unit (OrderDual α) _ _

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem csupr_pos {p : exprProp()} {f : p → α} (hp : p) : «expr = »(«expr⨆ , »((h : p), f h), f hp) :=
by haveI [] [] [":=", expr unique_prop hp]; exact [expr supr_unique]

@[simp]
theorem cinfi_pos {p : Prop} {f : p → α} (hp : p) : (⨅h : p, f h) = f hp :=
  @csupr_pos (OrderDual α) _ _ _ hp

theorem csupr_set {s : Set β} {f : β → α} : (⨆x : s, f x) = Sup (f '' s) :=
  by 
    rw [supr]
    congr 
    ext 
    rw [mem_image, mem_range, SetCoe.exists]
    simpRw [Subtype.coe_mk, exists_prop]

theorem cinfi_set {s : Set β} {f : β → α} : (⨅x : s, f x) = Inf (f '' s) :=
  @csupr_set (OrderDual α) _ _ _ _

/--Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `supr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupr_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
  (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆i : ι, f i) = b :=
  cSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁)
    fun w hw => exists_range_iff.mpr$ h₂ w hw

/--Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `infi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfi_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
  (h₂ : ∀ w, b < w → ∃ i, f i < w) : (⨅i : ι, f i) = b :=
  @csupr_eq_of_forall_le_of_forall_lt_exists_gt (OrderDual α) _ _ _ _ ‹_› ‹_› ‹_›

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem monotone.csupr_mem_Inter_Icc_of_antitone
[semilattice_sup β]
{f g : β → α}
(hf : monotone f)
(hg : antitone g)
(h : «expr ≤ »(f, g)) : «expr ∈ »(«expr⨆ , »((n), f n), «expr⋂ , »((n), Icc (f n) (g n))) :=
begin
  refine [expr mem_Inter.2 (λ n, _)],
  haveI [] [":", expr nonempty β] [":=", expr ⟨n⟩],
  have [] [":", expr ∀ m, «expr ≤ »(f m, g n)] [":=", expr λ m, hf.forall_le_of_antitone hg h m n],
  exact [expr ⟨le_csupr ⟨«expr $ »(g, n), forall_range_iff.2 this⟩ _, csupr_le this⟩]
end

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem csupr_mem_Inter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α} (h : Antitone fun n => Icc (f n) (g n))
  (h' : ∀ n, f n ≤ g n) : (⨆n, f n) ∈ ⋂n, Icc (f n) (g n) :=
  Monotone.csupr_mem_Inter_Icc_of_antitone (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

theorem Finset.Nonempty.sup'_eq_cSup_image {s : Finset β} (hs : s.nonempty) (f : β → α) : s.sup' hs f = Sup (f '' s) :=
  eq_of_forall_ge_iff$
    fun a =>
      by 
        simp [cSup_le_iff (s.finite_to_set.image f).BddAbove (hs.to_set.image f)]

theorem Finset.Nonempty.sup'_id_eq_cSup {s : Finset α} (hs : s.nonempty) : s.sup' hs id = Sup s :=
  by 
    rw [hs.sup'_eq_cSup_image, image_id]

end ConditionallyCompleteLattice

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance pi.conditionally_complete_lattice
{ι : Type*}
{α : ∀ i : ι, Type*}
[∀ i, conditionally_complete_lattice (α i)] : conditionally_complete_lattice (∀ i, α i) :=
{ le_cSup := λ
  (s f)
  ⟨g, hg⟩
  (hf i), le_cSup ⟨g i, «expr $ »(set.forall_range_iff.2, λ ⟨f', hf'⟩, hg hf' i)⟩ ⟨⟨f, hf⟩, rfl⟩,
  cSup_le := λ
  s
  f
  hs
  hf
  i, «expr $ »(cSup_le (by haveI [] [] [":=", expr hs.to_subtype]; apply [expr range_nonempty]), λ
   (b)
   ⟨⟨g, hg⟩, hb⟩, «expr ▸ »(hb, hf hg i)),
  cInf_le := λ
  (s f)
  ⟨g, hg⟩
  (hf i), cInf_le ⟨g i, «expr $ »(set.forall_range_iff.2, λ ⟨f', hf'⟩, hg hf' i)⟩ ⟨⟨f, hf⟩, rfl⟩,
  le_cInf := λ
  s
  f
  hs
  hf
  i, «expr $ »(le_cInf (by haveI [] [] [":=", expr hs.to_subtype]; apply [expr range_nonempty]), λ
   (b)
   ⟨⟨g, hg⟩, hb⟩, «expr ▸ »(hb, hf hg i)),
  ..pi.lattice,
  ..pi.has_Sup,
  ..pi.has_Inf }

section ConditionallyCompleteLinearOrder

variable[ConditionallyCompleteLinearOrder α]{s t : Set α}{a b : α}

theorem Finset.Nonempty.cSup_eq_max' {s : Finset α} (h : s.nonempty) : Sup («expr↑ » s) = s.max' h :=
  eq_of_forall_ge_iff$ fun a => (cSup_le_iff s.bdd_above h.to_set).trans (s.max'_le_iff h).symm

theorem Finset.Nonempty.cInf_eq_min' {s : Finset α} (h : s.nonempty) : Inf («expr↑ » s) = s.min' h :=
  @Finset.Nonempty.cSup_eq_max' (OrderDual α) _ s h

theorem Finset.Nonempty.cSup_mem {s : Finset α} (h : s.nonempty) : Sup (s : Set α) ∈ s :=
  by 
    rw [h.cSup_eq_max']
    exact s.max'_mem _

theorem Finset.Nonempty.cInf_mem {s : Finset α} (h : s.nonempty) : Inf (s : Set α) ∈ s :=
  @Finset.Nonempty.cSup_mem (OrderDual α) _ _ h

theorem Set.Nonempty.cSup_mem (h : s.nonempty) (hs : finite s) : Sup s ∈ s :=
  by 
    lift s to Finset α using hs 
    exact Finset.Nonempty.cSup_mem h

theorem Set.Nonempty.cInf_mem (h : s.nonempty) (hs : finite s) : Inf s ∈ s :=
  @Set.Nonempty.cSup_mem (OrderDual α) _ _ h hs

theorem Set.Finite.cSup_lt_iff (hs : finite s) (h : s.nonempty) : Sup s < a ↔ ∀ x (_ : x ∈ s), x < a :=
  ⟨fun h x hx => (le_cSup hs.bdd_above hx).trans_lt h, fun H => H _$ h.cSup_mem hs⟩

theorem Set.Finite.lt_cInf_iff (hs : finite s) (h : s.nonempty) : a < Inf s ↔ ∀ x (_ : x ∈ s), a < x :=
  @Set.Finite.cSup_lt_iff (OrderDual α) _ _ _ hs h

/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
theorem exists_lt_of_lt_cSup (hs : s.nonempty) (hb : b < Sup s) : ∃ (a : _)(_ : a ∈ s), b < a :=
  by 
    classical 
    contrapose! hb 
    exact cSup_le hs hb

/--
Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_csupr [Nonempty ι] {f : ι → α} (h : b < supr f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_cSup (range_nonempty f) h
  ⟨i, h⟩

/--When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
theorem exists_lt_of_cInf_lt (hs : s.nonempty) (hb : Inf s < b) : ∃ (a : _)(_ : a ∈ s), a < b :=
  @exists_lt_of_lt_cSup (OrderDual α) _ _ _ hs hb

/--
Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_cinfi_lt [Nonempty ι] {f : ι → α} (h : infi f < a) : ∃ i, f i < a :=
  @exists_lt_of_lt_csupr (OrderDual α) _ _ _ _ _ h

/--Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem cSup_eq_of_is_forall_le_of_forall_le_imp_ge (_ : s.nonempty) (h_is_ub : ∀ a (_ : a ∈ s), a ≤ b)
  (h_b_le_ub : ∀ ub, (∀ a (_ : a ∈ s), a ≤ ub) → b ≤ ub) : Sup s = b :=
  le_antisymmₓ (show Sup s ≤ b from cSup_le ‹s.nonempty› h_is_ub)
    (show b ≤ Sup s from h_b_le_ub _$ fun a => le_cSup ⟨b, h_is_ub⟩)

open Function

variable[IsWellOrder α (· < ·)]

theorem Inf_eq_argmin_on (hs : s.nonempty) : Inf s = argmin_on id (@IsWellOrder.wf α (· < ·) _) s hs :=
  IsLeast.cInf_eq ⟨argmin_on_mem _ _ _ _, fun a ha => argmin_on_le id _ _ ha⟩

theorem is_least_Inf (hs : s.nonempty) : IsLeast s (Inf s) :=
  by 
    rw [Inf_eq_argmin_on hs]
    exact ⟨argmin_on_mem _ _ _ _, fun a ha => argmin_on_le id _ _ ha⟩

theorem le_cInf_iff' (hs : s.nonempty) : b ≤ Inf s ↔ b ∈ LowerBounds s :=
  le_is_glb_iff (is_least_Inf hs).IsGlb

theorem Inf_mem (hs : s.nonempty) : Inf s ∈ s :=
  (is_least_Inf hs).1

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `nonempty`/`set.nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable[ConditionallyCompleteLinearOrderBot α]

theorem cSup_empty : (Sup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.cSup_empty

theorem csupr_of_empty [IsEmpty ι] (f : ι → α) : (⨆i, f i) = ⊥ :=
  by 
    rw [supr_of_empty', cSup_empty]

@[simp]
theorem csupr_false (f : False → α) : (⨆i, f i) = ⊥ :=
  csupr_of_empty f

theorem is_lub_cSup' {s : Set α} (hs : BddAbove s) : IsLub s (Sup s) :=
  by 
    rcases eq_empty_or_nonempty s with (rfl | hne)
    ·
      simp only [cSup_empty, is_lub_empty]
    ·
      exact is_lub_cSup hne hs

theorem cSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : Sup s ≤ a ↔ ∀ x (_ : x ∈ s), x ≤ a :=
  is_lub_le_iff (is_lub_cSup' hs)

theorem cSup_le' {s : Set α} {a : α} (h : a ∈ UpperBounds s) : Sup s ≤ a :=
  (cSup_le_iff' ⟨a, h⟩).2 h

theorem exists_lt_of_lt_cSup' {s : Set α} {a : α} (h : a < Sup s) : ∃ (b : _)(_ : b ∈ s), a < b :=
  by 
    contrapose! h 
    exact cSup_le' h

theorem csupr_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} : (⨆i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
  (cSup_le_iff' h).trans forall_range_iff

theorem csupr_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆i, f i) ≤ a :=
  cSup_le'$ forall_range_iff.2 h

theorem exists_lt_of_lt_csupr' {f : ι → α} {a : α} (h : a < ⨆i, f i) : ∃ i, a < f i :=
  by 
    contrapose! h 
    exact csupr_le' h

end ConditionallyCompleteLinearOrderBot

namespace WithTop

open_locale Classical

variable[ConditionallyCompleteLinearOrderBot α]

/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem is_lub_Sup' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)} (hs : s.nonempty) :
  IsLub s (Sup s) :=
  by 
    split 
    ·
      show ite _ _ _ ∈ _ 
      splitIfs
      ·
        intro _ _ 
        exact le_top
      ·
        rintro (⟨⟩ | a) ha
        ·
          contradiction 
        apply some_le_some.2 
        exact le_cSup h_1 ha
      ·
        intro _ _ 
        exact le_top
    ·
      show ite _ _ _ ∈ _ 
      splitIfs
      ·
        rintro (⟨⟩ | a) ha
        ·
          exact _root_.le_refl _
        ·
          exact False.elim (not_top_le_coe a (ha h))
      ·
        rintro (⟨⟩ | b) hb
        ·
          exact le_top 
        refine' some_le_some.2 (cSup_le _ _)
        ·
          rcases hs with ⟨⟨⟩ | b, hb⟩
          ·
            exact absurd hb h
          ·
            exact ⟨b, hb⟩
        ·
          intro a ha 
          exact some_le_some.1 (hb ha)
      ·
        rintro (⟨⟩ | b) hb
        ·
          exact _root_.le_refl _
        ·
          exfalso 
          apply h_1 
          use b 
          intro a ha 
          exact some_le_some.1 (hb ha)

theorem is_lub_Sup (s : Set (WithTop α)) : IsLub s (Sup s) :=
  by 
    cases' s.eq_empty_or_nonempty with hs hs
    ·
      rw [hs]
      show IsLub ∅ (ite _ _ _)
      splitIfs
      ·
        cases h
      ·
        rw [preimage_empty, cSup_empty]
        exact is_lub_empty
      ·
        exfalso 
        apply h_1 
        use ⊥
        rintro a ⟨⟩
    exact is_lub_Sup' hs

/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem is_glb_Inf' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)} (hs : BddBelow s) :
  IsGlb s (Inf s) :=
  by 
    split 
    ·
      show ite _ _ _ ∈ _ 
      splitIfs
      ·
        intro a ha 
        exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
      ·
        rintro (⟨⟩ | a) ha
        ·
          exact le_top 
        refine' some_le_some.2 (cInf_le _ ha)
        rcases hs with ⟨⟨⟩ | b, hb⟩
        ·
          exfalso 
          apply h 
          intro c hc 
          rw [mem_singleton_iff, ←top_le_iff]
          exact hb hc 
        use b 
        intro c hc 
        exact some_le_some.1 (hb hc)
    ·
      show ite _ _ _ ∈ _ 
      splitIfs
      ·
        intro _ _ 
        exact le_top
      ·
        rintro (⟨⟩ | a) ha
        ·
          exfalso 
          apply h 
          intro b hb 
          exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
        ·
          refine' some_le_some.2 (le_cInf _ _)
          ·
            classical 
            contrapose! h 
            rintro (⟨⟩ | a) ha
            ·
              exact mem_singleton ⊤
            ·
              exact (h ⟨a, ha⟩).elim
          ·
            intro b hb 
            rw [←some_le_some]
            exact ha hb

theorem is_glb_Inf (s : Set (WithTop α)) : IsGlb s (Inf s) :=
  by 
    byCases' hs : BddBelow s
    ·
      exact is_glb_Inf' hs
    ·
      exfalso 
      apply hs 
      use ⊥
      intro _ _ 
      exact bot_le

noncomputable instance  : CompleteLinearOrder (WithTop α) :=
  { WithTop.linearOrder, WithTop.lattice, WithTop.orderTop, WithTop.orderBot with sup := Sup,
    le_Sup := fun s => (is_lub_Sup s).1, Sup_le := fun s => (is_lub_Sup s).2, inf := Inf,
    le_Inf := fun s => (is_glb_Inf s).2, Inf_le := fun s => (is_glb_Inf s).1 }

theorem coe_Sup {s : Set α} (hb : BddAbove s) : («expr↑ » (Sup s) : WithTop α) = ⨆(a : _)(_ : a ∈ s), «expr↑ » a :=
  by 
    cases' s.eq_empty_or_nonempty with hs hs
    ·
      rw [hs, cSup_empty]
      simp only [Set.mem_empty_eq, supr_bot, supr_false]
      rfl 
    apply le_antisymmₓ
    ·
      refine' coe_le_iff.2$ fun b hb => cSup_le hs$ fun a has => coe_le_coe.1$ hb ▸ _ 
      exact le_supr_of_le a$ le_supr_of_le has$ _root_.le_refl _
    ·
      exact supr_le$ fun a => supr_le$ fun ha => coe_le_coe.2$ le_cSup hb ha

theorem coe_Inf {s : Set α} (hs : s.nonempty) : («expr↑ » (Inf s) : WithTop α) = ⨅(a : _)(_ : a ∈ s), «expr↑ » a :=
  let ⟨x, hx⟩ := hs 
  have  : (⨅(a : _)(_ : a ∈ s), «expr↑ » a : WithTop α) ≤ x := infi_le_of_le x$ infi_le_of_le hx$ _root_.le_refl _ 
  let ⟨r, r_eq, hr⟩ := le_coe_iff.1 this 
  le_antisymmₓ (le_infi$ fun a => le_infi$ fun ha => coe_le_coe.2$ cInf_le (OrderBot.bdd_below s) ha)
    (by 
      refine' r_eq.symm ▸ coe_le_coe.2$ le_cInf hs$ fun a has => coe_le_coe.1$ _ 
      refine' r_eq ▸ infi_le_of_le a _ 
      exact infi_le_of_le has$ _root_.le_refl _)

end WithTop

namespace Monotone

variable[Preorderₓ α][ConditionallyCompleteLattice β]{f : α → β}(h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`Sup` and `Inf`. -/


theorem le_cSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) : f c ≤ Sup (f '' s) :=
  le_cSup (map_bdd_above h_mono h_bdd) (mem_image_of_mem f hcs)

theorem cSup_image_le {s : Set α} (hs : s.nonempty) {B : α} (hB : B ∈ UpperBounds s) : Sup (f '' s) ≤ f B :=
  cSup_le (nonempty.image f hs) (h_mono.mem_upper_bounds_image hB)

theorem cInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) : Inf (f '' s) ≤ f c :=
  @le_cSup_image (OrderDual α) (OrderDual β) _ _ _ (fun x y hxy => h_mono hxy) _ _ hcs h_bdd

theorem le_cInf_image {s : Set α} (hs : s.nonempty) {B : α} (hB : B ∈ LowerBounds s) : f B ≤ Inf (f '' s) :=
  @cSup_image_le (OrderDual α) (OrderDual β) _ _ _ (fun x y hxy => h_mono hxy) _ hs _ hB

end Monotone

namespace GaloisConnection

variable{γ : Type _}[ConditionallyCompleteLattice α][ConditionallyCompleteLattice β][Nonempty ι]{l : α → β}{u : β → α}

theorem l_cSup (gc : GaloisConnection l u) {s : Set α} (hne : s.nonempty) (hbdd : BddAbove s) :
  l (Sup s) = ⨆x : s, l x :=
  Eq.symm$ IsLub.csupr_set_eq (gc.is_lub_l_image$ is_lub_cSup hne hbdd) hne

theorem l_cSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.nonempty) (hbdd : BddAbove s) :
  l (Sup s) = Sup (l '' s) :=
  by 
    rw [gc.l_cSup hne hbdd, csupr_set]

theorem l_csupr (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) : l (⨆i, f i) = ⨆i, l (f i) :=
  by 
    rw [supr, gc.l_cSup (range_nonempty _) hf, supr_range']

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem l_csupr_set
(gc : galois_connection l u)
{s : set γ}
{f : γ → α}
(hf : bdd_above «expr '' »(f, s))
(hne : s.nonempty) : «expr = »(l «expr⨆ , »((i : s), f i), «expr⨆ , »((i : s), l (f i))) :=
by { haveI [] [] [":=", expr hne.to_subtype],
  rw [expr image_eq_range] ["at", ident hf],
  exact [expr gc.l_csupr hf] }

theorem u_cInf (gc : GaloisConnection l u) {s : Set β} (hne : s.nonempty) (hbdd : BddBelow s) :
  u (Inf s) = ⨅x : s, u x :=
  gc.dual.l_cSup hne hbdd

theorem u_cInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.nonempty) (hbdd : BddBelow s) :
  u (Inf s) = Inf (u '' s) :=
  gc.dual.l_cSup' hne hbdd

theorem u_cinfi (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) : u (⨅i, f i) = ⨅i, u (f i) :=
  gc.dual.l_csupr hf

theorem u_cinfi_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s)) (hne : s.nonempty) :
  u (⨅i : s, f i) = ⨅i : s, u (f i) :=
  gc.dual.l_csupr_set hf hne

end GaloisConnection

namespace OrderIso

variable{γ : Type _}[ConditionallyCompleteLattice α][ConditionallyCompleteLattice β][Nonempty ι]

theorem map_cSup (e : α ≃o β) {s : Set α} (hne : s.nonempty) (hbdd : BddAbove s) : e (Sup s) = ⨆x : s, e x :=
  e.to_galois_connection.l_cSup hne hbdd

theorem map_cSup' (e : α ≃o β) {s : Set α} (hne : s.nonempty) (hbdd : BddAbove s) : e (Sup s) = Sup (e '' s) :=
  e.to_galois_connection.l_cSup' hne hbdd

theorem map_csupr (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) : e (⨆i, f i) = ⨆i, e (f i) :=
  e.to_galois_connection.l_csupr hf

theorem map_csupr_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s)) (hne : s.nonempty) :
  e (⨆i : s, f i) = ⨆i : s, e (f i) :=
  e.to_galois_connection.l_csupr_set hf hne

theorem map_cInf (e : α ≃o β) {s : Set α} (hne : s.nonempty) (hbdd : BddBelow s) : e (Inf s) = ⨅x : s, e x :=
  e.dual.map_cSup hne hbdd

theorem map_cInf' (e : α ≃o β) {s : Set α} (hne : s.nonempty) (hbdd : BddBelow s) : e (Inf s) = Inf (e '' s) :=
  e.dual.map_cSup' hne hbdd

theorem map_cinfi (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) : e (⨅i, f i) = ⨅i, e (f i) :=
  e.dual.map_csupr hf

theorem map_cinfi_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s)) (hne : s.nonempty) :
  e (⨅i : s, f i) = ⨅i : s, e (f i) :=
  e.dual.map_csupr_set hf hne

end OrderIso

/-!
### Relation between `Sup` / `Inf` and `finset.sup'` / `finset.inf'`

Like the `Sup` of a `conditionally_complete_lattice`, `finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/


namespace Finset

theorem sup'_eq_cSup_image [ConditionallyCompleteLattice β] (s : Finset α) H (f : α → β) : s.sup' H f = Sup (f '' s) :=
  by 
    apply le_antisymmₓ
    ·
      refine' Finset.sup'_le _ _$ fun a ha => _ 
      refine' le_cSup ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩
      rintro i ⟨j, hj, rfl⟩
      exact Finset.le_sup' _ hj
    ·
      apply cSup_le ((coe_nonempty.mpr H).Image _)
      rintro _ ⟨a, ha, rfl⟩
      exact Finset.le_sup' _ ha

theorem inf'_eq_cInf_image [ConditionallyCompleteLattice β] (s : Finset α) H (f : α → β) : s.inf' H f = Inf (f '' s) :=
  @sup'_eq_cSup_image _ (OrderDual β) _ _ _ _

theorem sup'_id_eq_cSup [ConditionallyCompleteLattice α] (s : Finset α) H : s.sup' H id = Sup s :=
  by 
    rw [sup'_eq_cSup_image s H, Set.image_id]

theorem inf'_id_eq_cInf [ConditionallyCompleteLattice α] (s : Finset α) H : s.inf' H id = Inf s :=
  @sup'_id_eq_cSup (OrderDual α) _ _ _

end Finset

section WithTopBot

/-!
### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` naturally inherits the structure of a complete lattice. Note that
for α a conditionally complete lattice, `Sup` and `Inf` both return junk values
for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals [-∞, ∞] are a complete lattice.
-/


open_locale Classical

/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type _} [ConditionallyCompleteLattice α] :
  ConditionallyCompleteLattice (WithTop α) :=
  { WithTop.lattice, WithTop.hasSup, WithTop.hasInf with
    le_cSup := fun S a hS haS => (WithTop.is_lub_Sup' ⟨a, haS⟩).1 haS,
    cSup_le := fun S a hS haS => (WithTop.is_lub_Sup' hS).2 haS,
    cInf_le := fun S a hS haS => (WithTop.is_glb_Inf' hS).1 haS,
    le_cInf := fun S a hS haS => (WithTop.is_glb_Inf' ⟨a, haS⟩).2 haS }

/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type _} [ConditionallyCompleteLattice α] :
  ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice, WithBot.hasSup, WithBot.hasInf with
    le_cSup := (@WithTop.conditionallyCompleteLattice (OrderDual α) _).cInf_le,
    cSup_le := (@WithTop.conditionallyCompleteLattice (OrderDual α) _).le_cInf,
    cInf_le := (@WithTop.conditionallyCompleteLattice (OrderDual α) _).le_cSup,
    le_cInf := (@WithTop.conditionallyCompleteLattice (OrderDual α) _).cSup_le }

noncomputable instance WithTop.WithBot.completeLattice {α : Type _} [ConditionallyCompleteLattice α] :
  CompleteLattice (WithTop (WithBot α)) :=
  { WithTop.hasInf, WithTop.hasSup, WithTop.boundedOrder, WithTop.lattice with
    le_Sup := fun S a haS => (WithTop.is_lub_Sup' ⟨a, haS⟩).1 haS,
    Sup_le :=
      fun S a ha =>
        by 
          cases' S.eq_empty_or_nonempty with h
          ·
            show ite _ _ _ ≤ a 
            splitIfs
            ·
              rw [h] at h_1 
              cases h_1
            ·
              convert bot_le 
              convert WithBot.cSup_empty 
              rw [h]
              rfl
            ·
              exfalso 
              apply h_2 
              use ⊥
              rw [h]
              rintro b ⟨⟩
          ·
            refine' (WithTop.is_lub_Sup' h).2 ha,
    Inf_le :=
      fun S a haS =>
        show ite _ _ _ ≤ a by 
          splitIfs
          ·
            cases' a with a 
            exact _root_.le_refl _ 
            cases h haS <;> tauto
          ·
            cases a
            ·
              exact le_top
            ·
              apply WithTop.some_le_some.2
              refine' cInf_le _ haS 
              use ⊥
              intro b hb 
              exact bot_le,
    le_Inf := fun S a haS => (WithTop.is_glb_Inf' ⟨a, haS⟩).2 haS }

noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type _} [ConditionallyCompleteLinearOrder α] :
  CompleteLinearOrder (WithTop (WithBot α)) :=
  { WithTop.WithBot.completeLattice, WithTop.linearOrder with  }

end WithTopBot

section Subtype

variable(s : Set α)

/-! ### Subtypes of conditionally complete linear orders

In this section we give conditions on a subset of a conditionally complete linear order, to ensure
that the subtype is itself conditionally complete.

We check that an `ord_connected` set satisfies these conditions.

TODO There are several possible variants; the `conditionally_complete_linear_order` could be changed
to `conditionally_complete_linear_order_bot` or `complete_linear_order`.
-/


open_locale Classical

section HasSupₓ

variable[HasSupₓ α]

/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetHasSup [Inhabited s] : HasSupₓ s :=
  { sup := fun t => if ht : Sup (coeₓ '' t : Set α) ∈ s then ⟨Sup (coeₓ '' t : Set α), ht⟩ else default s }

attribute [local instance] subsetHasSup

@[simp]
theorem subset_Sup_def [Inhabited s] :
  @Sup s _ = fun t => if ht : Sup (coeₓ '' t : Set α) ∈ s then ⟨Sup (coeₓ '' t : Set α), ht⟩ else default s :=
  rfl

theorem subset_Sup_of_within [Inhabited s] {t : Set s} (h : Sup (coeₓ '' t : Set α) ∈ s) :
  Sup (coeₓ '' t : Set α) = (@Sup s _ t : α) :=
  by 
    simp [dif_pos h]

end HasSupₓ

section HasInfₓ

variable[HasInfₓ α]

/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetHasInf [Inhabited s] : HasInfₓ s :=
  { inf := fun t => if ht : Inf (coeₓ '' t : Set α) ∈ s then ⟨Inf (coeₓ '' t : Set α), ht⟩ else default s }

attribute [local instance] subsetHasInf

@[simp]
theorem subset_Inf_def [Inhabited s] :
  @Inf s _ = fun t => if ht : Inf (coeₓ '' t : Set α) ∈ s then ⟨Inf (coeₓ '' t : Set α), ht⟩ else default s :=
  rfl

theorem subset_Inf_of_within [Inhabited s] {t : Set s} (h : Inf (coeₓ '' t : Set α) ∈ s) :
  Inf (coeₓ '' t : Set α) = (@Inf s _ t : α) :=
  by 
    simp [dif_pos h]

end HasInfₓ

variable[ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetHasSup

attribute [local instance] subsetHasInf

-- error in Order.ConditionallyCompleteLattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable
def subset_conditionally_complete_linear_order
[inhabited s]
(h_Sup : ∀ {t : set s} (ht : t.nonempty) (h_bdd : bdd_above t), «expr ∈ »(Sup («expr '' »(coe, t) : set α), s))
(h_Inf : ∀
 {t : set s}
 (ht : t.nonempty)
 (h_bdd : bdd_below t), «expr ∈ »(Inf («expr '' »(coe, t) : set α), s)) : conditionally_complete_linear_order s :=
{ le_cSup := begin
    rintros [ident t, ident c, ident h_bdd, ident hct],
    have [] [] [":=", expr (subtype.mono_coe s).le_cSup_image hct h_bdd],
    rwa [expr subset_Sup_of_within s (h_Sup ⟨c, hct⟩ h_bdd)] ["at", ident this]
  end,
  cSup_le := begin
    rintros [ident t, ident B, ident ht, ident hB],
    have [] [] [":=", expr (subtype.mono_coe s).cSup_image_le ht hB],
    rwa [expr subset_Sup_of_within s (h_Sup ht ⟨B, hB⟩)] ["at", ident this]
  end,
  le_cInf := begin
    intros [ident t, ident B, ident ht, ident hB],
    have [] [] [":=", expr (subtype.mono_coe s).le_cInf_image ht hB],
    rwa [expr subset_Inf_of_within s (h_Inf ht ⟨B, hB⟩)] ["at", ident this]
  end,
  cInf_le := begin
    rintros [ident t, ident c, ident h_bdd, ident hct],
    have [] [] [":=", expr (subtype.mono_coe s).cInf_image_le hct h_bdd],
    rwa [expr subset_Inf_of_within s (h_Inf ⟨c, hct⟩ h_bdd)] ["at", ident this]
  end,
  ..subset_has_Sup s,
  ..subset_has_Inf s,
  ..distrib_lattice.to_lattice s,
  ..(infer_instance : linear_order s) }

section OrdConnected

/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem Sup_within_of_ord_connected {s : Set α} [hs : ord_connected s] ⦃t : Set s⦄ (ht : t.nonempty)
  (h_bdd : BddAbove t) : Sup (coeₓ '' t : Set α) ∈ s :=
  by 
    obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht 
    obtain ⟨B, hB⟩ : ∃ B, B ∈ UpperBounds t := h_bdd 
    refine' hs.out c.2 B.2 ⟨_, _⟩
    ·
      exact (Subtype.mono_coe s).le_cSup_image hct ⟨B, hB⟩
    ·
      exact (Subtype.mono_coe s).cSup_image_le ⟨c, hct⟩ hB

/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem Inf_within_of_ord_connected {s : Set α} [hs : ord_connected s] ⦃t : Set s⦄ (ht : t.nonempty)
  (h_bdd : BddBelow t) : Inf (coeₓ '' t : Set α) ∈ s :=
  by 
    obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht 
    obtain ⟨B, hB⟩ : ∃ B, B ∈ LowerBounds t := h_bdd 
    refine' hs.out B.2 c.2 ⟨_, _⟩
    ·
      exact (Subtype.mono_coe s).le_cInf_image ⟨c, hct⟩ hB
    ·
      exact (Subtype.mono_coe s).cInf_image_le hct ⟨B, hB⟩

/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s] [ord_connected s] :
  ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s Sup_within_of_ord_connected Inf_within_of_ord_connected

end OrdConnected

end Subtype

