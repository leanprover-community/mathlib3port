import Mathbin.Data.Rbtree.Default 
import Mathbin.Data.Rbmap.Basic

universe u v

namespace Rbmap

variable {α : Type u} {β : Type v} {lt : α → α → Prop}

private def rbmap_lt_is_swo {α : Type u} {β : Type v} {lt : α → α → Prop} [IsStrictWeakOrder α lt] :
  IsStrictWeakOrder (α × β) (RbmapLt lt) :=
  { irrefl := fun _ => irrefl_of lt _, trans := fun _ _ _ h₁ h₂ => trans_of lt h₁ h₂,
    incomp_trans := fun _ _ _ h₁ h₂ => incomp_trans_of lt h₁ h₂ }

private def rbmap_lt_dec {α : Type u} {β : Type v} {lt : α → α → Prop} [h : DecidableRel lt] :
  DecidableRel (@RbmapLt α β lt) :=
  fun a b => h a.1 b.1

attribute [local instance] rbmap_lt_is_swo rbmap_lt_dec

private theorem to_rbtree_mem {k : α} {m : Rbmap α β lt} : (k∈m) → ∃ v : β, Rbtree.Mem (k, v) m :=
  by 
    cases' m with n p <;> cases n <;> intro h
    ·
      exact False.elim h 
    all_goals 
      exists n_val.2 
      exact h

private theorem eqv_entries_of_eqv_keys {k₁ k₂ : α} (v₁ v₂ : β) : k₁ ≈[lt]k₂ → (k₁, v₁) ≈[RbmapLt lt](k₂, v₂) :=
  id

private theorem eqv_keys_of_eqv_entries {k₁ k₂ : α} {v₁ v₂ : β} : (k₁, v₁) ≈[RbmapLt lt](k₂, v₂) → k₁ ≈[lt]k₂ :=
  id

private theorem eqv_entries [IsIrrefl α lt] (k : α) (v₁ v₂ : β) : (k, v₁) ≈[RbmapLt lt](k, v₂) :=
  And.intro (irrefl_of lt k) (irrefl_of lt k)

private theorem to_rbmap_mem [IsStrictWeakOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
  Rbtree.Mem (k, v) m → (k∈m) :=
  by 
    cases' m with n p <;> cases n <;> intro h
    ·
      exact False.elim h
    ·
      simp [HasMem.Mem, Rbmap.Mem]
      exact @Rbtree.mem_of_mem_of_eqv _ _ _ ⟨Rbnode.red_node n_lchild n_val n_rchild, p⟩ _ _ h (eqv_entries _ _ _)
    ·
      simp [HasMem.Mem, Rbmap.Mem]
      exact @Rbtree.mem_of_mem_of_eqv _ _ _ ⟨Rbnode.black_node n_lchild n_val n_rchild, p⟩ _ _ h (eqv_entries _ _ _)

private theorem to_rbtree_mem' [IsStrictWeakOrder α lt] {k : α} {m : Rbmap α β lt} (v : β) :
  (k∈m) → Rbtree.Mem (k, v) m :=
  by 
    intro h 
    cases' to_rbtree_mem h with v' hm 
    apply Rbtree.mem_of_mem_of_eqv hm 
    apply eqv_entries

theorem eq_some_of_to_value_eq_some {e : Option (α × β)} {v : β} : to_value e = some v → ∃ k, e = some (k, v) :=
  by 
    cases' e with val <;> simp [to_value, false_implies_iff]
    ·
      cases val 
      simp 
      intro h 
      subst v 
      constructor 
      rfl

theorem eq_none_of_to_value_eq_none {e : Option (α × β)} : to_value e = none → e = none :=
  by 
    cases e <;> simp [to_value, false_implies_iff]

theorem not_mem_mk_rbmap : ∀ k : α, k ∉ mkRbmap α β lt :=
  by 
    simp [HasMem.Mem, mkRbmap, mkRbtree, Rbmap.Mem]

theorem not_mem_of_empty {m : Rbmap α β lt} (k : α) : m.empty = tt → k ∉ m :=
  by 
    cases' m with n p <;>
      cases n <;> simp [HasMem.Mem, mkRbmap, mkRbtree, Rbmap.Mem, Rbmap.empty, Rbtree.empty, false_implies_iff]

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_of_mem_of_eqv
[is_strict_weak_order α lt]
{m : rbmap α β lt}
{k₁ k₂ : α} : «expr ∈ »(k₁, m) → «expr ≈[ ] »(k₁, lt, k₂) → «expr ∈ »(k₂, m) :=
begin
  intros [ident h₁, ident h₂],
  have [ident h₁] [] [":=", expr to_rbtree_mem h₁],
  cases [expr h₁] ["with", ident v, ident h₁],
  exact [expr to_rbmap_mem (rbtree.mem_of_mem_of_eqv h₁ (eqv_entries_of_eqv_keys v v h₂))]
end

section Decidable

variable [DecidableRel lt]

theorem not_mem_of_find_entry_none [IsStrictWeakOrder α lt] {k : α} {m : Rbmap α β lt} :
  m.find_entry k = none → k ∉ m :=
  by 
    cases' m with t p 
    cases t <;> simp [find_entry]
    ·
      intros 
      simp [HasMem.Mem, Rbmap.Mem]
    all_goals 
      intro h 
      exact Rbtree.not_mem_of_find_none h

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem not_mem_of_find_none
[is_strict_weak_order α lt]
{k : α}
{m : rbmap α β lt} : «expr = »(m.find k, none) → «expr ∉ »(k, m) :=
begin
  simp [] [] [] ["[", expr find, "]"] [] [],
  intro [ident h],
  have [] [] [":=", expr eq_none_of_to_value_eq_none h],
  exact [expr not_mem_of_find_entry_none this]
end

theorem mem_of_find_entry_some [IsStrictWeakOrder α lt] {k₁ : α} {e : α × β} {m : Rbmap α β lt} :
  m.find_entry k₁ = some e → (k₁∈m) :=
  by 
    cases' m with t p 
    cases t <;> simp [find_entry, false_implies_iff]
    all_goals 
      intro h 
      exact Rbtree.mem_of_find_some h

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_of_find_some
[is_strict_weak_order α lt]
{k : α}
{v : β}
{m : rbmap α β lt} : «expr = »(m.find k, some v) → «expr ∈ »(k, m) :=
begin
  simp [] [] [] ["[", expr find, "]"] [] [],
  intro [ident h],
  have [] [] [":=", expr eq_some_of_to_value_eq_some h],
  cases [expr this] ["with", "_", ident he],
  exact [expr mem_of_find_entry_some he]
end

theorem find_entry_eq_find_entry_of_eqv [IsStrictWeakOrder α lt] {m : Rbmap α β lt} {k₁ k₂ : α} :
  k₁ ≈[lt]k₂ → m.find_entry k₁ = m.find_entry k₂ :=
  by 
    intro h 
    cases' m with t p 
    cases t <;> simp [find_entry]
    all_goals 
      apply Rbtree.find_eq_find_of_eqv 
      apply eqv_entries_of_eqv_keys 
      assumption

theorem find_eq_find_of_eqv [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) :
  k₁ ≈[lt]k₂ → m.find k₁ = m.find k₂ :=
  by 
    intro h 
    simp [find]
    apply congr_argₓ 
    apply find_entry_eq_find_entry_of_eqv 
    assumption

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_entry_correct
[is_strict_weak_order α lt]
(k : α)
(m : rbmap α β lt) : «expr ↔ »(«expr ∈ »(k, m), «expr∃ , »((e), «expr ∧ »(«expr = »(m.find_entry k, some e), «expr ≈[ ] »(k, lt, e.1)))) :=
begin
  apply [expr iff.intro]; cases [expr m] ["with", ident t, ident p],
  { intro [ident h],
    have [ident h] [] [":=", expr to_rbtree_mem h],
    cases [expr h] ["with", ident v, ident h₁],
    have [ident hex] [] [":=", expr iff.mp (rbtree.find_correct _ _) h₁],
    cases [expr hex] ["with", ident e, ident h₂],
    existsi [expr e],
    cases [expr t] []; simp [] [] [] ["[", expr find_entry, "]"] [] ["at", "⊢", ident h₂],
    { simp [] [] [] ["[", expr rbtree.find, ",", expr rbnode.find, "]"] [] ["at", ident h₂],
      cases [expr h₂] [] },
    { cases [expr h₂] ["with", ident h₂₁, ident h₂₂],
      split,
      { have [] [] [":=", expr rbtree.find_eq_find_of_eqv ⟨rbnode.red_node t_lchild t_val t_rchild, p⟩ (eqv_entries k v t_val.2)],
        rw ["[", "<-", expr this, "]"] [],
        exact [expr h₂₁] },
      { cases [expr e] [],
        apply [expr eqv_keys_of_eqv_entries h₂₂] } },
    { cases [expr h₂] ["with", ident h₂₁, ident h₂₂],
      split,
      { have [] [] [":=", expr rbtree.find_eq_find_of_eqv ⟨rbnode.black_node t_lchild t_val t_rchild, p⟩ (eqv_entries k v t_val.2)],
        rw ["[", "<-", expr this, "]"] [],
        exact [expr h₂₁] },
      { cases [expr e] [],
        apply [expr eqv_keys_of_eqv_entries h₂₂] } } },
  { intro [ident h],
    cases [expr h] ["with", ident e, ident h],
    cases [expr h] ["with", ident h₁, ident h₂],
    cases [expr t] []; simp [] [] [] ["[", expr find_entry, "]"] [] ["at", ident h₁],
    { contradiction },
    all_goals { exact [expr to_rbmap_mem (rbtree.mem_of_find_some h₁)] } }
end

theorem eqv_of_find_entry_some [IsStrictWeakOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
  m.find_entry k₁ = some (k₂, v) → k₁ ≈[lt]k₂ :=
  by 
    cases' m with t p 
    cases t <;> simp [find_entry, false_implies_iff]
    all_goals 
      intro h 
      exact eqv_keys_of_eqv_entries (Rbtree.eqv_of_find_some h)

theorem eq_of_find_entry_some [IsStrictTotalOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
  m.find_entry k₁ = some (k₂, v) → k₁ = k₂ :=
  fun h =>
    suffices k₁ ≈[lt]k₂ from eq_of_eqv_lt this 
    eqv_of_find_entry_some h

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_correct
[is_strict_weak_order α lt]
(k : α)
(m : rbmap α β lt) : «expr ↔ »(«expr ∈ »(k, m), «expr∃ , »((v), «expr = »(m.find k, some v))) :=
begin
  apply [expr iff.intro],
  { intro [ident h],
    have [] [] [":=", expr iff.mp (find_entry_correct k m) h],
    cases [expr this] ["with", ident e, ident h],
    cases [expr h] ["with", ident h₁, ident h₂],
    existsi [expr e.2],
    simp [] [] [] ["[", expr find, ",", expr h₁, ",", expr to_value, "]"] [] [] },
  { intro [ident h],
    cases [expr h] ["with", ident v, ident h],
    simp [] [] [] ["[", expr find, "]"] [] ["at", ident h],
    have [ident h] [] [":=", expr eq_some_of_to_value_eq_some h],
    cases [expr h] ["with", ident k', ident h],
    have [ident heqv] [] [":=", expr eqv_of_find_entry_some h],
    exact [expr iff.mpr (find_entry_correct k m) ⟨(k', v), ⟨h, heqv⟩⟩] }
end

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem constains_correct
[is_strict_weak_order α lt]
(k : α)
(m : rbmap α β lt) : «expr ↔ »(«expr ∈ »(k, m), «expr = »(m.contains k, tt)) :=
begin
  apply [expr iff.intro],
  { intro [ident h],
    have [ident h] [] [":=", expr iff.mp (find_entry_correct k m) h],
    cases [expr h] ["with", ident e, ident h],
    cases [expr h] ["with", ident h₁, ident h₂],
    simp [] [] [] ["[", expr contains, ",", expr h₁, ",", expr option.is_some, "]"] [] [] },
  { simp [] [] [] ["[", expr contains, "]"] [] [],
    intro [ident h],
    generalize [ident he] [":"] [expr «expr = »(find_entry m k, e)],
    cases [expr e] [],
    { simp [] [] [] ["[", expr he, ",", expr option.is_some, "]"] [] ["at", ident h],
      contradiction },
    { exact [expr mem_of_find_entry_some he] } }
end

theorem mem_insert_of_incomp [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
  ¬lt k₁ k₂ ∧ ¬lt k₂ k₁ → (k₁∈m.insert k₂ v) :=
  fun h => to_rbmap_mem (Rbtree.mem_insert_of_incomp m (eqv_entries_of_eqv_keys v v h))

theorem mem_insert [IsStrictWeakOrder α lt] (k : α) (m : Rbmap α β lt) (v : β) : k∈m.insert k v :=
  to_rbmap_mem (Rbtree.mem_insert (k, v) m)

theorem mem_insert_of_equiv [IsStrictWeakOrder α lt] {k₁ k₂ : α} (m : Rbmap α β lt) (v : β) :
  k₁ ≈[lt]k₂ → (k₁∈m.insert k₂ v) :=
  mem_insert_of_incomp m v

theorem mem_insert_of_mem [IsStrictWeakOrder α lt] {k₁ : α} {m : Rbmap α β lt} (k₂ : α) (v : β) :
  (k₁∈m) → (k₁∈m.insert k₂ v) :=
  fun h => to_rbmap_mem (Rbtree.mem_insert_of_mem (k₂, v) (to_rbtree_mem' v h))

theorem equiv_or_mem_of_mem_insert [IsStrictWeakOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
  (k₁∈m.insert k₂ v) → k₁ ≈[lt]k₂ ∨ (k₁∈m) :=
  fun h =>
    Or.elim (Rbtree.equiv_or_mem_of_mem_insert (to_rbtree_mem' v h)) (fun h => Or.inl (eqv_keys_of_eqv_entries h))
      fun h => Or.inr (to_rbmap_mem h)

theorem incomp_or_mem_of_mem_ins [IsStrictWeakOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
  (k₁∈m.insert k₂ v) → ¬lt k₁ k₂ ∧ ¬lt k₂ k₁ ∨ (k₁∈m) :=
  equiv_or_mem_of_mem_insert

theorem eq_or_mem_of_mem_ins [IsStrictTotalOrder α lt] {k₁ k₂ : α} {v : β} {m : Rbmap α β lt} :
  (k₁∈m.insert k₂ v) → k₁ = k₂ ∨ (k₁∈m) :=
  fun h =>
    suffices k₁ ≈[lt]k₂ ∨ (k₁∈m)by 
      simp [eqv_lt_iff_eq] at this <;> assumption 
    incomp_or_mem_of_mem_ins h

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_entry_insert_of_eqv
[is_strict_weak_order α lt]
(m : rbmap α β lt)
{k₁ k₂ : α}
(v : β) : «expr ≈[ ] »(k₁, lt, k₂) → «expr = »((m.insert k₁ v).find_entry k₂, some (k₁, v)) :=
begin
  intro [ident h],
  generalize [ident h₁] [":"] [expr «expr = »(m.insert k₁ v, m')],
  cases [expr m'] ["with", ident t, ident p],
  cases [expr t] [],
  { have [] [] [":=", expr mem_insert k₁ m v],
    rw ["[", expr h₁, "]"] ["at", ident this],
    apply [expr absurd this],
    apply [expr not_mem_mk_rbmap] },
  all_goals { simp [] [] [] ["[", expr find_entry, "]"] [] [],
    rw ["[", "<-", expr h₁, ",", expr insert, "]"] [],
    apply [expr rbtree.find_insert_of_eqv],
    apply [expr eqv_entries_of_eqv_keys _ _ h] }
end

theorem find_entry_insert [IsStrictWeakOrder α lt] (m : Rbmap α β lt) (k : α) (v : β) :
  (m.insert k v).findEntry k = some (k, v) :=
  find_entry_insert_of_eqv m v (refl k)

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_insert_of_eqv
[is_strict_weak_order α lt]
(m : rbmap α β lt)
{k₁ k₂ : α}
(v : β) : «expr ≈[ ] »(k₁, lt, k₂) → «expr = »((m.insert k₁ v).find k₂, some v) :=
begin
  intro [ident h],
  have [] [] [":=", expr find_entry_insert_of_eqv m v h],
  simp [] [] [] ["[", expr find, ",", expr this, ",", expr to_value, "]"] [] []
end

theorem find_insert [IsStrictWeakOrder α lt] (m : Rbmap α β lt) (k : α) (v : β) : (m.insert k v).find k = some v :=
  find_insert_of_eqv m v (refl k)

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_entry_insert_of_disj
[is_strict_weak_order α lt]
{k₁ k₂ : α}
(m : rbmap α β lt)
(v : β) : «expr ∨ »(lt k₁ k₂, lt k₂ k₁) → «expr = »((m.insert k₁ v).find_entry k₂, m.find_entry k₂) :=
begin
  intro [ident h],
  have [ident h'] [":", expr ∀
   {v₁ v₂ : β}, «expr ∨ »(rbmap_lt lt (k₁, v₁) (k₂, v₂), rbmap_lt lt (k₂, v₂) (k₁, v₁))] [":=", expr λ _ _, h],
  generalize [ident h₁] [":"] [expr «expr = »(m, m₁)],
  generalize [ident h₂] [":"] [expr «expr = »(insert m₁ k₁ v, m₂)],
  rw ["[", "<-", expr h₁, "]"] ["at", ident h₂, "⊢"],
  rw ["[", "<-", expr h₂, "]"] [],
  cases [expr m₁] ["with", ident t₁, ident p₁]; cases [expr t₁] []; cases [expr m₂] ["with", ident t₂, ident p₂]; cases [expr t₂] [],
  { rw ["[", expr h₂, ",", expr h₁, "]"] [] },
  iterate [2] { rw ["[", expr h₂, "]"] [],
    conv [] [] { to_lhs,
      simp [] ["[", expr find_entry, "]"] [] },
    rw ["[", "<-", expr h₂, ",", expr insert, ",", expr rbtree.find_insert_of_disj _ h', ",", expr h₁, "]"] [],
    refl },
  any_goals { simp [] [] [] ["[", expr insert, "]"] [] ["at", ident h₂],
    exact [expr absurd h₂ (rbtree.insert_ne_mk_rbtree m (k₁, v))] },
  any_goals { rw ["[", expr h₂, ",", expr h₁, "]"] [],
    simp [] [] [] ["[", expr find_entry, "]"] [] [],
    rw ["[", "<-", expr h₂, ",", "<-", expr h₁, ",", expr insert, ",", expr rbtree.find_insert_of_disj _ h', "]"] [],
    apply [expr rbtree.find_eq_find_of_eqv],
    apply [expr eqv_entries] }
end

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_entry_insert_of_not_eqv
[is_strict_weak_order α lt]
{k₁ k₂ : α}
(m : rbmap α β lt)
(v : β) : «expr¬ »(«expr ≈[ ] »(k₁, lt, k₂)) → «expr = »((m.insert k₁ v).find_entry k₂, m.find_entry k₂) :=
begin
  intro [ident hn],
  have [ident he] [":", expr «expr ∨ »(lt k₁ k₂, lt k₂ k₁)] [],
  { simp [] [] [] ["[", expr strict_weak_order.equiv, ",", expr decidable.not_and_iff_or_not, ",", expr decidable.not_not_iff, "]"] [] ["at", ident hn],
    assumption },
  apply [expr find_entry_insert_of_disj _ _ he]
end

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_entry_insert_of_ne
[is_strict_total_order α lt]
{k₁ k₂ : α}
(m : rbmap α β lt)
(v : β) : «expr ≠ »(k₁, k₂) → «expr = »((m.insert k₁ v).find_entry k₂, m.find_entry k₂) :=
begin
  intro [ident h],
  have [] [":", expr «expr¬ »(«expr ≈[ ] »(k₁, lt, k₂))] [":=", expr λ h', h (eq_of_eqv_lt h')],
  apply [expr find_entry_insert_of_not_eqv _ _ this]
end

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_insert_of_disj
[is_strict_weak_order α lt]
{k₁ k₂ : α}
(m : rbmap α β lt)
(v : β) : «expr ∨ »(lt k₁ k₂, lt k₂ k₁) → «expr = »((m.insert k₁ v).find k₂, m.find k₂) :=
begin
  intro [ident h],
  have [] [] [":=", expr find_entry_insert_of_disj m v h],
  simp [] [] [] ["[", expr find, ",", expr this, "]"] [] []
end

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_insert_of_not_eqv
[is_strict_weak_order α lt]
{k₁ k₂ : α}
(m : rbmap α β lt)
(v : β) : «expr¬ »(«expr ≈[ ] »(k₁, lt, k₂)) → «expr = »((m.insert k₁ v).find k₂, m.find k₂) :=
begin
  intro [ident h],
  have [] [] [":=", expr find_entry_insert_of_not_eqv m v h],
  simp [] [] [] ["[", expr find, ",", expr this, "]"] [] []
end

-- error in Data.Rbmap.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_insert_of_ne
[is_strict_total_order α lt]
{k₁ k₂ : α}
(m : rbmap α β lt)
(v : β) : «expr ≠ »(k₁, k₂) → «expr = »((m.insert k₁ v).find k₂, m.find k₂) :=
begin
  intro [ident h],
  have [] [] [":=", expr find_entry_insert_of_ne m v h],
  simp [] [] [] ["[", expr find, ",", expr this, "]"] [] []
end

end Decidable

theorem mem_of_min_eq [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} : m.min = some (k, v) → (k∈m) :=
  fun h => to_rbmap_mem (Rbtree.mem_of_min_eq h)

theorem mem_of_max_eq [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} : m.max = some (k, v) → (k∈m) :=
  fun h => to_rbmap_mem (Rbtree.mem_of_max_eq h)

theorem eq_leaf_of_min_eq_none {m : Rbmap α β lt} : m.min = none → m = mkRbmap α β lt :=
  Rbtree.eq_leaf_of_min_eq_none

theorem eq_leaf_of_max_eq_none {m : Rbmap α β lt} : m.max = none → m = mkRbmap α β lt :=
  Rbtree.eq_leaf_of_max_eq_none

theorem min_is_minimal [IsStrictWeakOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
  m.min = some (k, v) → ∀ {k'}, (k'∈m) → k ≈[lt]k' ∨ lt k k' :=
  fun h k' hm =>
    Or.elim (Rbtree.min_is_minimal h (to_rbtree_mem' v hm)) (fun h => Or.inl (eqv_keys_of_eqv_entries h))
      fun h => Or.inr h

theorem max_is_maximal [IsStrictWeakOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
  m.max = some (k, v) → ∀ {k'}, (k'∈m) → k ≈[lt]k' ∨ lt k' k :=
  fun h k' hm =>
    Or.elim (Rbtree.max_is_maximal h (to_rbtree_mem' v hm)) (fun h => Or.inl (eqv_keys_of_eqv_entries h))
      fun h => Or.inr h

theorem min_is_minimal_of_total [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
  m.min = some (k, v) → ∀ {k'}, (k'∈m) → k = k' ∨ lt k k' :=
  fun h k' hm =>
    match min_is_minimal h hm with 
    | Or.inl h => Or.inl (eq_of_eqv_lt h)
    | Or.inr h => Or.inr h

theorem max_is_maximal_of_total [IsStrictTotalOrder α lt] {k : α} {v : β} {m : Rbmap α β lt} :
  m.max = some (k, v) → ∀ {k'}, (k'∈m) → k = k' ∨ lt k' k :=
  fun h k' hm =>
    match max_is_maximal h hm with 
    | Or.inl h => Or.inl (eq_of_eqv_lt h)
    | Or.inr h => Or.inr h

end Rbmap

