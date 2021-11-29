import Mathbin.Data.Finset.Fold 
import Mathbin.Data.Finset.Option 
import Mathbin.Data.Multiset.Lattice 
import Mathbin.Order.OrderDual 
import Mathbin.Order.CompleteLattice

/-!
# Lattice operations on finsets
-/


variable {α β γ : Type _}

namespace Finset

open Multiset OrderDual

/-! ### sup -/


section Sup

variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : Finset β) (f : β → α) : α :=
  s.fold (·⊔·) ⊥ f

variable {s s₁ s₂ : Finset β} {f g : β → α}

theorem sup_def : s.sup f = (s.1.map f).sup :=
  rfl

@[simp]
theorem sup_empty : (∅ : Finset β).sup f = ⊥ :=
  fold_empty

@[simp]
theorem sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b⊔s.sup f :=
  fold_cons h

@[simp]
theorem sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b⊔s.sup f :=
  fold_insert_idem

theorem sup_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) : (s.image f).sup g = s.sup (g ∘ f) :=
  fold_image_idem

@[simp]
theorem sup_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).sup g = s.sup (g ∘ f) :=
  fold_map

@[simp]
theorem sup_singleton {b : β} : ({b} : Finset β).sup f = f b :=
  sup_singleton

theorem sup_union [DecidableEq β] : (s₁ ∪ s₂).sup f = s₁.sup f⊔s₂.sup f :=
  Finset.induction_on s₁
      (by 
        rw [empty_union, sup_empty, bot_sup_eq])$
    fun a s has ih =>
      by 
        rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]

theorem sup_sup : s.sup (f⊔g) = s.sup f⊔s.sup g :=
  by 
    refine' Finset.cons_induction_on s _ fun b t _ h => _
    ·
      rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
    ·
      rw [sup_cons, sup_cons, sup_cons, h]
      exact sup_sup_sup_comm _ _ _ _

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a _ : a ∈ s₂, f a = g a) : s₁.sup f = s₂.sup g :=
  by 
    subst hs <;> exact Finset.fold_congr hfg

@[simp]
theorem sup_le_iff {a : α} : s.sup f ≤ a ↔ ∀ b _ : b ∈ s, f b ≤ a :=
  by 
    apply Iff.trans Multiset.sup_le 
    simp only [Multiset.mem_map, and_imp, exists_imp_distrib]
    exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

@[simp]
theorem sup_bUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
  (s.bUnion t).sup f = s.sup fun x => (t x).sup f :=
  eq_of_forall_ge_iff$
    fun c =>
      by 
        simp [@forall_swap _ β]

theorem sup_const {s : Finset β} (h : s.nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff$ fun b => sup_le_iff.trans h.forall_const

theorem sup_le {a : α} : (∀ b _ : b ∈ s, f b ≤ a) → s.sup f ≤ a :=
  sup_le_iff.2

theorem le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
  sup_le_iff.1 (le_reflₓ _) _ hb

theorem sup_mono_fun {g : β → α} (h : ∀ b _ : b ∈ s, f b ≤ g b) : s.sup f ≤ s.sup g :=
  sup_le fun b hb => le_transₓ (h b hb) (le_sup hb)

theorem sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
  sup_le$ fun b hb => le_sup (h hb)

@[simp]
theorem sup_lt_iff [IsTotal α (· ≤ ·)] {a : α} (ha : ⊥ < a) : s.sup f < a ↔ ∀ b _ : b ∈ s, f b < a :=
  ⟨fun hs b hb => lt_of_le_of_ltₓ (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha)
      fun c t hc =>
        by 
          simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩

@[simp]
theorem le_sup_iff [IsTotal α (· ≤ ·)] {a : α} (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ (b : _)(_ : b ∈ s), a ≤ f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h (not_le_of_lt ha))
      fun c t hc ih =>
        by 
          simpa using
            @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a ≤ f b) (fun h => ⟨c, Or.inl rfl, h⟩)
              fun h =>
                let ⟨b, hb, hle⟩ := ih h
                ⟨b, Or.inr hb, hle⟩,
    fun ⟨b, hb, hle⟩ => trans hle (le_sup hb)⟩

@[simp]
theorem lt_sup_iff [IsTotal α (· ≤ ·)] {a : α} : a < s.sup f ↔ ∃ (b : _)(_ : b ∈ s), a < f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h not_lt_bot)
      fun c t hc ih =>
        by 
          simpa using
            @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a < f b) (fun h => ⟨c, Or.inl rfl, h⟩)
              fun h =>
                let ⟨b, hb, hlt⟩ := ih h
                ⟨b, Or.inr hb, hlt⟩,
    fun ⟨b, hb, hlt⟩ => lt_of_lt_of_leₓ hlt (le_sup hb)⟩

@[simp]
theorem sup_attach (s : Finset β) (f : β → α) : (s.attach.sup fun x => f x) = s.sup f :=
  (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans$ congr_argₓ _ attach_map_val

@[simp]
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id :=
  by 
    refine' (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2$ fun a ha => _)
    obtain rfl | ha' := eq_or_ne a ⊥
    ·
      exact bot_le
    ·
      exact le_sup (mem_erase.2 ⟨ha', ha⟩)

theorem sup_sdiff_right {α β : Type _} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β → α) (a : α) :
  (s.sup fun b => f b \ a) = s.sup f \ a :=
  by 
    refine' Finset.cons_induction_on s _ fun b t _ h => _
    ·
      rw [sup_empty, sup_empty, bot_sdiff]
    ·
      rw [sup_cons, sup_cons, h, sup_sdiff]

theorem comp_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β → α} (g : α → γ)
  (g_sup : ∀ x y, g (x⊔y) = g x⊔g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot
    fun c t hc ih =>
      by 
        rw [sup_cons, sup_cons, g_sup, ih]

theorem comp_sup_eq_sup_comp_of_is_total [IsTotal α (· ≤ ·)] {γ : Type} [SemilatticeSup γ] [OrderBot γ] (g : α → γ)
  (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  comp_sup_eq_sup_comp g mono_g.map_sup bot

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
theorem sup_coe {P : α → Prop} {Pbot : P ⊥} {Psup : ∀ ⦃x y⦄, P x → P y → P (x⊔y)} (t : Finset β)
  (f : β → { x : α // P x }) :
  (@sup _ _ (Subtype.semilatticeSup Psup) (Subtype.orderBot Pbot) t f : α) = t.sup fun x => f x :=
  by 
    rw [comp_sup_eq_sup_comp coeₓ] <;> intros  <;> rfl

@[simp]
theorem sup_to_finset {α β} [DecidableEq β] (s : Finset α) (f : α → Multiset β) :
  (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  comp_sup_eq_sup_comp Multiset.toFinset to_finset_union rfl

theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ :=
  fun n hn => mem_range.2$ Nat.lt_succ_of_leₓ$ le_sup hn

theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  ⟨_, s.subset_range_sup_succ⟩

theorem sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁ a₂ : α, p a₁ → p a₂ → p (a₁⊔a₂))
  (hs : ∀ b _ : b ∈ s, p (f b)) : p (s.sup f) :=
  by 
    induction' s using Finset.cons_induction with c s hc ih
    ·
      exact hb
    ·
      rw [sup_cons]
      apply hp
      ·
        exact hs c (mem_cons.2 (Or.inl rfl))
      ·
        exact ih fun b h => hs b (mem_cons.2 (Or.inr h))

-- error in Data.Finset.Lattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sup_le_of_le_directed
{α : Type*}
[semilattice_sup α]
[order_bot α]
(s : set α)
(hs : s.nonempty)
(hdir : directed_on ((«expr ≤ »)) s)
(t : finset α) : ∀
x «expr ∈ » t, «expr∃ , »((y «expr ∈ » s), «expr ≤ »(x, y)) → «expr∃ , »((x), «expr ∧ »(«expr ∈ »(x, s), «expr ≤ »(t.sup id, x))) :=
begin
  classical,
  apply [expr finset.induction_on t],
  { simpa [] [] ["only"] ["[", expr forall_prop_of_true, ",", expr and_true, ",", expr forall_prop_of_false, ",", expr bot_le, ",", expr not_false_iff, ",", expr sup_empty, ",", expr forall_true_iff, ",", expr not_mem_empty, "]"] [] [] },
  { intros [ident a, ident r, ident har, ident ih, ident h],
    have [ident incs] [":", expr «expr ⊆ »(«expr↑ »(r), «expr↑ »(insert a r))] [],
    by { rw [expr finset.coe_subset] [],
      apply [expr finset.subset_insert] },
    obtain ["⟨", ident x, ",", "⟨", ident hxs, ",", ident hsx_sup, "⟩", "⟩", ":=", expr ih (λ
      x hx, «expr $ »(h x, incs hx))],
    obtain ["⟨", ident y, ",", ident hys, ",", ident hay, "⟩", ":=", expr h a (finset.mem_insert_self a r)],
    obtain ["⟨", ident z, ",", ident hzs, ",", "⟨", ident hxz, ",", ident hyz, "⟩", "⟩", ":=", expr hdir x hxs y hys],
    use ["[", expr z, ",", expr hzs, "]"],
    rw ["[", expr sup_insert, ",", expr id.def, ",", expr _root_.sup_le_iff, "]"] [],
    exact [expr ⟨le_trans hay hyz, le_trans hsx_sup hxz⟩] }
end

theorem sup_mem (s : Set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ x y _ : x ∈ s _ : y ∈ s, x⊔y ∈ s) {ι : Type _} (t : Finset ι)
  (p : ι → α) (h : ∀ i _ : i ∈ t, p i ∈ s) : t.sup p ∈ s :=
  @sup_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h

end Sup

theorem disjoint_sup_right [DistribLattice α] [OrderBot α] {a : α} {s : Finset β} {f : β → α} :
  Disjoint a (s.sup f) ↔ ∀ i _ : i ∈ s, Disjoint a (f i) :=
  ⟨fun h i hi => h.mono_right (le_sup hi), sup_induction disjoint_bot_right fun b c => Disjoint.sup_right⟩

theorem disjoint_sup_left [DistribLattice α] [OrderBot α] {a : α} {s : Finset β} {f : β → α} :
  Disjoint (s.sup f) a ↔ ∀ i _ : i ∈ s, Disjoint (f i) a :=
  by 
    simpRw [@Disjoint.comm _ _ _ _ a]
    exact disjoint_sup_right

theorem sup_eq_supr [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = ⨆(a : _)(_ : a ∈ s), f a :=
  le_antisymmₓ (Finset.sup_le$ fun a ha => le_supr_of_le a$ le_supr _ ha)
    (supr_le$ fun a => supr_le$ fun ha => le_sup ha)

theorem sup_id_eq_Sup [CompleteLattice α] (s : Finset α) : s.sup id = Sup s :=
  by 
    simp [Sup_eq_supr, sup_eq_supr]

theorem sup_eq_Sup_image [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = Sup (f '' s) :=
  by 
    classical 
    rw [←Finset.coe_image, ←sup_id_eq_Sup, sup_image, Function.comp.left_id]

/-! ### inf -/


section Inf

variable [SemilatticeInf α] [OrderTop α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : Finset β) (f : β → α) : α :=
  s.fold (·⊓·) ⊤ f

variable {s s₁ s₂ : Finset β} {f g : β → α}

theorem inf_def : s.inf f = (s.1.map f).inf :=
  rfl

@[simp]
theorem inf_empty : (∅ : Finset β).inf f = ⊤ :=
  fold_empty

@[simp]
theorem inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b⊓s.inf f :=
  @sup_cons (OrderDual α) _ _ _ _ _ _ h

@[simp]
theorem inf_insert [DecidableEq β] {b : β} : (insert b s : Finset β).inf f = f b⊓s.inf f :=
  fold_insert_idem

theorem inf_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) : (s.image f).inf g = s.inf (g ∘ f) :=
  fold_image_idem

@[simp]
theorem inf_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).inf g = s.inf (g ∘ f) :=
  fold_map

@[simp]
theorem inf_singleton {b : β} : ({b} : Finset β).inf f = f b :=
  inf_singleton

theorem inf_union [DecidableEq β] : (s₁ ∪ s₂).inf f = s₁.inf f⊓s₂.inf f :=
  @sup_union (OrderDual α) _ _ _ _ _ _ _

theorem inf_inf : s.inf (f⊓g) = s.inf f⊓s.inf g :=
  @sup_sup (OrderDual α) _ _ _ _ _ _

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a _ : a ∈ s₂, f a = g a) : s₁.inf f = s₂.inf g :=
  by 
    subst hs <;> exact Finset.fold_congr hfg

@[simp]
theorem inf_bUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
  (s.bUnion t).inf f = s.inf fun x => (t x).inf f :=
  @sup_bUnion (OrderDual α) _ _ _ _ _ _ _ _

theorem inf_const {s : Finset β} (h : s.nonempty) (c : α) : (s.inf fun _ => c) = c :=
  @sup_const (OrderDual α) _ _ _ _ h _

theorem le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀ b _ : b ∈ s, a ≤ f b :=
  @sup_le_iff (OrderDual α) _ _ _ _ _ _

theorem inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
  le_inf_iff.1 (le_reflₓ _) _ hb

theorem le_inf {a : α} : (∀ b _ : b ∈ s, a ≤ f b) → a ≤ s.inf f :=
  le_inf_iff.2

theorem inf_mono_fun {g : β → α} (h : ∀ b _ : b ∈ s, f b ≤ g b) : s.inf f ≤ s.inf g :=
  le_inf fun b hb => le_transₓ (inf_le hb) (h b hb)

theorem inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
  le_inf$ fun b hb => inf_le (h hb)

@[simp]
theorem lt_inf_iff [IsTotal α (· ≤ ·)] {a : α} (ha : a < ⊤) : a < s.inf f ↔ ∀ b _ : b ∈ s, a < f b :=
  @sup_lt_iff (OrderDual α) _ _ _ _ _ _ _ ha

@[simp]
theorem inf_le_iff [IsTotal α (· ≤ ·)] {a : α} (ha : a < ⊤) : s.inf f ≤ a ↔ ∃ (b : _)(_ : b ∈ s), f b ≤ a :=
  @le_sup_iff (OrderDual α) _ _ _ _ _ _ _ ha

@[simp]
theorem inf_lt_iff [IsTotal α (· ≤ ·)] {a : α} : s.inf f < a ↔ ∃ (b : _)(_ : b ∈ s), f b < a :=
  @lt_sup_iff (OrderDual α) _ _ _ _ _ _ _

theorem inf_attach (s : Finset β) (f : β → α) : (s.attach.inf fun x => f x) = s.inf f :=
  @sup_attach (OrderDual α) _ _ _ _ _

@[simp]
theorem inf_erase_top [DecidableEq α] (s : Finset α) : (s.erase ⊤).inf id = s.inf id :=
  @sup_erase_bot (OrderDual α) _ _ _ _

theorem sup_sdiff_left {α β : Type _} [BooleanAlgebra α] (s : Finset β) (f : β → α) (a : α) :
  (s.sup fun b => a \ f b) = a \ s.inf f :=
  by 
    refine' Finset.cons_induction_on s _ fun b t _ h => _
    ·
      rw [sup_empty, inf_empty, sdiff_top]
    ·
      rw [sup_cons, inf_cons, h, sdiff_inf]

theorem inf_sdiff_left {α β : Type _} [BooleanAlgebra α] {s : Finset β} (hs : s.nonempty) (f : β → α) (a : α) :
  (s.inf fun b => a \ f b) = a \ s.sup f :=
  by 
    refine' hs.cons_induction (fun b => _) fun b t _ h => _
    ·
      rw [sup_singleton, inf_singleton]
    ·
      rw [sup_cons, inf_cons, h, sdiff_sup]

theorem inf_sdiff_right {α β : Type _} [BooleanAlgebra α] {s : Finset β} (hs : s.nonempty) (f : β → α) (a : α) :
  (s.inf fun b => f b \ a) = s.inf f \ a :=
  by 
    refine' hs.cons_induction (fun b => _) fun b t _ h => _
    ·
      rw [inf_singleton, inf_singleton]
    ·
      rw [inf_cons, inf_cons, h, inf_sdiff]

theorem comp_inf_eq_inf_comp [SemilatticeInf γ] [OrderTop γ] {s : Finset β} {f : β → α} (g : α → γ)
  (g_inf : ∀ x y, g (x⊓y) = g x⊓g y) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  @comp_sup_eq_sup_comp (OrderDual α) _ (OrderDual γ) _ _ _ _ _ _ _ g_inf top

theorem comp_inf_eq_inf_comp_of_is_total [h : IsTotal α (· ≤ ·)] {γ : Type} [SemilatticeInf γ] [OrderTop γ] (g : α → γ)
  (mono_g : Monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  comp_inf_eq_inf_comp g mono_g.map_inf top

/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
theorem inf_coe {P : α → Prop} {Ptop : P ⊤} {Pinf : ∀ ⦃x y⦄, P x → P y → P (x⊓y)} (t : Finset β)
  (f : β → { x : α // P x }) :
  (@inf _ _ (Subtype.semilatticeInf Pinf) (Subtype.orderTop Ptop) t f : α) = t.inf fun x => f x :=
  @sup_coe (OrderDual α) _ _ _ _ Ptop Pinf t f

theorem inf_induction {p : α → Prop} (ht : p ⊤) (hp : ∀ a₁ a₂ : α, p a₁ → p a₂ → p (a₁⊓a₂))
  (hs : ∀ b _ : b ∈ s, p (f b)) : p (s.inf f) :=
  @sup_induction (OrderDual α) _ _ _ _ _ _ ht hp hs

theorem inf_mem (s : Set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ x y _ : x ∈ s _ : y ∈ s, x⊓y ∈ s) {ι : Type _} (t : Finset ι)
  (p : ι → α) (h : ∀ i _ : i ∈ t, p i ∈ s) : t.inf p ∈ s :=
  @inf_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h

end Inf

theorem inf_eq_infi [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = ⨅(a : _)(_ : a ∈ s), f a :=
  @sup_eq_supr _ (OrderDual β) _ _ _

theorem inf_id_eq_Inf [CompleteLattice α] (s : Finset α) : s.inf id = Inf s :=
  @sup_id_eq_Sup (OrderDual α) _ _

theorem inf_eq_Inf_image [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = Inf (f '' s) :=
  @sup_eq_Sup_image _ (OrderDual β) _ _ _

section Sup'

variable [SemilatticeSup α]

theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ a : α, s.sup (coeₓ ∘ f : β → WithBot α) = «expr↑ » a :=
  Exists.impₓ (fun a => Exists.fst) (@le_sup (WithBot α) _ _ _ _ _ _ h (f b) rfl)

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `finset.sup` which does not require `s` nonempty. -/
def sup' (s : Finset β) (H : s.nonempty) (f : β → α) : α :=
  Option.get$
    let ⟨b, hb⟩ := H 
    Option.is_some_iff_exists.2 (sup_of_mem f hb)

variable {s : Finset β} (H : s.nonempty) (f : β → α)

@[simp]
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup (coeₓ ∘ f) :=
  by 
    rw [sup', ←WithBot.some_eq_coe, Option.some_get]

@[simp]
theorem sup'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} : (cons b s hb).sup' h f = f b⊔s.sup' H f :=
  by 
    rw [←WithBot.coe_eq_coe]
    simp only [coe_sup', sup_cons, WithBot.coe_sup]

@[simp]
theorem sup'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} : (insert b s).sup' h f = f b⊔s.sup' H f :=
  by 
    rw [←WithBot.coe_eq_coe]
    simp only [coe_sup', sup_insert, WithBot.coe_sup]

@[simp]
theorem sup'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).sup' h f = f b :=
  rfl

theorem sup'_le {a : α} (hs : ∀ b _ : b ∈ s, f b ≤ a) : s.sup' H f ≤ a :=
  by 
    rw [←WithBot.coe_le_coe, coe_sup']
    exact sup_le fun b h => WithBot.coe_le_coe.2$ hs b h

theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f :=
  by 
    rw [←WithBot.coe_le_coe, coe_sup']
    exact le_sup h

@[simp]
theorem sup'_const (a : α) : (s.sup' H fun b => a) = a :=
  by 
    apply le_antisymmₓ
    ·
      apply sup'_le 
      intros 
      apply le_reflₓ
    ·
      apply le_sup' (fun b => a) H.some_spec

@[simp]
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b _ : b ∈ s, f b ≤ a :=
  Iff.intro (fun h b hb => trans (le_sup' f hb) h) (sup'_le H f)

@[simp]
theorem sup'_lt_iff [IsTotal α (· ≤ ·)] {a : α} : s.sup' H f < a ↔ ∀ b _ : b ∈ s, f b < a :=
  by 
    rw [←WithBot.coe_lt_coe, coe_sup', sup_lt_iff (WithBot.bot_lt_coe a)]
    exact ball_congr fun b hb => WithBot.coe_lt_coe

@[simp]
theorem le_sup'_iff [IsTotal α (· ≤ ·)] {a : α} : a ≤ s.sup' H f ↔ ∃ (b : _)(_ : b ∈ s), a ≤ f b :=
  by 
    rw [←WithBot.coe_le_coe, coe_sup', le_sup_iff (WithBot.bot_lt_coe a)]
    exact bex_congr fun b hb => WithBot.coe_le_coe

@[simp]
theorem lt_sup'_iff [IsTotal α (· ≤ ·)] {a : α} : a < s.sup' H f ↔ ∃ (b : _)(_ : b ∈ s), a < f b :=
  by 
    rw [←WithBot.coe_lt_coe, coe_sup', lt_sup_iff]
    exact bex_congr fun b hb => WithBot.coe_lt_coe

theorem sup'_bUnion [DecidableEq β] {s : Finset γ} (Hs : s.nonempty) {t : γ → Finset β} (Ht : ∀ b, (t b).Nonempty) :
  (s.bUnion t).sup' (Hs.bUnion fun b _ => Ht b) f = s.sup' Hs fun b => (t b).sup' (Ht b) f :=
  eq_of_forall_ge_iff$
    fun c =>
      by 
        simp [@forall_swap _ β]

theorem comp_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.nonempty) {f : β → α} (g : α → γ)
  (g_sup : ∀ x y, g (x⊔y) = g x⊔g y) : g (s.sup' H f) = s.sup' H (g ∘ f) :=
  by 
    rw [←WithBot.coe_eq_coe, coe_sup']
    let g' : WithBot α → WithBot γ := WithBot.recBotCoe ⊥ fun x => «expr↑ » (g x)
    show g' («expr↑ » (s.sup' H f)) = s.sup fun a => g' («expr↑ » (f a))
    rw [coe_sup']
    refine' comp_sup_eq_sup_comp g' _ rfl 
    intro f₁ f₂ 
    cases f₁
    ·
      rw [WithBot.none_eq_bot, bot_sup_eq]
      exact bot_sup_eq.symm
    ·
      cases f₂ 
      rfl 
      exact congr_argₓ coeₓ (g_sup f₁ f₂)

theorem sup'_induction {p : α → Prop} (hp : ∀ a₁ a₂ : α, p a₁ → p a₂ → p (a₁⊔a₂)) (hs : ∀ b _ : b ∈ s, p (f b)) :
  p (s.sup' H f) :=
  by 
    show @WithBot.recBotCoe α (fun _ => Prop) True p («expr↑ » (s.sup' H f))
    rw [coe_sup']
    refine' sup_induction trivialₓ _ hs 
    intro a₁ a₂ h₁ h₂ 
    cases a₁
    ·
      rw [WithBot.none_eq_bot, bot_sup_eq]
      exact h₂
    ·
      cases a₂ 
      exact h₁ 
      exact hp a₁ a₂ h₁ h₂

theorem exists_mem_eq_sup' [IsTotal α (· ≤ ·)] : ∃ b, b ∈ s ∧ s.sup' H f = f b :=
  by 
    induction' s using Finset.cons_induction with c s hc ih
    ·
      exact False.elim (not_nonempty_empty H)
    ·
      rcases s.eq_empty_or_nonempty with (rfl | hs)
      ·
        exact ⟨c, mem_singleton_self c, rfl⟩
      ·
        rcases ih hs with ⟨b, hb, h'⟩
        rw [sup'_cons hs, h']
        cases' total_of (· ≤ ·) (f b) (f c) with h h
        ·
          exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
        ·
          exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩

theorem sup'_mem (s : Set α) (w : ∀ x y _ : x ∈ s _ : y ∈ s, x⊔y ∈ s) {ι : Type _} (t : Finset ι) (H : t.nonempty)
  (p : ι → α) (h : ∀ i _ : i ∈ t, p i ∈ s) : t.sup' H p ∈ s :=
  sup'_induction H p w h

-- error in Data.Finset.Lattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[congr]
theorem sup'_congr
{t : finset β}
{f g : β → α}
(h₁ : «expr = »(s, t))
(h₂ : ∀ x «expr ∈ » s, «expr = »(f x, g x)) : «expr = »(s.sup' H f, t.sup' «expr ▸ »(h₁, H) g) :=
begin
  subst [expr s],
  refine [expr eq_of_forall_ge_iff (λ c, _)],
  simp [] [] ["only"] ["[", expr sup'_le_iff, ",", expr h₂, "]"] [] [] { contextual := tt }
end

end Sup'

section Inf'

variable [SemilatticeInf α]

theorem inf_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ a : α, s.inf (coeₓ ∘ f : β → WithTop α) = «expr↑ » a :=
  @sup_of_mem (OrderDual α) _ _ _ f _ h

/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `finset.inf` which does not require `s` nonempty. -/
def inf' (s : Finset β) (H : s.nonempty) (f : β → α) : α :=
  @sup' (OrderDual α) _ _ s H f

variable {s : Finset β} (H : s.nonempty) (f : β → α)

@[simp]
theorem coe_inf' : ((s.inf' H f : α) : WithTop α) = s.inf (coeₓ ∘ f) :=
  @coe_sup' (OrderDual α) _ _ _ H f

@[simp]
theorem inf'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} : (cons b s hb).inf' h f = f b⊓s.inf' H f :=
  @sup'_cons (OrderDual α) _ _ _ H f _ _ _

@[simp]
theorem inf'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} : (insert b s).inf' h f = f b⊓s.inf' H f :=
  @sup'_insert (OrderDual α) _ _ _ H f _ _ _

@[simp]
theorem inf'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).inf' h f = f b :=
  rfl

theorem le_inf' {a : α} (hs : ∀ b _ : b ∈ s, a ≤ f b) : a ≤ s.inf' H f :=
  @sup'_le (OrderDual α) _ _ _ H f _ hs

theorem inf'_le {b : β} (h : b ∈ s) : s.inf' ⟨b, h⟩ f ≤ f b :=
  @le_sup' (OrderDual α) _ _ _ f _ h

@[simp]
theorem inf'_const (a : α) : (s.inf' H fun b => a) = a :=
  @sup'_const (OrderDual α) _ _ _ _ _

@[simp]
theorem le_inf'_iff {a : α} : a ≤ s.inf' H f ↔ ∀ b _ : b ∈ s, a ≤ f b :=
  @sup'_le_iff (OrderDual α) _ _ _ H f _

@[simp]
theorem lt_inf'_iff [IsTotal α (· ≤ ·)] {a : α} : a < s.inf' H f ↔ ∀ b _ : b ∈ s, a < f b :=
  @sup'_lt_iff (OrderDual α) _ _ _ H f _ _

@[simp]
theorem inf'_le_iff [IsTotal α (· ≤ ·)] {a : α} : s.inf' H f ≤ a ↔ ∃ (b : _)(_ : b ∈ s), f b ≤ a :=
  @le_sup'_iff (OrderDual α) _ _ _ H f _ _

@[simp]
theorem inf'_lt_iff [IsTotal α (· ≤ ·)] {a : α} : s.inf' H f < a ↔ ∃ (b : _)(_ : b ∈ s), f b < a :=
  @lt_sup'_iff (OrderDual α) _ _ _ H f _ _

theorem inf'_bUnion [DecidableEq β] {s : Finset γ} (Hs : s.nonempty) {t : γ → Finset β} (Ht : ∀ b, (t b).Nonempty) :
  (s.bUnion t).inf' (Hs.bUnion fun b _ => Ht b) f = s.inf' Hs fun b => (t b).inf' (Ht b) f :=
  @sup'_bUnion (OrderDual α) _ _ _ _ _ _ Hs _ Ht

theorem comp_inf'_eq_inf'_comp [SemilatticeInf γ] {s : Finset β} (H : s.nonempty) {f : β → α} (g : α → γ)
  (g_inf : ∀ x y, g (x⊓y) = g x⊓g y) : g (s.inf' H f) = s.inf' H (g ∘ f) :=
  @comp_sup'_eq_sup'_comp (OrderDual α) _ (OrderDual γ) _ _ _ H f g g_inf

theorem inf'_induction {p : α → Prop} (hp : ∀ a₁ a₂ : α, p a₁ → p a₂ → p (a₁⊓a₂)) (hs : ∀ b _ : b ∈ s, p (f b)) :
  p (s.inf' H f) :=
  @sup'_induction (OrderDual α) _ _ _ H f _ hp hs

theorem exists_mem_eq_inf' [IsTotal α (· ≤ ·)] : ∃ b, b ∈ s ∧ s.inf' H f = f b :=
  @exists_mem_eq_sup' (OrderDual α) _ _ _ H f _

theorem inf'_mem (s : Set α) (w : ∀ x y _ : x ∈ s _ : y ∈ s, x⊓y ∈ s) {ι : Type _} (t : Finset ι) (H : t.nonempty)
  (p : ι → α) (h : ∀ i _ : i ∈ t, p i ∈ s) : t.inf' H p ∈ s :=
  inf'_induction H p w h

@[congr]
theorem inf'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x _ : x ∈ s, f x = g x) :
  s.inf' H f = t.inf' (h₁ ▸ H) g :=
  @sup'_congr (OrderDual α) _ _ _ H _ _ _ h₁ h₂

end Inf'

section Sup

variable [SemilatticeSup α] [OrderBot α]

theorem sup'_eq_sup {s : Finset β} (H : s.nonempty) (f : β → α) : s.sup' H f = s.sup f :=
  le_antisymmₓ (sup'_le H f fun b => le_sup) (sup_le fun b => le_sup' f)

theorem sup_closed_of_sup_closed {s : Set α} (t : Finset α) (htne : t.nonempty) (h_subset : «expr↑ » t ⊆ s)
  (h : ∀ ⦃a b⦄, a ∈ s → b ∈ s → a⊔b ∈ s) : t.sup id ∈ s :=
  sup'_eq_sup htne id ▸ sup'_induction _ _ h h_subset

theorem exists_mem_eq_sup [IsTotal α (· ≤ ·)] (s : Finset β) (h : s.nonempty) (f : β → α) :
  ∃ b, b ∈ s ∧ s.sup f = f b :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

theorem inf'_eq_inf {s : Finset β} (H : s.nonempty) (f : β → α) : s.inf' H f = s.inf f :=
  @sup'_eq_sup (OrderDual α) _ _ _ _ H f

theorem inf_closed_of_inf_closed {s : Set α} (t : Finset α) (htne : t.nonempty) (h_subset : «expr↑ » t ⊆ s)
  (h : ∀ ⦃a b⦄, a ∈ s → b ∈ s → a⊓b ∈ s) : t.inf id ∈ s :=
  @sup_closed_of_sup_closed (OrderDual α) _ _ _ t htne h_subset h

theorem exists_mem_eq_inf [IsTotal α (· ≤ ·)] (s : Finset β) (h : s.nonempty) (f : β → α) :
  ∃ a, a ∈ s ∧ s.inf f = f a :=
  @exists_mem_eq_sup (OrderDual α) _ _ _ _ _ h f

end Inf

section Sup

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)] [∀ b : β, OrderBot (C b)]

@[simp]
protected theorem sup_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) : s.sup f b = s.sup fun a => f a b :=
  comp_sup_eq_sup_comp (fun x : ∀ b : β, C b => x b) (fun i j => rfl) rfl

end Sup

section Inf

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)] [∀ b : β, OrderTop (C b)]

@[simp]
protected theorem inf_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) : s.inf f b = s.inf fun a => f a b :=
  @Finset.sup_apply _ _ (fun b => OrderDual (C b)) _ _ s f b

end Inf

section Sup'

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)]

@[simp]
protected theorem sup'_apply {s : Finset α} (H : s.nonempty) (f : α → ∀ b : β, C b) (b : β) :
  s.sup' H f b = s.sup' H fun a => f a b :=
  comp_sup'_eq_sup'_comp H (fun x : ∀ b : β, C b => x b) fun i j => rfl

end Sup'

section Inf'

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)]

@[simp]
protected theorem inf'_apply {s : Finset α} (H : s.nonempty) (f : α → ∀ b : β, C b) (b : β) :
  s.inf' H f b = s.inf' H fun a => f a b :=
  @Finset.sup'_apply _ _ (fun b => OrderDual (C b)) _ _ H f b

end Inf'

/-! ### max and min of finite sets -/


section MaxMin

variable [LinearOrderₓ α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max : Finset α → Option α :=
  fold (Option.liftOrGet max) none some

theorem max_eq_sup_with_bot (s : Finset α) : s.max = @sup (WithBot α) α _ _ s some :=
  rfl

@[simp]
theorem max_empty : (∅ : Finset α).max = none :=
  rfl

@[simp]
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = Option.liftOrGet max (some a) s.max :=
  fold_insert_idem

@[simp]
theorem max_singleton {a : α} : Finset.max {a} = some a :=
  by 
    rw [←insert_emptyc_eq]
    exact max_insert

theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.max :=
  (@le_sup (WithBot α) _ _ _ _ _ _ h _ rfl).imp$ fun b => Exists.fst

theorem max_of_nonempty {s : Finset α} (h : s.nonempty) : ∃ a, a ∈ s.max :=
  let ⟨a, ha⟩ := h 
  max_of_mem ha

theorem max_eq_none {s : Finset α} : s.max = none ↔ s = ∅ :=
  ⟨fun h =>
      s.eq_empty_or_nonempty.elim id
        fun H =>
          let ⟨a, ha⟩ := max_of_nonempty H 
          by 
            rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ max_empty⟩

theorem mem_of_max {s : Finset α} : ∀ {a : α}, a ∈ s.max → a ∈ s :=
  Finset.induction_on s
    (fun _ H =>
      by 
        cases H)
    fun b s _ ih : ∀ {a}, a ∈ s.max → a ∈ s a h : a ∈ (insert b s).max =>
      by 
        byCases' p : b = a
        ·
          induction p 
          exact mem_insert_self b s
        ·
          cases' Option.lift_or_get_choice max_choice (some b) s.max with q q <;> rw [max_insert, q] at h
          ·
            cases h 
            cases p rfl
          ·
            exact mem_insert_of_mem (ih h)

theorem le_max_of_mem {s : Finset α} {a b : α} (h₁ : a ∈ s) (h₂ : b ∈ s.max) : a ≤ b :=
  by 
    rcases@le_sup (WithBot α) _ _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩ <;> cases h₂.symm.trans hb <;> assumption

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min : Finset α → Option α :=
  fold (Option.liftOrGet min) none some

theorem min_eq_inf_with_top (s : Finset α) : s.min = @inf (WithTop α) α _ _ s some :=
  rfl

@[simp]
theorem min_empty : (∅ : Finset α).min = none :=
  rfl

@[simp]
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = Option.liftOrGet min (some a) s.min :=
  fold_insert_idem

@[simp]
theorem min_singleton {a : α} : Finset.min {a} = some a :=
  by 
    rw [←insert_emptyc_eq]
    exact min_insert

theorem min_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.min :=
  (@inf_le (WithTop α) _ _ _ _ _ _ h _ rfl).imp$ fun b => Exists.fst

theorem min_of_nonempty {s : Finset α} (h : s.nonempty) : ∃ a, a ∈ s.min :=
  let ⟨a, ha⟩ := h 
  min_of_mem ha

theorem min_eq_none {s : Finset α} : s.min = none ↔ s = ∅ :=
  ⟨fun h =>
      s.eq_empty_or_nonempty.elim id
        fun H =>
          let ⟨a, ha⟩ := min_of_nonempty H 
          by 
            rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ min_empty⟩

theorem mem_of_min {s : Finset α} : ∀ {a : α}, a ∈ s.min → a ∈ s :=
  @mem_of_max (OrderDual α) _ s

theorem min_le_of_mem {s : Finset α} {a b : α} (h₁ : b ∈ s) (h₂ : a ∈ s.min) : a ≤ b :=
  by 
    rcases@inf_le (WithTop α) _ _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩ <;> cases h₂.symm.trans hb <;> assumption

/-- Given a nonempty finset `s` in a linear order `α `, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `option α`. -/
def min' (s : Finset α) (H : s.nonempty) : α :=
  @Option.get _ s.min$
    let ⟨k, hk⟩ := H 
    let ⟨b, hb⟩ := min_of_mem hk 
    by 
      simp  at hb <;> simp [hb]

/-- Given a nonempty finset `s` in a linear order `α `, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `option α`. -/
def max' (s : Finset α) (H : s.nonempty) : α :=
  @Option.get _ s.max$
    let ⟨k, hk⟩ := H 
    let ⟨b, hb⟩ := max_of_mem hk 
    by 
      simp  at hb <;> simp [hb]

variable (s : Finset α) (H : s.nonempty)

theorem min'_mem : s.min' H ∈ s :=
  mem_of_min$
    by 
      simp [min']

theorem min'_le x (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x :=
  min_le_of_mem H2$ Option.get_mem _

theorem le_min' x (H2 : ∀ y _ : y ∈ s, x ≤ y) : x ≤ s.min' H :=
  H2 _$ min'_mem _ _

theorem is_least_min' : IsLeast («expr↑ » s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩

@[simp]
theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y _ : y ∈ s, x ≤ y :=
  le_is_glb_iff (is_least_min' s H).IsGlb

/-- `{a}.min' _` is `a`. -/
@[simp]
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a :=
  by 
    simp [min']

theorem max'_mem : s.max' H ∈ s :=
  mem_of_max$
    by 
      simp [max']

theorem le_max' x (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_mem H2$ Option.get_mem _

theorem max'_le x (H2 : ∀ y _ : y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _$ max'_mem _ _

theorem is_greatest_max' : IsGreatest («expr↑ » s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩

@[simp]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y _ : y ∈ s, y ≤ x :=
  is_lub_le_iff (is_greatest_max' s H).IsLub

@[simp]
theorem max'_lt_iff {x} : s.max' H < x ↔ ∀ y _ : y ∈ s, y < x :=
  ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _$ s.max'_mem _⟩

@[simp]
theorem lt_min'_iff {x} : x < s.min' H ↔ ∀ y _ : y ∈ s, x < y :=
  @max'_lt_iff (OrderDual α) _ _ H _

theorem max'_eq_sup' : s.max' H = s.sup' H id :=
  eq_of_forall_ge_iff$ fun a => (max'_le_iff _ _).trans (sup'_le_iff _ _).symm

theorem min'_eq_inf' : s.min' H = s.inf' H id :=
  @max'_eq_sup' (OrderDual α) _ s H

/-- `{a}.max' _` is `a`. -/
@[simp]
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a :=
  by 
    simp [max']

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) : s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  is_glb_lt_is_lub_of_ne (s.is_least_min' _).IsGlb (s.is_greatest_max' _).IsLub H1 H2 H3

/--
If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
  s.min' (Finset.card_pos.mp$ lt_transₓ zero_lt_one h₂) < s.max' (Finset.card_pos.mp$ lt_transₓ zero_lt_one h₂) :=
  by 
    rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
    exact s.min'_lt_max' ha hb hab

theorem max'_eq_of_dual_min' {s : Finset α} (hs : s.nonempty) :
  max' s hs = of_dual (min' (image to_dual s) (nonempty.image hs to_dual)) :=
  by 
    rw [of_dual, to_dual, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, id.def]
    simpRw [@image_id (OrderDual α) (s : Finset (OrderDual α))]
    rfl

theorem min'_eq_of_dual_max' {s : Finset α} (hs : s.nonempty) :
  min' s hs = of_dual (max' (image to_dual s) (nonempty.image hs to_dual)) :=
  by 
    rw [of_dual, to_dual, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, id.def]
    simpRw [@image_id (OrderDual α) (s : Finset (OrderDual α))]
    rfl

@[simp]
theorem of_dual_max_eq_min_of_dual {a b : α} : of_dual (max a b) = min (of_dual a) (of_dual b) :=
  rfl

@[simp]
theorem of_dual_min_eq_max_of_dual {a b : α} : of_dual (min a b) = max (of_dual a) (of_dual b) :=
  rfl

theorem max'_subset {s t : Finset α} (H : s.nonempty) (hst : s ⊆ t) : s.max' H ≤ t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))

theorem min'_subset {s t : Finset α} (H : s.nonempty) (hst : s ⊆ t) : t.min' (H.mono hst) ≤ s.min' H :=
  min'_le _ _ (hst (s.min'_mem H))

theorem max'_insert (a : α) (s : Finset α) (H : s.nonempty) :
  (insert a s).max' (s.insert_nonempty a) = max (s.max' H) a :=
  (is_greatest_max' _ _).unique$
    by 
      rw [coe_insert, max_commₓ]
      exact (is_greatest_max' _ _).insert _

theorem min'_insert (a : α) (s : Finset α) (H : s.nonempty) :
  (insert a s).min' (s.insert_nonempty a) = min (s.min' H) a :=
  (is_least_min' _ _).unique$
    by 
      rw [coe_insert, min_commₓ]
      exact (is_least_min' _ _).insert _

theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.max' H)) : a < s.max' H :=
  lt_of_le_of_neₓ (le_max' _ _ (mem_of_mem_erase ha))$ ne_of_mem_of_not_mem ha$ not_mem_erase _ _

theorem min'_lt_of_mem_erase_min' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.min' H)) : s.min' H < a :=
  @lt_max'_of_mem_erase_max' (OrderDual α) _ s H _ a ha

@[simp]
theorem max'_image [LinearOrderₓ β] {f : α → β} (hf : Monotone f) (s : Finset α) (h : (s.image f).Nonempty) :
  (s.image f).max' h = f (s.max' ((nonempty.image_iff f).mp h)) :=
  by 
    refine' le_antisymmₓ (max'_le _ _ _ fun y hy => _) (le_max' _ _ (mem_image.mpr ⟨_, max'_mem _ _, rfl⟩))
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy 
    exact hf (le_max' _ _ hx)

@[simp]
theorem min'_image [LinearOrderₓ β] {f : α → β} (hf : Monotone f) (s : Finset α) (h : (s.image f).Nonempty) :
  (s.image f).min' h = f (s.min' ((nonempty.image_iff f).mp h)) :=
  by 
    refine' le_antisymmₓ (min'_le _ _ (mem_image.mpr ⟨_, min'_mem _ _, rfl⟩)) (le_min' _ _ _ fun y hy => _)
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy 
    exact hf (min'_le _ _ hx)

-- error in Data.Finset.Lattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_eliminator]
theorem induction_on_max
[decidable_eq α]
{p : finset α → exprProp()}
(s : finset α)
(h0 : p «expr∅»())
(step : ∀ a s, ∀ x «expr ∈ » s, «expr < »(x, a) → p s → p (insert a s)) : p s :=
begin
  induction [expr s] ["using", ident finset.strong_induction_on] ["with", ident s, ident ihs] [],
  rcases [expr s.eq_empty_or_nonempty, "with", ident rfl, "|", ident hne],
  { exact [expr h0] },
  { have [ident H] [":", expr «expr ∈ »(s.max' hne, s)] [],
    from [expr max'_mem s hne],
    rw ["<-", expr insert_erase H] [],
    exact [expr step _ _ (λ x, s.lt_max'_of_mem_erase_max' hne) «expr $ »(ihs _, erase_ssubset H)] }
end

/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_eliminator]
theorem induction_on_min [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
  (step : ∀ a s, (∀ x _ : x ∈ s, a < x) → p s → p (insert a s)) : p s :=
  @induction_on_max (OrderDual α) _ _ _ s h0 step

end MaxMin

section ExistsMaxMin

variable [LinearOrderₓ α]

theorem exists_max_image (s : Finset β) (f : β → α) (h : s.nonempty) :
  ∃ (x : _)(_ : x ∈ s), ∀ x' _ : x' ∈ s, f x' ≤ f x :=
  by 
    cases' max_of_nonempty (h.image f) with y hy 
    rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
    exact ⟨x, hx, fun x' hx' => le_max_of_mem (mem_image_of_mem f hx') hy⟩

theorem exists_min_image (s : Finset β) (f : β → α) (h : s.nonempty) :
  ∃ (x : _)(_ : x ∈ s), ∀ x' _ : x' ∈ s, f x ≤ f x' :=
  @exists_max_image (OrderDual α) β _ s f h

end ExistsMaxMin

end Finset

namespace Multiset

-- error in Data.Finset.Lattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem count_sup
[decidable_eq β]
(s : finset α)
(f : α → multiset β)
(b : β) : «expr = »(count b (s.sup f), s.sup (λ a, count b (f a))) :=
begin
  letI [] [] [":=", expr classical.dec_eq α],
  refine [expr s.induction _ _],
  { exact [expr count_zero _] },
  { assume [binders (i s his ih)],
    rw ["[", expr finset.sup_insert, ",", expr sup_eq_union, ",", expr count_union, ",", expr finset.sup_insert, ",", expr ih, "]"] [],
    refl }
end

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Multiset β} {x : β} :
  x ∈ s.sup f ↔ ∃ (v : _)(_ : v ∈ s), x ∈ f v :=
  by 
    classical 
    apply s.induction_on
    ·
      simp 
    ·
      intro a s has hxs 
      rw [Finset.sup_insert, Multiset.sup_eq_union, Multiset.mem_union]
      split 
      ·
        intro hxi 
        cases' hxi with hf hf
        ·
          refine' ⟨a, _, hf⟩
          simp only [true_orₓ, eq_self_iff_true, Finset.mem_insert]
        ·
          rcases hxs.mp hf with ⟨v, hv, hfv⟩
          refine' ⟨v, _, hfv⟩
          simp only [hv, or_trueₓ, Finset.mem_insert]
      ·
        rintro ⟨v, hv, hfv⟩
        rw [Finset.mem_insert] at hv 
        rcases hv with (rfl | hv)
        ·
          exact Or.inl hfv
        ·
          refine' Or.inr (hxs.mpr ⟨v, hv, hfv⟩)

end Multiset

namespace Finset

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Finset β} {x : β} :
  x ∈ s.sup f ↔ ∃ (v : _)(_ : v ∈ s), x ∈ f v :=
  by 
    change _ ↔ ∃ (v : _)(_ : v ∈ s), x ∈ (f v).val 
    rw [←Multiset.mem_sup, ←Multiset.mem_to_finset, sup_to_finset]
    simpRw [val_to_finset]

theorem sup_eq_bUnion {α β} [DecidableEq β] (s : Finset α) (t : α → Finset β) : s.sup t = s.bUnion t :=
  by 
    ext 
    rw [mem_sup, mem_bUnion]

@[simp]
theorem sup_singleton' [DecidableEq α] (s : Finset α) : s.sup singleton = s :=
  by 
    refine' (Finset.sup_le$ fun a => _).antisymm fun a ha => mem_sup.2 ⟨a, ha, mem_singleton_self a⟩
    exact singleton_subset_iff.2

end Finset

section Lattice

variable {ι : Type _} {ι' : Sort _} [CompleteLattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
theorem supr_eq_supr_finset (s : ι → α) : (⨆i, s i) = ⨆t : Finset ι, ⨆(i : _)(_ : i ∈ t), s i :=
  by 
    classical 
    exact
      le_antisymmₓ
        (supr_le$
          fun b =>
            le_supr_of_le {b}$
              le_supr_of_le b$
                le_supr_of_le
                    (by 
                      simp )$
                  le_reflₓ _)
        (supr_le$ fun t => supr_le$ fun b => supr_le$ fun hb => le_supr _ _)

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem supr_eq_supr_finset' (s : ι' → α) : (⨆i, s i) = ⨆t : Finset (Plift ι'), ⨆(i : _)(_ : i ∈ t), s (Plift.down i) :=
  by 
    rw [←supr_eq_supr_finset, ←equiv.plift.surjective.supr_comp] <;> rfl

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
theorem infi_eq_infi_finset (s : ι → α) : (⨅i, s i) = ⨅t : Finset ι, ⨅(i : _)(_ : i ∈ t), s i :=
  @supr_eq_supr_finset (OrderDual α) _ _ _

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem infi_eq_infi_finset' (s : ι' → α) : (⨅i, s i) = ⨅t : Finset (Plift ι'), ⨅(i : _)(_ : i ∈ t), s (Plift.down i) :=
  @supr_eq_supr_finset' (OrderDual α) _ _ _

end Lattice

namespace Set

variable {ι : Type _} {ι' : Sort _}

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
theorem Union_eq_Union_finset (s : ι → Set α) : (⋃i, s i) = ⋃t : Finset ι, ⋃(i : _)(_ : i ∈ t), s i :=
  supr_eq_supr_finset s

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
theorem Union_eq_Union_finset' (s : ι' → Set α) :
  (⋃i, s i) = ⋃t : Finset (Plift ι'), ⋃(i : _)(_ : i ∈ t), s (Plift.down i) :=
  supr_eq_supr_finset' s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
theorem Inter_eq_Inter_finset (s : ι → Set α) : (⋂i, s i) = ⋂t : Finset ι, ⋂(i : _)(_ : i ∈ t), s i :=
  infi_eq_infi_finset s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
theorem Inter_eq_Inter_finset' (s : ι' → Set α) :
  (⋂i, s i) = ⋂t : Finset (Plift ι'), ⋂(i : _)(_ : i ∈ t), s (Plift.down i) :=
  infi_eq_infi_finset' s

end Set

namespace Finset

open Function

/-! ### Interaction with big lattice/set operations -/


section Lattice

theorem supr_coe [HasSupₓ β] (f : α → β) (s : Finset α) :
  (⨆(x : _)(_ : x ∈ («expr↑ » s : Set α)), f x) = ⨆(x : _)(_ : x ∈ s), f x :=
  rfl

theorem infi_coe [HasInfₓ β] (f : α → β) (s : Finset α) :
  (⨅(x : _)(_ : x ∈ («expr↑ » s : Set α)), f x) = ⨅(x : _)(_ : x ∈ s), f x :=
  rfl

variable [CompleteLattice β]

theorem supr_singleton (a : α) (s : α → β) : (⨆(x : _)(_ : x ∈ ({a} : Finset α)), s x) = s a :=
  by 
    simp 

theorem infi_singleton (a : α) (s : α → β) : (⨅(x : _)(_ : x ∈ ({a} : Finset α)), s x) = s a :=
  by 
    simp 

theorem supr_option_to_finset (o : Option α) (f : α → β) :
  (⨆(x : _)(_ : x ∈ o.to_finset), f x) = ⨆(x : _)(_ : x ∈ o), f x :=
  by 
    simp 

theorem infi_option_to_finset (o : Option α) (f : α → β) :
  (⨅(x : _)(_ : x ∈ o.to_finset), f x) = ⨅(x : _)(_ : x ∈ o), f x :=
  @supr_option_to_finset _ (OrderDual β) _ _ _

variable [DecidableEq α]

theorem supr_union {f : α → β} {s t : Finset α} :
  (⨆(x : _)(_ : x ∈ s ∪ t), f x) = (⨆(x : _)(_ : x ∈ s), f x)⊔⨆(x : _)(_ : x ∈ t), f x :=
  by 
    simp [supr_or, supr_sup_eq]

theorem infi_union {f : α → β} {s t : Finset α} :
  (⨅(x : _)(_ : x ∈ s ∪ t), f x) = (⨅(x : _)(_ : x ∈ s), f x)⊓⨅(x : _)(_ : x ∈ t), f x :=
  @supr_union α (OrderDual β) _ _ _ _ _

theorem supr_insert (a : α) (s : Finset α) (t : α → β) :
  (⨆(x : _)(_ : x ∈ insert a s), t x) = t a⊔⨆(x : _)(_ : x ∈ s), t x :=
  by 
    rw [insert_eq]
    simp only [supr_union, Finset.supr_singleton]

theorem infi_insert (a : α) (s : Finset α) (t : α → β) :
  (⨅(x : _)(_ : x ∈ insert a s), t x) = t a⊓⨅(x : _)(_ : x ∈ s), t x :=
  @supr_insert α (OrderDual β) _ _ _ _ _

theorem supr_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
  (⨆(x : _)(_ : x ∈ s.image f), g x) = ⨆(y : _)(_ : y ∈ s), g (f y) :=
  by 
    rw [←supr_coe, coe_image, supr_image, supr_coe]

theorem sup_finset_image {β γ : Type _} [SemilatticeSup β] [OrderBot β] (f : γ → α) (g : α → β) (s : Finset γ) :
  (s.image f).sup g = s.sup (g ∘ f) :=
  by 
    classical 
    induction' s using Finset.induction_on with a s' ha ih <;> simp 

theorem infi_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
  (⨅(x : _)(_ : x ∈ s.image f), g x) = ⨅(y : _)(_ : y ∈ s), g (f y) :=
  by 
    rw [←infi_coe, coe_image, infi_image, infi_coe]

theorem supr_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨆(i : _)(_ : i ∈ insert x t), Function.update f x s i) = s⊔⨆(i : _)(_ : i ∈ t), f i :=
  by 
    simp only [Finset.supr_insert, update_same]
    rcongr i hi 
    apply update_noteq 
    rintro rfl 
    exact hx hi

theorem infi_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨅(i : _)(_ : i ∈ insert x t), update f x s i) = s⊓⨅(i : _)(_ : i ∈ t), f i :=
  @supr_insert_update α (OrderDual β) _ _ _ _ f _ hx

theorem supr_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
  (⨆(y : _)(_ : y ∈ s.bUnion t), f y) = ⨆(x : _)(_ : x ∈ s)(y : _)(_ : y ∈ t x), f y :=
  by 
    simp [@supr_comm _ α, supr_and]

theorem infi_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
  (⨅(y : _)(_ : y ∈ s.bUnion t), f y) = ⨅(x : _)(_ : x ∈ s)(y : _)(_ : y ∈ t x), f y :=
  @supr_bUnion _ (OrderDual β) _ _ _ _ _ _

end Lattice

theorem set_bUnion_coe (s : Finset α) (t : α → Set β) :
  (⋃(x : _)(_ : x ∈ («expr↑ » s : Set α)), t x) = ⋃(x : _)(_ : x ∈ s), t x :=
  rfl

theorem set_bInter_coe (s : Finset α) (t : α → Set β) :
  (⋂(x : _)(_ : x ∈ («expr↑ » s : Set α)), t x) = ⋂(x : _)(_ : x ∈ s), t x :=
  rfl

theorem set_bUnion_singleton (a : α) (s : α → Set β) : (⋃(x : _)(_ : x ∈ ({a} : Finset α)), s x) = s a :=
  supr_singleton a s

theorem set_bInter_singleton (a : α) (s : α → Set β) : (⋂(x : _)(_ : x ∈ ({a} : Finset α)), s x) = s a :=
  infi_singleton a s

@[simp]
theorem set_bUnion_preimage_singleton (f : α → β) (s : Finset β) : (⋃(y : _)(_ : y ∈ s), f ⁻¹' {y}) = f ⁻¹' s :=
  Set.bUnion_preimage_singleton f s

theorem set_bUnion_option_to_finset (o : Option α) (f : α → Set β) :
  (⋃(x : _)(_ : x ∈ o.to_finset), f x) = ⋃(x : _)(_ : x ∈ o), f x :=
  supr_option_to_finset o f

theorem set_bInter_option_to_finset (o : Option α) (f : α → Set β) :
  (⋂(x : _)(_ : x ∈ o.to_finset), f x) = ⋂(x : _)(_ : x ∈ o), f x :=
  infi_option_to_finset o f

theorem subset_set_bUnion_of_mem {s : Finset α} {f : α → Set β} {x : α} (h : x ∈ s) : f x ⊆ ⋃(y : _)(_ : y ∈ s), f y :=
  show f x ≤ ⨆(y : _)(_ : y ∈ s), f y from le_supr_of_le x$ le_supr _ h

variable [DecidableEq α]

theorem set_bUnion_union (s t : Finset α) (u : α → Set β) :
  (⋃(x : _)(_ : x ∈ s ∪ t), u x) = (⋃(x : _)(_ : x ∈ s), u x) ∪ ⋃(x : _)(_ : x ∈ t), u x :=
  supr_union

theorem set_bInter_inter (s t : Finset α) (u : α → Set β) :
  (⋂(x : _)(_ : x ∈ s ∪ t), u x) = (⋂(x : _)(_ : x ∈ s), u x) ∩ ⋂(x : _)(_ : x ∈ t), u x :=
  infi_union

theorem set_bUnion_insert (a : α) (s : Finset α) (t : α → Set β) :
  (⋃(x : _)(_ : x ∈ insert a s), t x) = t a ∪ ⋃(x : _)(_ : x ∈ s), t x :=
  supr_insert a s t

theorem set_bInter_insert (a : α) (s : Finset α) (t : α → Set β) :
  (⋂(x : _)(_ : x ∈ insert a s), t x) = t a ∩ ⋂(x : _)(_ : x ∈ s), t x :=
  infi_insert a s t

theorem set_bUnion_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
  (⋃(x : _)(_ : x ∈ s.image f), g x) = ⋃(y : _)(_ : y ∈ s), g (f y) :=
  supr_finset_image

theorem set_bInter_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
  (⋂(x : _)(_ : x ∈ s.image f), g x) = ⋂(y : _)(_ : y ∈ s), g (f y) :=
  infi_finset_image

theorem set_bUnion_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
  (⋃(i : _)(_ : i ∈ insert x t), @update _ _ _ f x s i) = s ∪ ⋃(i : _)(_ : i ∈ t), f i :=
  supr_insert_update f hx

theorem set_bInter_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
  (⋂(i : _)(_ : i ∈ insert x t), @update _ _ _ f x s i) = s ∩ ⋂(i : _)(_ : i ∈ t), f i :=
  infi_insert_update f hx

theorem set_bUnion_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
  (⋃(y : _)(_ : y ∈ s.bUnion t), f y) = ⋃(x : _)(_ : x ∈ s)(y : _)(_ : y ∈ t x), f y :=
  supr_bUnion s t f

theorem set_bInter_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
  (⋂(y : _)(_ : y ∈ s.bUnion t), f y) = ⋂(x : _)(_ : x ∈ s)(y : _)(_ : y ∈ t x), f y :=
  infi_bUnion s t f

end Finset

