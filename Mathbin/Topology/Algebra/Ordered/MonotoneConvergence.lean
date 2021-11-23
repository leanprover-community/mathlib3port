import Mathbin.Topology.Algebra.Ordered.Basic

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `is_lub`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/


open Filter Set Function

open_locale Filter TopologicalSpace Classical

variable{α β : Type _}

/-- We say that `α` is a `Sup_convergence_class` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `set.range f`. Then `f x` tends to `𝓝 a` as
`x → ∞` (formally, at the filter `filter.at_top`). We require this for `ι = (s : set α)`, `f = coe`
in the definition, then prove it for any `f` in `tendsto_at_top_is_lub`.

This property holds for linear orders with order topology as well as their products. -/
class SupConvergenceClass(α : Type _)[Preorderₓ α][TopologicalSpace α] : Prop where 
  tendsto_coe_at_top_is_lub : ∀ a : α s : Set α, IsLub s a → tendsto (coeₓ : s → α) at_top (𝓝 a)

/-- We say that `α` is an `Inf_convergence_class` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `filter.at_bot`). We require this for `ι = (s : set α)`,
`f = coe` in the definition, then prove it for any `f` in `tendsto_at_bot_is_glb`.

This property holds for linear orders with order topology as well as their products. -/
class InfConvergenceClass(α : Type _)[Preorderₓ α][TopologicalSpace α] : Prop where 
  tendsto_coe_at_bot_is_glb : ∀ a : α s : Set α, IsGlb s a → tendsto (coeₓ : s → α) at_bot (𝓝 a)

instance OrderDual.Sup_convergence_class [Preorderₓ α] [TopologicalSpace α] [InfConvergenceClass α] :
  SupConvergenceClass (OrderDual α) :=
  ⟨‹InfConvergenceClass α›.1⟩

instance OrderDual.Inf_convergence_class [Preorderₓ α] [TopologicalSpace α] [SupConvergenceClass α] :
  InfConvergenceClass (OrderDual α) :=
  ⟨‹SupConvergenceClass α›.1⟩

instance (priority := 100)LinearOrderₓ.Sup_convergence_class [TopologicalSpace α] [LinearOrderₓ α] [OrderTopology α] :
  SupConvergenceClass α :=
  by 
    refine' ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => _, fun b hb => _⟩⟩
    ·
      rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
      lift c to s using hcs 
      refine' (eventually_ge_at_top c).mono fun x hx => bc.trans_le hx
    ·
      exact eventually_of_forall fun x => (ha.1 x.2).trans_lt hb

instance (priority := 100)LinearOrderₓ.Inf_convergence_class [TopologicalSpace α] [LinearOrderₓ α] [OrderTopology α] :
  InfConvergenceClass α :=
  show InfConvergenceClass (OrderDual$ OrderDual α) from OrderDual.Inf_convergence_class

section 

variable{ι : Type _}[Preorderₓ ι][TopologicalSpace α]

section IsLub

variable[Preorderₓ α][SupConvergenceClass α]{f : ι → α}{a : α}

theorem tendsto_at_top_is_lub (h_mono : Monotone f) (ha : IsLub (Set.Range f) a) : tendsto f at_top (𝓝 a) :=
  by 
    suffices  : tendsto (range_factorization f) at_top at_top 
    exact (SupConvergenceClass.tendsto_coe_at_top_is_lub _ _ ha).comp this 
    exact h_mono.range_factorization.tendsto_at_top_at_top fun b => b.2.imp$ fun a ha => ha.ge

theorem tendsto_at_bot_is_lub (h_anti : Antitone f) (ha : IsLub (Set.Range f) a) : tendsto f at_bot (𝓝 a) :=
  @tendsto_at_top_is_lub α (OrderDual ι) _ _ _ _ f a h_anti.dual ha

end IsLub

section IsGlb

variable[Preorderₓ α][InfConvergenceClass α]{f : ι → α}{a : α}

theorem tendsto_at_bot_is_glb (h_mono : Monotone f) (ha : IsGlb (Set.Range f) a) : tendsto f at_bot (𝓝 a) :=
  @tendsto_at_top_is_lub (OrderDual α) (OrderDual ι) _ _ _ _ f a h_mono.dual ha

theorem tendsto_at_top_is_glb (h_anti : Antitone f) (ha : IsGlb (Set.Range f) a) : tendsto f at_top (𝓝 a) :=
  @tendsto_at_top_is_lub (OrderDual α) ι _ _ _ _ f a h_anti ha

end IsGlb

section Csupr

variable[ConditionallyCompleteLattice α][SupConvergenceClass α]{f : ι → α}{a : α}

theorem tendsto_at_top_csupr (h_mono : Monotone f) (hbdd : BddAbove$ range f) : tendsto f at_top (𝓝 (⨆i, f i)) :=
  by 
    cases' is_empty_or_nonempty ι 
    exacts[tendsto_of_is_empty, tendsto_at_top_is_lub h_mono (is_lub_csupr hbdd)]

theorem tendsto_at_bot_csupr (h_anti : Antitone f) (hbdd : BddAbove$ range f) : tendsto f at_bot (𝓝 (⨆i, f i)) :=
  @tendsto_at_top_csupr α (OrderDual ι) _ _ _ _ _ h_anti.dual hbdd

end Csupr

section Cinfi

variable[ConditionallyCompleteLattice α][InfConvergenceClass α]{f : ι → α}{a : α}

theorem tendsto_at_bot_cinfi (h_mono : Monotone f) (hbdd : BddBelow$ range f) : tendsto f at_bot (𝓝 (⨅i, f i)) :=
  @tendsto_at_top_csupr (OrderDual α) (OrderDual ι) _ _ _ _ _ h_mono.dual hbdd

theorem tendsto_at_top_cinfi (h_anti : Antitone f) (hbdd : BddBelow$ range f) : tendsto f at_top (𝓝 (⨅i, f i)) :=
  @tendsto_at_top_csupr (OrderDual α) ι _ _ _ _ _ h_anti hbdd

end Cinfi

section supr

variable[CompleteLattice α][SupConvergenceClass α]{f : ι → α}{a : α}

theorem tendsto_at_top_supr (h_mono : Monotone f) : tendsto f at_top (𝓝 (⨆i, f i)) :=
  tendsto_at_top_csupr h_mono (OrderTop.bdd_above _)

theorem tendsto_at_bot_supr (h_anti : Antitone f) : tendsto f at_bot (𝓝 (⨆i, f i)) :=
  tendsto_at_bot_csupr h_anti (OrderTop.bdd_above _)

end supr

section infi

variable[CompleteLattice α][InfConvergenceClass α]{f : ι → α}{a : α}

theorem tendsto_at_bot_infi (h_mono : Monotone f) : tendsto f at_bot (𝓝 (⨅i, f i)) :=
  tendsto_at_bot_cinfi h_mono (OrderBot.bdd_below _)

theorem tendsto_at_top_infi (h_anti : Antitone f) : tendsto f at_top (𝓝 (⨅i, f i)) :=
  tendsto_at_top_cinfi h_anti (OrderBot.bdd_below _)

end infi

end 

-- error in Topology.Algebra.Ordered.MonotoneConvergence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance
[preorder α]
[preorder β]
[topological_space α]
[topological_space β]
[Sup_convergence_class α]
[Sup_convergence_class β] : Sup_convergence_class «expr × »(α, β) :=
begin
  constructor,
  rintro ["⟨", ident a, ",", ident b, "⟩", ident s, ident h],
  rw ["[", expr is_lub_prod, ",", "<-", expr range_restrict, ",", "<-", expr range_restrict, "]"] ["at", ident h],
  have [ident A] [":", expr tendsto (λ x : s, (x : «expr × »(α, β)).1) at_top (expr𝓝() a)] [],
  from [expr tendsto_at_top_is_lub (monotone_fst.restrict s) h.1],
  have [ident B] [":", expr tendsto (λ x : s, (x : «expr × »(α, β)).2) at_top (expr𝓝() b)] [],
  from [expr tendsto_at_top_is_lub (monotone_snd.restrict s) h.2],
  convert [] [expr A.prod_mk_nhds B] [],
  ext1 [] ["⟨", "⟨", ident x, ",", ident y, "⟩", ",", ident h, "⟩"],
  refl
end

instance  [Preorderₓ α] [Preorderₓ β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
  [InfConvergenceClass β] : InfConvergenceClass (α × β) :=
  show InfConvergenceClass (OrderDual$ OrderDual α × OrderDual β) from OrderDual.Inf_convergence_class

instance  {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] [∀ i, TopologicalSpace (α i)]
  [∀ i, SupConvergenceClass (α i)] : SupConvergenceClass (∀ i, α i) :=
  by 
    refine' ⟨fun f s h => _⟩
    simp only [is_lub_pi, ←range_restrict] at h 
    exact tendsto_pi.2 fun i => tendsto_at_top_is_lub ((monotone_eval _).restrict _) (h i)

instance  {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] [∀ i, TopologicalSpace (α i)]
  [∀ i, InfConvergenceClass (α i)] : InfConvergenceClass (∀ i, α i) :=
  show InfConvergenceClass (OrderDual$ ∀ i, OrderDual (α i)) from OrderDual.Inf_convergence_class

instance Pi.Sup_convergence_class' {ι : Type _} [Preorderₓ α] [TopologicalSpace α] [SupConvergenceClass α] :
  SupConvergenceClass (ι → α) :=
  Pi.Sup_convergence_class

instance Pi.Inf_convergence_class' {ι : Type _} [Preorderₓ α] [TopologicalSpace α] [InfConvergenceClass α] :
  InfConvergenceClass (ι → α) :=
  Pi.Inf_convergence_class

theorem tendsto_of_monotone {ι α : Type _} [Preorderₓ ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α]
  [OrderTopology α] {f : ι → α} (h_mono : Monotone f) : tendsto f at_top at_top ∨ ∃ l, tendsto f at_top (𝓝 l) :=
  if H : BddAbove (range f) then Or.inr ⟨_, tendsto_at_top_csupr h_mono H⟩ else
    Or.inl$ tendsto_at_top_at_top_of_monotone' h_mono H

theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type _} [SemilatticeSup ι₁] [Preorderₓ ι₂] [Nonempty ι₁]
  [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α] [NoTopOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂}
  {l : α} (hf : Monotone f) (hg : tendsto φ at_top at_top) : tendsto f at_top (𝓝 l) ↔ tendsto (f ∘ φ) at_top (𝓝 l) :=
  by 
    split  <;> intro h
    ·
      exact h.comp hg
    ·
      rcases tendsto_of_monotone hf with (h' | ⟨l', hl'⟩)
      ·
        exact (not_tendsto_at_top_of_tendsto_nhds h (h'.comp hg)).elim
      ·
        rwa [tendsto_nhds_unique h (hl'.comp hg)]

/-! The next family of results, such as `is_lub_of_tendsto` and `supr_eq_of_tendsto`, are converses
to the standard fact that bounded monotone functions converge. They state, that if a monotone
function `f` tends to `a` along `at_top`, then that value `a` is a least upper bound for the range
of `f`.

Related theorems above (`is_lub.is_lub_of_tendsto`, `is_glb.is_glb_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/


-- error in Topology.Algebra.Ordered.MonotoneConvergence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem monotone.ge_of_tendsto
{α β : Type*}
[topological_space α]
[preorder α]
[order_closed_topology α]
[semilattice_sup β]
{f : β → α}
{a : α}
(hf : monotone f)
(ha : tendsto f at_top (expr𝓝() a))
(b : β) : «expr ≤ »(f b, a) :=
begin
  haveI [] [":", expr nonempty β] [":=", expr nonempty.intro b],
  exact [expr ge_of_tendsto ha ((eventually_ge_at_top b).mono (λ _ hxy, hf hxy))]
end

theorem Monotone.le_of_tendsto {α β : Type _} [TopologicalSpace α] [Preorderₓ α] [OrderClosedTopology α]
  [SemilatticeInf β] {f : β → α} {a : α} (hf : Monotone f) (ha : tendsto f at_bot (𝓝 a)) (b : β) : a ≤ f b :=
  @Monotone.ge_of_tendsto (OrderDual α) (OrderDual β) _ _ _ _ f _ hf.dual ha b

theorem is_lub_of_tendsto {α β : Type _} [TopologicalSpace α] [Preorderₓ α] [OrderClosedTopology α] [Nonempty β]
  [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) (ha : tendsto f at_top (𝓝 a)) : IsLub (Set.Range f) a :=
  by 
    split 
    ·
      rintro _ ⟨b, rfl⟩
      exact hf.ge_of_tendsto ha b
    ·
      exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem is_glb_of_tendsto {α β : Type _} [TopologicalSpace α] [Preorderₓ α] [OrderClosedTopology α] [Nonempty β]
  [SemilatticeInf β] {f : β → α} {a : α} (hf : Monotone f) (ha : tendsto f at_bot (𝓝 a)) : IsGlb (Set.Range f) a :=
  @is_lub_of_tendsto (OrderDual α) (OrderDual β) _ _ _ _ _ _ _ hf.dual ha

theorem supr_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α] [Nonempty β]
  [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) : tendsto f at_top (𝓝 a) → supr f = a :=
  tendsto_nhds_unique (tendsto_at_top_supr hf)

theorem infi_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α] [Nonempty β]
  [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) : tendsto f at_top (𝓝 a) → infi f = a :=
  tendsto_nhds_unique (tendsto_at_top_infi hf)

theorem supr_eq_supr_subseq_of_monotone {ι₁ ι₂ α : Type _} [Preorderₓ ι₂] [CompleteLattice α] {l : Filter ι₁} [l.ne_bot]
  {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f) (hφ : tendsto φ l at_top) : (⨆i, f i) = ⨆i, f (φ i) :=
  le_antisymmₓ
    (supr_le_supr2$
      fun i => exists_imp_exists (fun j hj : i ≤ φ j => hf hj) (hφ.eventually$ eventually_ge_at_top i).exists)
    (supr_le_supr2$ fun i => ⟨φ i, le_reflₓ _⟩)

theorem infi_eq_infi_subseq_of_monotone {ι₁ ι₂ α : Type _} [Preorderₓ ι₂] [CompleteLattice α] {l : Filter ι₁} [l.ne_bot]
  {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f) (hφ : tendsto φ l at_bot) : (⨅i, f i) = ⨅i, f (φ i) :=
  supr_eq_supr_subseq_of_monotone hf.dual hφ

