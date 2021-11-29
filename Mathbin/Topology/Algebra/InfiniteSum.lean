import Mathbin.Algebra.BigOperators.Intervals 
import Mathbin.Algebra.BigOperators.NatAntidiagonal 
import Mathbin.Data.Equiv.Encodable.Lattice 
import Mathbin.Topology.Algebra.MulAction 
import Mathbin.Topology.Algebra.Ordered.MonotoneConvergence 
import Mathbin.Topology.Instances.Real

/-!
# Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/


noncomputable theory

open Finset Filter Function Classical

open_locale TopologicalSpace Classical BigOperators Nnreal

variable{α : Type _}{β : Type _}{γ : Type _}{δ : Type _}

section HasSum

variable[AddCommMonoidₓ α][TopologicalSpace α]

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/ def has_sum (f : β → α) (a : α) : exprProp() :=
tendsto (λ s : finset β, «expr∑ in , »((b), s, f b)) at_top (expr𝓝() a)

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def Summable (f : β → α) : Prop :=
  ∃ a, HasSum f a

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise -/
@[irreducible]
def tsum {β} (f : β → α) :=
  if h : Summable f then Classical.some h else 0

notation3  "∑'" (...) ", " r:(scoped f => tsum f) => r

variable{f g : β → α}{a b : α}{s : Finset β}

theorem Summable.has_sum (ha : Summable f) : HasSum f (∑'b, f b) :=
  by 
    simp [ha, tsum] <;> exact some_spec ha

theorem HasSum.summable (h : HasSum f a) : Summable f :=
  ⟨a, h⟩

/-- Constant zero function has sum `0` -/
theorem has_sum_zero : HasSum (fun b => 0 : β → α) 0 :=
  by 
    simp [HasSum, tendsto_const_nhds]

theorem has_sum_empty [IsEmpty β] : HasSum f 0 :=
  by 
    convert has_sum_zero

theorem summable_zero : Summable (fun b => 0 : β → α) :=
  has_sum_zero.Summable

theorem summable_empty [IsEmpty β] : Summable f :=
  has_sum_empty.Summable

theorem tsum_eq_zero_of_not_summable (h : ¬Summable f) : (∑'b, f b) = 0 :=
  by 
    simp [tsum, h]

theorem summable_congr (hfg : ∀ b, f b = g b) : Summable f ↔ Summable g :=
  iff_of_eq (congr_argₓ Summable$ funext hfg)

theorem Summable.congr (hf : Summable f) (hfg : ∀ b, f b = g b) : Summable g :=
  (summable_congr hfg).mp hf

theorem HasSum.has_sum_of_sum_eq {g : γ → α}
  (h_eq : ∀ (u : Finset γ), ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑x in u', g x) = ∑b in v', f b)
  (hf : HasSum g a) : HasSum f a :=
  le_transₓ (map_at_top_finset_sum_le_of_sum_eq h_eq) hf

theorem has_sum_iff_has_sum {g : γ → α}
  (h₁ : ∀ (u : Finset γ), ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑x in u', g x) = ∑b in v', f b)
  (h₂ : ∀ (v : Finset β), ∃ u : Finset γ, ∀ u', u ⊆ u' → ∃ v', v ⊆ v' ∧ (∑b in v', f b) = ∑x in u', g x) :
  HasSum f a ↔ HasSum g a :=
  ⟨HasSum.has_sum_of_sum_eq h₂, HasSum.has_sum_of_sum_eq h₁⟩

theorem Function.Injective.has_sum_iff {g : γ → β} (hg : injective g) (hf : ∀ x (_ : x ∉ Set.Range g), f x = 0) :
  HasSum (f ∘ g) a ↔ HasSum f a :=
  by 
    simp only [HasSum, tendsto, hg.map_at_top_finset_sum_eq hf]

theorem Function.Injective.summable_iff {g : γ → β} (hg : injective g) (hf : ∀ x (_ : x ∉ Set.Range g), f x = 0) :
  Summable (f ∘ g) ↔ Summable f :=
  exists_congr$ fun _ => hg.has_sum_iff hf

theorem has_sum_subtype_iff_of_support_subset {s : Set β} (hf : support f ⊆ s) :
  HasSum (f ∘ coeₓ : s → α) a ↔ HasSum f a :=
  Subtype.coe_injective.has_sum_iff$
    by 
      simpa using support_subset_iff'.1 hf

theorem has_sum_subtype_iff_indicator {s : Set β} : HasSum (f ∘ coeₓ : s → α) a ↔ HasSum (s.indicator f) a :=
  by 
    rw [←Set.indicator_range_comp, Subtype.range_coe,
      has_sum_subtype_iff_of_support_subset Set.support_indicator_subset]

@[simp]
theorem has_sum_subtype_support : HasSum (f ∘ coeₓ : support f → α) a ↔ HasSum f a :=
  has_sum_subtype_iff_of_support_subset$ Set.Subset.refl _

theorem has_sum_fintype [Fintype β] (f : β → α) : HasSum f (∑b, f b) :=
  OrderTop.tendsto_at_top_nhds _

protected theorem Finset.has_sum (s : Finset β) (f : β → α) :
  HasSum (f ∘ coeₓ : («expr↑ » s : Set β) → α) (∑b in s, f b) :=
  by 
    rw [←sum_attach]
    exact has_sum_fintype _

protected theorem Finset.summable (s : Finset β) (f : β → α) : Summable (f ∘ coeₓ : («expr↑ » s : Set β) → α) :=
  (s.has_sum f).Summable

protected theorem Set.Finite.summable {s : Set β} (hs : s.finite) (f : β → α) : Summable (f ∘ coeₓ : s → α) :=
  by 
    convert hs.to_finset.summable f <;> simp only [hs.coe_to_finset]

/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
theorem has_sum_sum_of_ne_finset_zero (hf : ∀ b (_ : b ∉ s), f b = 0) : HasSum f (∑b in s, f b) :=
  (has_sum_subtype_iff_of_support_subset$ support_subset_iff'.2 hf).1$ s.has_sum f

theorem summable_of_ne_finset_zero (hf : ∀ b (_ : b ∉ s), f b = 0) : Summable f :=
  (has_sum_sum_of_ne_finset_zero hf).Summable

theorem has_sum_single {f : β → α} (b : β) (hf : ∀ b' (_ : b' ≠ b), f b' = 0) : HasSum f (f b) :=
  suffices HasSum f (∑b' in {b}, f b')by 
    simpa using this 
  has_sum_sum_of_ne_finset_zero$
    by 
      simpa [hf]

theorem has_sum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) : HasSum (fun b' => if b' = b then a else 0) a :=
  by 
    convert has_sum_single b _
    ·
      exact (if_pos rfl).symm 
    intro b' hb' 
    exact if_neg hb'

theorem Equiv.has_sum_iff (e : γ ≃ β) : HasSum (f ∘ e) a ↔ HasSum f a :=
  e.injective.has_sum_iff$
    by 
      simp 

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem function.injective.has_sum_range_iff
{g : γ → β}
(hg : injective g) : «expr ↔ »(has_sum (λ x : set.range g, f x) a, has_sum «expr ∘ »(f, g) a) :=
(equiv.of_injective g hg).has_sum_iff.symm

theorem Equiv.summable_iff (e : γ ≃ β) : Summable (f ∘ e) ↔ Summable f :=
  exists_congr$ fun a => e.has_sum_iff

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable.prod_symm {f : «expr × »(β, γ) → α} (hf : summable f) : summable (λ p : «expr × »(γ, β), f p.swap) :=
(equiv.prod_comm γ β).summable_iff.2 hf

theorem Equiv.has_sum_iff_of_support {g : γ → α} (e : support f ≃ support g) (he : ∀ (x : support f), g (e x) = f x) :
  HasSum f a ↔ HasSum g a :=
  have  : ((g ∘ coeₓ) ∘ e) = (f ∘ coeₓ) := funext he 
  by 
    rw [←has_sum_subtype_support, ←this, e.has_sum_iff, has_sum_subtype_support]

theorem has_sum_iff_has_sum_of_ne_zero_bij {g : γ → α} (i : support g → β) (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
  (hf : support f ⊆ Set.Range i) (hfg : ∀ x, f (i x) = g x) : HasSum f a ↔ HasSum g a :=
  Iff.symm$
    Equiv.has_sum_iff_of_support
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop$ hfg x ▸ hx⟩)
        ⟨fun x y h => Subtype.ext$ hi$ Subtype.ext_iff.1 h, fun y => (hf y.coe_prop).imp$ fun x hx => Subtype.ext hx⟩)
      hfg

theorem Equiv.summable_iff_of_support {g : γ → α} (e : support f ≃ support g) (he : ∀ (x : support f), g (e x) = f x) :
  Summable f ↔ Summable g :=
  exists_congr$ fun _ => e.has_sum_iff_of_support he

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem has_sum.map
[add_comm_monoid γ]
[topological_space γ]
(hf : has_sum f a)
(g : «expr →+ »(α, γ))
(hg : continuous g) : has_sum «expr ∘ »(g, f) (g a) :=
have «expr = »(«expr ∘ »(g, λ
  s : finset β, «expr∑ in , »((b), s, f b)), λ
 s : finset β, «expr∑ in , »((b), s, g (f b))), from «expr $ »(funext, g.map_sum _),
show tendsto (λ
 s : finset β, «expr∑ in , »((b), s, g (f b))) at_top (expr𝓝() (g a)), from «expr ▸ »(this, (hg.tendsto a).comp hf)

protected theorem Summable.map [AddCommMonoidₓ γ] [TopologicalSpace γ] (hf : Summable f) (g : α →+ γ)
  (hg : Continuous g) : Summable (g ∘ f) :=
  (hf.has_sum.map g hg).Summable

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
theorem has_sum.tendsto_sum_nat
{f : exprℕ() → α}
(h : has_sum f a) : tendsto (λ n : exprℕ(), «expr∑ in , »((i), range n, f i)) at_top (expr𝓝() a) :=
h.comp tendsto_finset_range

theorem HasSum.unique {a₁ a₂ : α} [T2Space α] : HasSum f a₁ → HasSum f a₂ → a₁ = a₂ :=
  tendsto_nhds_unique

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable.has_sum_iff_tendsto_nat
[t2_space α]
{f : exprℕ() → α}
{a : α}
(hf : summable f) : «expr ↔ »(has_sum f a, tendsto (λ
  n : exprℕ(), «expr∑ in , »((i), range n, f i)) at_top (expr𝓝() a)) :=
begin
  refine [expr ⟨λ h, h.tendsto_sum_nat, λ h, _⟩],
  rw [expr tendsto_nhds_unique h hf.has_sum.tendsto_sum_nat] [],
  exact [expr hf.has_sum]
end

theorem Equiv.summable_iff_of_has_sum_iff {α' : Type _} [AddCommMonoidₓ α'] [TopologicalSpace α'] (e : α' ≃ α)
  {f : β → α} {g : γ → α'} (he : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : Summable f ↔ Summable g :=
  ⟨fun ⟨a, ha⟩ =>
      ⟨e.symm a,
        he.1$
          by 
            rwa [e.apply_symm_apply]⟩,
    fun ⟨a, ha⟩ => ⟨e a, he.2 ha⟩⟩

variable[HasContinuousAdd α]

theorem HasSum.add (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun b => f b+g b) (a+b) :=
  by 
    simp only [HasSum, sum_add_distrib] <;> exact hf.add hg

theorem Summable.add (hf : Summable f) (hg : Summable g) : Summable fun b => f b+g b :=
  (hf.has_sum.add hg.has_sum).Summable

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum_sum
{f : γ → β → α}
{a : γ → α}
{s : finset γ} : ∀
i «expr ∈ » s, has_sum (f i) (a i) → has_sum (λ b, «expr∑ in , »((i), s, f i b)) «expr∑ in , »((i), s, a i) :=
finset.induction_on s (by simp [] [] ["only"] ["[", expr has_sum_zero, ",", expr sum_empty, ",", expr forall_true_iff, "]"] [] []) (by simp [] [] ["only"] ["[", expr has_sum.add, ",", expr sum_insert, ",", expr mem_insert, ",", expr forall_eq_or_imp, ",", expr forall_2_true_iff, ",", expr not_false_iff, ",", expr forall_true_iff, "]"] [] [] { contextual := tt })

theorem summable_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i (_ : i ∈ s), Summable (f i)) :
  Summable fun b => ∑i in s, f i b :=
  (has_sum_sum$ fun i hi => (hf i hi).HasSum).Summable

theorem HasSum.add_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasSum (f ∘ coeₓ : s → α) a)
  (hb : HasSum (f ∘ coeₓ : t → α) b) : HasSum (f ∘ coeₓ : s ∪ t → α) (a+b) :=
  by 
    rw [has_sum_subtype_iff_indicator] at *
    rw [Set.indicator_union_of_disjoint hs]
    exact ha.add hb

theorem HasSum.add_is_compl {s t : Set β} (hs : IsCompl s t) (ha : HasSum (f ∘ coeₓ : s → α) a)
  (hb : HasSum (f ∘ coeₓ : t → α) b) : HasSum f (a+b) :=
  by 
    simpa [←hs.compl_eq] using (has_sum_subtype_iff_indicator.1 ha).add (has_sum_subtype_iff_indicator.1 hb)

theorem HasSum.add_compl {s : Set β} (ha : HasSum (f ∘ coeₓ : s → α) a) (hb : HasSum (f ∘ coeₓ : «expr ᶜ» s → α) b) :
  HasSum f (a+b) :=
  ha.add_is_compl is_compl_compl hb

theorem Summable.add_compl {s : Set β} (hs : Summable (f ∘ coeₓ : s → α)) (hsc : Summable (f ∘ coeₓ : «expr ᶜ» s → α)) :
  Summable f :=
  (hs.has_sum.add_compl hsc.has_sum).Summable

theorem HasSum.compl_add {s : Set β} (ha : HasSum (f ∘ coeₓ : «expr ᶜ» s → α) a) (hb : HasSum (f ∘ coeₓ : s → α) b) :
  HasSum f (a+b) :=
  ha.add_is_compl is_compl_compl.symm hb

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum.even_add_odd
{f : exprℕ() → α}
(he : has_sum (λ k, f «expr * »(2, k)) a)
(ho : has_sum (λ k, f «expr + »(«expr * »(2, k), 1)) b) : has_sum f «expr + »(a, b) :=
begin
  have [] [] [":=", expr mul_right_injective₀ (@two_ne_zero exprℕ() _ _)],
  replace [ident he] [] [":=", expr this.has_sum_range_iff.2 he],
  replace [ident ho] [] [":=", expr ((add_left_injective 1).comp this).has_sum_range_iff.2 ho],
  refine [expr he.add_is_compl _ ho],
  simpa [] [] [] ["[", expr («expr ∘ »), "]"] [] ["using", expr nat.is_compl_even_odd]
end

theorem Summable.compl_add {s : Set β} (hs : Summable (f ∘ coeₓ : «expr ᶜ» s → α)) (hsc : Summable (f ∘ coeₓ : s → α)) :
  Summable f :=
  (hs.has_sum.compl_add hsc.has_sum).Summable

theorem Summable.even_add_odd {f : ℕ → α} (he : Summable fun k => f (2*k)) (ho : Summable fun k => f ((2*k)+1)) :
  Summable f :=
  (he.has_sum.even_add_odd ho.has_sum).Summable

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum.sigma
[regular_space α]
{γ : β → Type*}
{f : «exprΣ , »((b : β), γ b) → α}
{g : β → α}
{a : α}
(ha : has_sum f a)
(hf : ∀ b, has_sum (λ c, f ⟨b, c⟩) (g b)) : has_sum g a :=
begin
  refine [expr (at_top_basis.tendsto_iff (closed_nhds_basis a)).mpr _],
  rintros [ident s, "⟨", ident hs, ",", ident hsc, "⟩"],
  rcases [expr mem_at_top_sets.mp (ha hs), "with", "⟨", ident u, ",", ident hu, "⟩"],
  use ["[", expr u.image sigma.fst, ",", expr trivial, "]"],
  intros [ident bs, ident hbs],
  simp [] [] ["only"] ["[", expr set.mem_preimage, ",", expr ge_iff_le, ",", expr finset.le_iff_subset, "]"] [] ["at", ident hu],
  have [] [":", expr tendsto (λ
    t : finset «exprΣ , »((b), γ b), «expr∑ in , »((p), t.filter (λ
      p, «expr ∈ »(p.1, bs)), f p)) at_top «expr $ »(expr𝓝(), «expr∑ in , »((b), bs, g b))] [],
  { simp [] [] ["only"] ["[", "<-", expr sigma_preimage_mk, ",", expr sum_sigma, "]"] [] [],
    refine [expr tendsto_finset_sum _ (λ b hb, _)],
    change [expr tendsto (λ
      t, λ t, «expr∑ in , »((s), t, f ⟨b, s⟩) (preimage t (sigma.mk b) _)) at_top (expr𝓝() (g b))] [] [],
    exact [expr tendsto.comp (hf b) (tendsto_finset_preimage_at_top_at_top _)] },
  refine [expr hsc.mem_of_tendsto this (eventually_at_top.2 ⟨u, λ t ht, hu _ (λ x hx, _)⟩)],
  exact [expr mem_filter.2 ⟨ht hx, «expr $ »(hbs, mem_image_of_mem _ hx)⟩]
end

/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
theorem HasSum.prod_fiberwise [RegularSpace α] {f : β × γ → α} {g : β → α} {a : α} (ha : HasSum f a)
  (hf : ∀ b, HasSum (fun c => f (b, c)) (g b)) : HasSum g a :=
  HasSum.sigma ((Equiv.sigmaEquivProd β γ).has_sum_iff.2 ha) hf

theorem Summable.sigma' [RegularSpace α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f)
  (hf : ∀ b, Summable fun c => f ⟨b, c⟩) : Summable fun b => ∑'c, f ⟨b, c⟩ :=
  (ha.has_sum.sigma fun b => (hf b).HasSum).Summable

theorem HasSum.sigma_of_has_sum [RegularSpace α] {γ : β → Type _} {f : (Σb : β, γ b) → α} {g : β → α} {a : α}
  (ha : HasSum g a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) (hf' : Summable f) : HasSum f a :=
  by 
    simpa [(hf'.has_sum.sigma hf).unique ha] using hf'.has_sum

end HasSum

section tsum

variable[AddCommMonoidₓ α][TopologicalSpace α][T2Space α]

variable{f g : β → α}{a a₁ a₂ : α}

theorem HasSum.tsum_eq (ha : HasSum f a) : (∑'b, f b) = a :=
  (Summable.has_sum ⟨a, ha⟩).unique ha

theorem Summable.has_sum_iff (h : Summable f) : HasSum f a ↔ (∑'b, f b) = a :=
  Iff.intro HasSum.tsum_eq fun eq => Eq ▸ h.has_sum

@[simp]
theorem tsum_zero : (∑'b : β, (0 : α)) = 0 :=
  has_sum_zero.tsum_eq

@[simp]
theorem tsum_empty [IsEmpty β] : (∑'b, f b) = 0 :=
  has_sum_empty.tsum_eq

theorem tsum_eq_sum {f : β → α} {s : Finset β} (hf : ∀ b (_ : b ∉ s), f b = 0) : (∑'b, f b) = ∑b in s, f b :=
  (has_sum_sum_of_ne_finset_zero hf).tsum_eq

theorem tsum_congr {α β : Type _} [AddCommMonoidₓ α] [TopologicalSpace α] {f g : β → α} (hfg : ∀ b, f b = g b) :
  (∑'b, f b) = ∑'b, g b :=
  congr_argₓ tsum (funext hfg)

theorem tsum_fintype [Fintype β] (f : β → α) : (∑'b, f b) = ∑b, f b :=
  (has_sum_fintype f).tsum_eq

theorem tsum_bool (f : Bool → α) : (∑'i : Bool, f i) = f False+f True :=
  by 
    rw [tsum_fintype, Finset.sum_eq_add] <;> simp 

@[simp]
theorem Finset.tsum_subtype (s : Finset β) (f : β → α) : (∑'x : { x // x ∈ s }, f x) = ∑x in s, f x :=
  (s.has_sum f).tsum_eq

@[simp]
theorem Finset.tsum_subtype' (s : Finset β) (f : β → α) : (∑'x : (s : Set β), f x) = ∑x in s, f x :=
  s.tsum_subtype f

theorem tsum_eq_single {f : β → α} (b : β) (hf : ∀ b' (_ : b' ≠ b), f b' = 0) : (∑'b, f b) = f b :=
  (has_sum_single b hf).tsum_eq

@[simp]
theorem tsum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) : (∑'b', if b' = b then a else 0) = a :=
  (has_sum_ite_eq b a).tsum_eq

theorem tsum_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
  (∑'b : β, if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑'b : β, x b h :=
  by 
    byCases' hP : P <;> simp [hP]

theorem tsum_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
  (∑'b : β, if h : P then x b h else 0) = if h : P then ∑'b : β, x b h else 0 :=
  by 
    byCases' hP : P <;> simp [hP]

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem equiv.tsum_eq_tsum_of_has_sum_iff_has_sum
{α' : Type*}
[add_comm_monoid α']
[topological_space α']
(e : «expr ≃ »(α', α))
(h0 : «expr = »(e 0, 0))
{f : β → α}
{g : γ → α'}
(h : ∀ {a}, «expr ↔ »(has_sum f (e a), has_sum g a)) : «expr = »(«expr∑' , »((b), f b), e «expr∑' , »((c), g c)) :=
by_cases (assume: summable g, (h.mpr this.has_sum).tsum_eq) (assume
 hg : «expr¬ »(summable g), have hf : «expr¬ »(summable f), from mt (e.summable_iff_of_has_sum_iff @h).1 hg,
 by simp [] [] [] ["[", expr tsum, ",", expr hf, ",", expr hg, ",", expr h0, "]"] [] [])

theorem tsum_eq_tsum_of_has_sum_iff_has_sum {f : β → α} {g : γ → α} (h : ∀ {a}, HasSum f a ↔ HasSum g a) :
  (∑'b, f b) = ∑'c, g c :=
  (Equiv.refl α).tsum_eq_tsum_of_has_sum_iff_has_sum rfl @h

theorem Equiv.tsum_eq (j : γ ≃ β) (f : β → α) : (∑'c, f (j c)) = ∑'b, f b :=
  tsum_eq_tsum_of_has_sum_iff_has_sum$ fun a => j.has_sum_iff

theorem Equiv.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : support f ≃ support g) (he : ∀ x, g (e x) = f x) :
  (∑'x, f x) = ∑'y, g y :=
  tsum_eq_tsum_of_has_sum_iff_has_sum$ fun _ => e.has_sum_iff_of_support he

theorem tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : support g → β) (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
  (hf : support f ⊆ Set.Range i) (hfg : ∀ x, f (i x) = g x) : (∑'x, f x) = ∑'y, g y :=
  tsum_eq_tsum_of_has_sum_iff_has_sum$ fun _ => has_sum_iff_has_sum_of_ne_zero_bij i hi hf hfg

theorem tsum_subtype (s : Set β) (f : β → α) : (∑'x : s, f x) = ∑'x, s.indicator f x :=
  tsum_eq_tsum_of_has_sum_iff_has_sum$ fun _ => has_sum_subtype_iff_indicator

section HasContinuousAdd

variable[HasContinuousAdd α]

theorem tsum_add (hf : Summable f) (hg : Summable g) : (∑'b, f b+g b) = (∑'b, f b)+∑'b, g b :=
  (hf.has_sum.add hg.has_sum).tsum_eq

theorem tsum_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i (_ : i ∈ s), Summable (f i)) :
  (∑'b, ∑i in s, f i b) = ∑i in s, ∑'b, f i b :=
  (has_sum_sum$ fun i hi => (hf i hi).HasSum).tsum_eq

theorem tsum_sigma' [RegularSpace α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (h₁ : ∀ b, Summable fun c => f ⟨b, c⟩)
  (h₂ : Summable f) : (∑'p, f p) = ∑'b c, f ⟨b, c⟩ :=
  (h₂.has_sum.sigma fun b => (h₁ b).HasSum).tsum_eq.symm

theorem tsum_prod' [RegularSpace α] {f : β × γ → α} (h : Summable f) (h₁ : ∀ b, Summable fun c => f (b, c)) :
  (∑'p, f p) = ∑'b c, f (b, c) :=
  (h.has_sum.prod_fiberwise fun b => (h₁ b).HasSum).tsum_eq.symm

theorem tsum_comm' [RegularSpace α] {f : β → γ → α} (h : Summable (Function.uncurry f)) (h₁ : ∀ b, Summable (f b))
  (h₂ : ∀ c, Summable fun b => f b c) : (∑'c b, f b c) = ∑'b c, f b c :=
  by 
    erw [←tsum_prod' h h₁, ←tsum_prod' h.prod_symm h₂, ←(Equiv.prodComm β γ).tsum_eq]
    rfl 
    assumption

end HasContinuousAdd

section Encodable

open Encodable

variable[Encodable γ]

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_supr_decode₂
[complete_lattice β]
(m : β → α)
(m0 : «expr = »(m «expr⊥»(), 0))
(s : γ → β) : «expr = »(«expr∑' , »((i : exprℕ()), m «expr⨆ , »((b «expr ∈ » decode₂ γ i), s b)), «expr∑' , »((b : γ), m (s b))) :=
begin
  have [ident H] [":", expr ∀ n, «expr ≠ »(m «expr⨆ , »((b «expr ∈ » decode₂ γ n), s b), 0) → (decode₂ γ n).is_some] [],
  { intros [ident n, ident h],
    cases [expr decode₂ γ n] ["with", ident b],
    { refine [expr «expr $ »(h, by simp [] [] [] ["[", expr m0, "]"] [] []).elim] },
    { exact [expr rfl] } },
  symmetry,
  refine [expr tsum_eq_tsum_of_ne_zero_bij (λ a, option.get (H a.1 a.2)) _ _ _],
  { rintros ["⟨", ident m, ",", ident hm, "⟩", "⟨", ident n, ",", ident hn, "⟩", ident e],
    have [] [] [":=", expr mem_decode₂.1 (option.get_mem (H n hn))],
    rwa ["[", "<-", expr e, ",", expr mem_decode₂.1 (option.get_mem (H m hm)), "]"] ["at", ident this] },
  { intros [ident b, ident h],
    refine [expr ⟨⟨encode b, _⟩, _⟩],
    { simp [] [] ["only"] ["[", expr mem_support, ",", expr encodek₂, "]"] [] ["at", ident h, "⊢"],
      convert [] [expr h] [],
      simp [] [] [] ["[", expr set.ext_iff, ",", expr encodek₂, "]"] [] [] },
    { exact [expr option.get_of_mem _ (encodek₂ _)] } },
  { rintros ["⟨", ident n, ",", ident h, "⟩"],
    dsimp ["only"] ["[", expr subtype.coe_mk, "]"] [] [],
    transitivity [],
    swap,
    rw ["[", expr show «expr = »(decode₂ γ n, _), from option.get_mem (H n h), "]"] [],
    congr,
    simp [] [] [] ["[", expr ext_iff, ",", "-", ident option.some_get, "]"] [] [] }
end

/-- `tsum_supr_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_Union_decode₂ (m : Set β → α) (m0 : m ∅ = 0) (s : γ → Set β) :
  (∑'i, m (⋃(b : _)(_ : b ∈ decode₂ γ i), s b)) = ∑'b, m (s b) :=
  tsum_supr_decode₂ m m0 s

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/


/-- If a function is countably sub-additive then it is sub-additive on encodable types -/
theorem rel_supr_tsum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
  (m_supr : ∀ (s : ℕ → β), R (m (⨆i, s i)) (∑'i, m (s i))) (s : γ → β) : R (m (⨆b : γ, s b)) (∑'b : γ, m (s b)) :=
  by 
    rw [←supr_decode₂, ←tsum_supr_decode₂ _ m0 s]
    exact m_supr _

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_supr_sum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
  (m_supr : ∀ (s : ℕ → β), R (m (⨆i, s i)) (∑'i, m (s i))) (s : δ → β) (t : Finset δ) :
  R (m (⨆(d : _)(_ : d ∈ t), s d)) (∑d in t, m (s d)) :=
  by 
    cases t.nonempty_encodable 
    rw [supr_subtype']
    convert rel_supr_tsum m m0 R m_supr _ 
    rw [←Finset.tsum_subtype]
    assumption

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
  (m_supr : ∀ (s : ℕ → β), R (m (⨆i, s i)) (∑'i, m (s i))) (s₁ s₂ : β) : R (m (s₁⊔s₂)) (m s₁+m s₂) :=
  by 
    convert rel_supr_tsum m m0 R m_supr fun b => cond b s₁ s₂
    ·
      simp only [supr_bool_eq, cond]
    ·
      rw [tsum_fintype, Fintype.sum_bool, cond, cond]

end Encodable

variable[HasContinuousAdd α]

theorem tsum_add_tsum_compl {s : Set β} (hs : Summable (f ∘ coeₓ : s → α))
  (hsc : Summable (f ∘ coeₓ : «expr ᶜ» s → α)) : ((∑'x : s, f x)+∑'x : «expr ᶜ» s, f x) = ∑'x, f x :=
  (hs.has_sum.add_compl hsc.has_sum).tsum_eq.symm

theorem tsum_union_disjoint {s t : Set β} (hd : Disjoint s t) (hs : Summable (f ∘ coeₓ : s → α))
  (ht : Summable (f ∘ coeₓ : t → α)) : (∑'x : s ∪ t, f x) = (∑'x : s, f x)+∑'x : t, f x :=
  (hs.has_sum.add_disjoint hd ht.has_sum).tsum_eq

theorem tsum_even_add_odd {f : ℕ → α} (he : Summable fun k => f (2*k)) (ho : Summable fun k => f ((2*k)+1)) :
  ((∑'k, f (2*k))+∑'k, f ((2*k)+1)) = ∑'k, f k :=
  (he.has_sum.even_add_odd ho.has_sum).tsum_eq.symm

end tsum

section Prod

variable[AddCommMonoidₓ α][TopologicalSpace α][AddCommMonoidₓ γ][TopologicalSpace γ]

theorem HasSum.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasSum f a) (hg : HasSum g b) :
  HasSum (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ :=
  by 
    simp [HasSum, ←prod_mk_sum, Filter.Tendsto.prod_mk_nhds hf hg]

end Prod

section Pi

variable{ι : Type _}{π : α → Type _}[∀ x, AddCommMonoidₓ (π x)][∀ x, TopologicalSpace (π x)]

theorem Pi.has_sum {f : ι → ∀ x, π x} {g : ∀ x, π x} : HasSum f g ↔ ∀ x, HasSum (fun i => f i x) (g x) :=
  by 
    simp only [HasSum, tendsto_pi_nhds, sum_apply]

theorem Pi.summable {f : ι → ∀ x, π x} : Summable f ↔ ∀ x, Summable fun i => f i x :=
  by 
    simp only [Summable, Pi.has_sum, skolem]

theorem tsum_apply [∀ x, T2Space (π x)] {f : ι → ∀ x, π x} {x : α} (hf : Summable f) : (∑'i, f i) x = ∑'i, f i x :=
  (Pi.has_sum.mp hf.has_sum x).tsum_eq.symm

end Pi

section TopologicalGroup

variable[AddCommGroupₓ α][TopologicalSpace α][TopologicalAddGroup α]

variable{f g : β → α}{a a₁ a₂ : α}

theorem HasSum.neg (h : HasSum f a) : HasSum (fun b => -f b) (-a) :=
  by 
    simpa only using h.map (-AddMonoidHom.id α) continuous_neg

theorem Summable.neg (hf : Summable f) : Summable fun b => -f b :=
  hf.has_sum.neg.summable

theorem Summable.of_neg (hf : Summable fun b => -f b) : Summable f :=
  by 
    simpa only [neg_negₓ] using hf.neg

theorem summable_neg_iff : (Summable fun b => -f b) ↔ Summable f :=
  ⟨Summable.of_neg, Summable.neg⟩

theorem HasSum.sub (hf : HasSum f a₁) (hg : HasSum g a₂) : HasSum (fun b => f b - g b) (a₁ - a₂) :=
  by 
    simp only [sub_eq_add_neg]
    exact hf.add hg.neg

theorem Summable.sub (hf : Summable f) (hg : Summable g) : Summable fun b => f b - g b :=
  (hf.has_sum.sub hg.has_sum).Summable

theorem Summable.trans_sub (hg : Summable g) (hfg : Summable fun b => f b - g b) : Summable f :=
  by 
    simpa only [sub_add_cancel] using hfg.add hg

theorem summable_iff_of_summable_sub (hfg : Summable fun b => f b - g b) : Summable f ↔ Summable g :=
  ⟨fun hf =>
      hf.trans_sub$
        by 
          simpa only [neg_sub] using hfg.neg,
    fun hg => hg.trans_sub hfg⟩

theorem HasSum.update (hf : HasSum f a₁) (b : β) [DecidableEq β] (a : α) : HasSum (update f b a) ((a - f b)+a₁) :=
  by 
    convert (has_sum_ite_eq b _).add hf 
    ext b' 
    byCases' h : b' = b
    ·
      rw [h, update_same]
      simp only [eq_self_iff_true, if_true, sub_add_cancel]
    simp only [h, update_noteq, if_false, Ne.def, zero_addₓ, not_false_iff]

theorem Summable.update (hf : Summable f) (b : β) [DecidableEq β] (a : α) : Summable (update f b a) :=
  (hf.has_sum.update b a).Summable

theorem HasSum.has_sum_compl_iff {s : Set β} (hf : HasSum (f ∘ coeₓ : s → α) a₁) :
  HasSum (f ∘ coeₓ : «expr ᶜ» s → α) a₂ ↔ HasSum f (a₁+a₂) :=
  by 
    refine' ⟨fun h => hf.add_compl h, fun h => _⟩
    rw [has_sum_subtype_iff_indicator] at hf⊢
    rw [Set.indicator_compl]
    simpa only [add_sub_cancel'] using h.sub hf

theorem HasSum.has_sum_iff_compl {s : Set β} (hf : HasSum (f ∘ coeₓ : s → α) a₁) :
  HasSum f a₂ ↔ HasSum (f ∘ coeₓ : «expr ᶜ» s → α) (a₂ - a₁) :=
  Iff.symm$
    hf.has_sum_compl_iff.trans$
      by 
        rw [add_sub_cancel'_right]

theorem Summable.summable_compl_iff {s : Set β} (hf : Summable (f ∘ coeₓ : s → α)) :
  Summable (f ∘ coeₓ : «expr ᶜ» s → α) ↔ Summable f :=
  ⟨fun ⟨a, ha⟩ => (hf.has_sum.has_sum_compl_iff.1 ha).Summable,
    fun ⟨a, ha⟩ => (hf.has_sum.has_sum_iff_compl.1 ha).Summable⟩

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem finset.has_sum_compl_iff
(s : finset β) : «expr ↔ »(has_sum (λ
  x : {x // «expr ∉ »(x, s)}, f x) a, has_sum f «expr + »(a, «expr∑ in , »((i), s, f i))) :=
«expr $ »((s.has_sum f).has_sum_compl_iff.trans, by rw ["[", expr add_comm, "]"] [])

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem finset.has_sum_iff_compl
(s : finset β) : «expr ↔ »(has_sum f a, has_sum (λ
  x : {x // «expr ∉ »(x, s)}, f x) «expr - »(a, «expr∑ in , »((i), s, f i))) :=
(s.has_sum f).has_sum_iff_compl

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem finset.summable_compl_iff
(s : finset β) : «expr ↔ »(summable (λ x : {x // «expr ∉ »(x, s)}, f x), summable f) :=
(s.summable f).summable_compl_iff

theorem Set.Finite.summable_compl_iff {s : Set β} (hs : s.finite) : Summable (f ∘ coeₓ : «expr ᶜ» s → α) ↔ Summable f :=
  (hs.summable f).summable_compl_iff

theorem has_sum_ite_eq_extract [DecidableEq β] (hf : HasSum f a) (b : β) :
  HasSum (fun n => ite (n = b) 0 (f n)) (a - f b) :=
  by 
    convert hf.update b 0 using 1
    ·
      ext n 
      rw [Function.update_apply]
    ·
      rw [sub_add_eq_add_sub, zero_addₓ]

section tsum

variable[T2Space α]

theorem tsum_neg (hf : Summable f) : (∑'b, -f b) = -∑'b, f b :=
  hf.has_sum.neg.tsum_eq

theorem tsum_sub (hf : Summable f) (hg : Summable g) : (∑'b, f b - g b) = (∑'b, f b) - ∑'b, g b :=
  (hf.has_sum.sub hg.has_sum).tsum_eq

theorem sum_add_tsum_compl {s : Finset β} (hf : Summable f) :
  ((∑x in s, f x)+∑'x : «expr ᶜ» («expr↑ » s : Set β), f x) = ∑'x, f x :=
  ((s.has_sum f).add_compl (s.summable_compl_iff.2 hf).HasSum).tsum_eq.symm

/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_ite_eq_extract` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
theorem tsum_ite_eq_extract [DecidableEq β] (hf : Summable f) (b : β) : (∑'n, f n) = f b+∑'n, ite (n = b) 0 (f n) :=
  by 
    rw [(has_sum_ite_eq_extract hf.has_sum b).tsum_eq]
    exact (add_sub_cancel'_right _ _).symm

end tsum

/-!
### Sums on subtypes

If `s` is a finset of `α`, we show that the summability of `f` in the whole space and on the subtype
`univ - s` are equivalent, and relate their sums. For a function defined on `ℕ`, we deduce the
formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in `sum_add_tsum_nat_add`.
-/


section Subtype

theorem has_sum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
  HasSum (fun n => f (n+k)) a ↔ HasSum f (a+∑i in range k, f i) :=
  by 
    refine' Iff.trans _ (range k).has_sum_compl_iff 
    rw [←(notMemRangeEquiv k).symm.has_sum_iff]
    rfl

theorem summable_nat_add_iff {f : ℕ → α} (k : ℕ) : (Summable fun n => f (n+k)) ↔ Summable f :=
  Iff.symm$ (Equiv.addRight (∑i in range k, f i)).summable_iff_of_has_sum_iff$ fun a => (has_sum_nat_add_iff k).symm

theorem has_sum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
  HasSum (fun n => f (n+k)) (a - ∑i in range k, f i) ↔ HasSum f a :=
  by 
    simp [has_sum_nat_add_iff]

theorem sum_add_tsum_nat_add [T2Space α] {f : ℕ → α} (k : ℕ) (h : Summable f) :
  ((∑i in range k, f i)+∑'i, f (i+k)) = ∑'i, f i :=
  by 
    simpa only [add_commₓ] using ((has_sum_nat_add_iff k).1 ((summable_nat_add_iff k).2 h).HasSum).unique h.has_sum

theorem tsum_eq_zero_add [T2Space α] {f : ℕ → α} (hf : Summable f) : (∑'b, f b) = f 0+∑'b, f (b+1) :=
  by 
    simpa only [sum_range_one] using (sum_add_tsum_nat_add 1 hf).symm

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add
[t2_space α]
(f : exprℕ() → α) : tendsto (λ i, «expr∑' , »((k), f «expr + »(k, i))) at_top (expr𝓝() 0) :=
begin
  by_cases [expr hf, ":", expr summable f],
  { have [ident h₀] [":", expr «expr = »(λ
      i, «expr - »(«expr∑' , »((i), f i), «expr∑ in , »((j), range i, f j)), λ
      i, «expr∑' , »((k : exprℕ()), f «expr + »(k, i)))] [],
    { ext1 [] [ident i],
      rw ["[", expr sub_eq_iff_eq_add, ",", expr add_comm, ",", expr sum_add_tsum_nat_add i hf, "]"] [] },
    have [ident h₁] [":", expr tendsto (λ
      i : exprℕ(), «expr∑' , »((i), f i)) at_top (expr𝓝() «expr∑' , »((i), f i))] [":=", expr tendsto_const_nhds],
    simpa [] [] ["only"] ["[", expr h₀, ",", expr sub_self, "]"] [] ["using", expr tendsto.sub h₁ hf.has_sum.tendsto_sum_nat] },
  { convert [] [expr tendsto_const_nhds] [],
    ext1 [] [ident i],
    rw ["<-", expr summable_nat_add_iff i] ["at", ident hf],
    { exact [expr tsum_eq_zero_of_not_summable hf] },
    { apply_instance } }
end

end Subtype

end TopologicalGroup

section TopologicalRing

variable[Semiringₓ α][TopologicalSpace α][TopologicalRing α]

variable{f g : β → α}{a a₁ a₂ : α}

theorem HasSum.mul_left a₂ (h : HasSum f a₁) : HasSum (fun b => a₂*f b) (a₂*a₁) :=
  by 
    simpa only using h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)

theorem HasSum.mul_right a₂ (hf : HasSum f a₁) : HasSum (fun b => f b*a₂) (a₁*a₂) :=
  by 
    simpa only using hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)

theorem Summable.mul_left a (hf : Summable f) : Summable fun b => a*f b :=
  (hf.has_sum.mul_left _).Summable

theorem Summable.mul_right a (hf : Summable f) : Summable fun b => f b*a :=
  (hf.has_sum.mul_right _).Summable

section tsum

variable[T2Space α]

theorem Summable.tsum_mul_left a (hf : Summable f) : (∑'b, a*f b) = a*∑'b, f b :=
  (hf.has_sum.mul_left _).tsum_eq

theorem Summable.tsum_mul_right a (hf : Summable f) : (∑'b, f b*a) = (∑'b, f b)*a :=
  (hf.has_sum.mul_right _).tsum_eq

end tsum

end TopologicalRing

section ConstSmul

variable{R :
    Type
      _}[Monoidₓ
      R][TopologicalSpace
      R][TopologicalSpace α][AddCommMonoidₓ α][DistribMulAction R α][HasContinuousSmul R α]{f : β → α}

theorem HasSum.const_smul {a : α} {r : R} (hf : HasSum f a) : HasSum (fun z => r • f z) (r • a) :=
  hf.map (DistribMulAction.toAddMonoidHom α r) (continuous_const.smul continuous_id)

theorem Summable.const_smul {r : R} (hf : Summable f) : Summable fun z => r • f z :=
  hf.has_sum.const_smul.summable

theorem tsum_const_smul [T2Space α] {r : R} (hf : Summable f) : (∑'z, r • f z) = r • ∑'z, f z :=
  hf.has_sum.const_smul.tsum_eq

end ConstSmul

section SmulConst

variable{R :
    Type
      _}[Semiringₓ
      R][TopologicalSpace R][TopologicalSpace α][AddCommMonoidₓ α][Module R α][HasContinuousSmul R α]{f : β → R}

theorem HasSum.smul_const {a : α} {r : R} (hf : HasSum f r) : HasSum (fun z => f z • a) (r • a) :=
  hf.map ((smulAddHom R α).flip a) (continuous_id.smul continuous_const)

theorem Summable.smul_const {a : α} (hf : Summable f) : Summable fun z => f z • a :=
  hf.has_sum.smul_const.summable

theorem tsum_smul_const [T2Space α] {a : α} (hf : Summable f) : (∑'z, f z • a) = (∑'z, f z) • a :=
  hf.has_sum.smul_const.tsum_eq

end SmulConst

section DivisionRing

variable[DivisionRing α][TopologicalSpace α][TopologicalRing α]{f g : β → α}{a a₁ a₂ : α}

theorem HasSum.div_const (h : HasSum f a) (b : α) : HasSum (fun x => f x / b) (a / b) :=
  by 
    simp only [div_eq_mul_inv, h.mul_right (b⁻¹)]

theorem Summable.div_const (h : Summable f) (b : α) : Summable fun x => f x / b :=
  (h.has_sum.div_const b).Summable

theorem has_sum_mul_left_iff (h : a₂ ≠ 0) : HasSum f a₁ ↔ HasSum (fun b => a₂*f b) (a₂*a₁) :=
  ⟨HasSum.mul_left _,
    fun H =>
      by 
        simpa only [inv_mul_cancel_left₀ h] using H.mul_left (a₂⁻¹)⟩

theorem has_sum_mul_right_iff (h : a₂ ≠ 0) : HasSum f a₁ ↔ HasSum (fun b => f b*a₂) (a₁*a₂) :=
  ⟨HasSum.mul_right _,
    fun H =>
      by 
        simpa only [mul_inv_cancel_right₀ h] using H.mul_right (a₂⁻¹)⟩

theorem summable_mul_left_iff (h : a ≠ 0) : Summable f ↔ Summable fun b => a*f b :=
  ⟨fun H => H.mul_left _,
    fun H =>
      by 
        simpa only [inv_mul_cancel_left₀ h] using H.mul_left (a⁻¹)⟩

theorem summable_mul_right_iff (h : a ≠ 0) : Summable f ↔ Summable fun b => f b*a :=
  ⟨fun H => H.mul_right _,
    fun H =>
      by 
        simpa only [mul_inv_cancel_right₀ h] using H.mul_right (a⁻¹)⟩

theorem tsum_mul_left [T2Space α] : (∑'x, a*f x) = a*∑'x, f x :=
  if hf : Summable f then hf.tsum_mul_left a else
    if ha : a = 0 then
      by 
        simp [ha]
    else
      by 
        rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt (summable_mul_left_iff ha).2 hf),
          mul_zero]

theorem tsum_mul_right [T2Space α] : (∑'x, f x*a) = (∑'x, f x)*a :=
  if hf : Summable f then hf.tsum_mul_right a else
    if ha : a = 0 then
      by 
        simp [ha]
    else
      by 
        rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt (summable_mul_right_iff ha).2 hf),
          zero_mul]

end DivisionRing

section OrderTopology

variable[OrderedAddCommMonoid α][TopologicalSpace α][OrderClosedTopology α]

variable{f g : β → α}{a a₁ a₂ : α}

theorem has_sum_le (h : ∀ b, f b ≤ g b) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg$ fun s => sum_le_sum$ fun b _ => h b

@[mono]
theorem has_sum_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
  has_sum_le h hf hg

theorem has_sum_le_of_sum_le (hf : HasSum f a) (h : ∀ (s : Finset β), (∑b in s, f b) ≤ a₂) : a ≤ a₂ :=
  le_of_tendsto' hf h

theorem le_has_sum_of_le_sum (hf : HasSum f a) (h : ∀ (s : Finset β), a₂ ≤ ∑b in s, f b) : a₂ ≤ a :=
  ge_of_tendsto' hf h

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum_le_inj
{g : γ → α}
(i : β → γ)
(hi : injective i)
(hs : ∀ c «expr ∉ » set.range i, «expr ≤ »(0, g c))
(h : ∀ b, «expr ≤ »(f b, g (i b)))
(hf : has_sum f a₁)
(hg : has_sum g a₂) : «expr ≤ »(a₁, a₂) :=
have has_sum (λ c, (partial_inv i c).cases_on' 0 f) a₁, begin
  refine [expr (has_sum_iff_has_sum_of_ne_zero_bij «expr ∘ »(i, coe) _ _ _).2 hf],
  { exact [expr assume c₁ c₂ eq, hi eq] },
  { intros [ident c, ident hc],
    rw ["[", expr mem_support, "]"] ["at", ident hc],
    cases [expr eq, ":", expr partial_inv i c] ["with", ident b]; rw [expr eq] ["at", ident hc],
    { contradiction },
    { rw ["[", expr partial_inv_of_injective hi, "]"] ["at", ident eq],
      exact [expr ⟨⟨b, hc⟩, eq⟩] } },
  { assume [binders (c)],
    simp [] [] [] ["[", expr partial_inv_left hi, ",", expr option.cases_on', "]"] [] [] }
end,
begin
  refine [expr has_sum_le (assume c, _) this hg],
  by_cases [expr «expr ∈ »(c, set.range i)],
  { rcases [expr h, "with", "⟨", ident b, ",", ident rfl, "⟩"],
    rw ["[", expr partial_inv_left hi, ",", expr option.cases_on', "]"] [],
    exact [expr h _] },
  { have [] [":", expr «expr = »(partial_inv i c, none)] [":=", expr dif_neg h],
    rw ["[", expr this, ",", expr option.cases_on', "]"] [],
    exact [expr hs _ h] }
end

theorem tsum_le_tsum_of_inj {g : γ → α} (i : β → γ) (hi : injective i) (hs : ∀ c (_ : c ∉ Set.Range i), 0 ≤ g c)
  (h : ∀ b, f b ≤ g (i b)) (hf : Summable f) (hg : Summable g) : tsum f ≤ tsum g :=
  has_sum_le_inj i hi hs h hf.has_sum hg.has_sum

theorem sum_le_has_sum (s : Finset β) (hs : ∀ b (_ : b ∉ s), 0 ≤ f b) (hf : HasSum f a) : (∑b in s, f b) ≤ a :=
  ge_of_tendsto hf (eventually_at_top.2 ⟨s, fun t hst => sum_le_sum_of_subset_of_nonneg hst$ fun b hbt hbs => hs b hbs⟩)

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_lub_has_sum
(h : ∀ b, «expr ≤ »(0, f b))
(hf : has_sum f a) : is_lub (set.range (λ s : finset β, «expr∑ in , »((b), s, f b))) a :=
is_lub_of_tendsto (finset.sum_mono_set_of_nonneg h) hf

theorem le_has_sum (hf : HasSum f a) (b : β) (hb : ∀ b' (_ : b' ≠ b), 0 ≤ f b') : f b ≤ a :=
  calc f b = ∑b in {b}, f b := Finset.sum_singleton.symm 
    _ ≤ a :=
    sum_le_has_sum _
      (by 
        convert hb 
        simp )
      hf
    

theorem sum_le_tsum {f : β → α} (s : Finset β) (hs : ∀ b (_ : b ∉ s), 0 ≤ f b) (hf : Summable f) :
  (∑b in s, f b) ≤ ∑'b, f b :=
  sum_le_has_sum s hs hf.has_sum

theorem le_tsum (hf : Summable f) (b : β) (hb : ∀ b' (_ : b' ≠ b), 0 ≤ f b') : f b ≤ ∑'b, f b :=
  le_has_sum (Summable.has_sum hf) b hb

theorem tsum_le_tsum (h : ∀ b, f b ≤ g b) (hf : Summable f) (hg : Summable g) : (∑'b, f b) ≤ ∑'b, g b :=
  has_sum_le h hf.has_sum hg.has_sum

@[mono]
theorem tsum_mono (hf : Summable f) (hg : Summable g) (h : f ≤ g) : (∑'n, f n) ≤ ∑'n, g n :=
  tsum_le_tsum h hf hg

theorem tsum_le_of_sum_le (hf : Summable f) (h : ∀ (s : Finset β), (∑b in s, f b) ≤ a₂) : (∑'b, f b) ≤ a₂ :=
  has_sum_le_of_sum_le hf.has_sum h

theorem tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ (s : Finset β), (∑b in s, f b) ≤ a₂) : (∑'b, f b) ≤ a₂ :=
  by 
    byCases' hf : Summable f
    ·
      exact tsum_le_of_sum_le hf h
    ·
      rw [tsum_eq_zero_of_not_summable hf]
      exact ha₂

theorem HasSum.nonneg (h : ∀ b, 0 ≤ g b) (ha : HasSum g a) : 0 ≤ a :=
  has_sum_le h has_sum_zero ha

theorem HasSum.nonpos (h : ∀ b, g b ≤ 0) (ha : HasSum g a) : a ≤ 0 :=
  has_sum_le h ha has_sum_zero

theorem tsum_nonneg (h : ∀ b, 0 ≤ g b) : 0 ≤ ∑'b, g b :=
  by 
    byCases' hg : Summable g
    ·
      exact hg.has_sum.nonneg h
    ·
      simp [tsum_eq_zero_of_not_summable hg]

theorem tsum_nonpos (h : ∀ b, f b ≤ 0) : (∑'b, f b) ≤ 0 :=
  by 
    byCases' hf : Summable f
    ·
      exact hf.has_sum.nonpos h
    ·
      simp [tsum_eq_zero_of_not_summable hf]

end OrderTopology

section OrderedTopologicalGroup

variable[OrderedAddCommGroup
      α][TopologicalSpace α][TopologicalAddGroup α][OrderClosedTopology α]{f g : β → α}{a₁ a₂ : α}

theorem has_sum_lt {i : β} (h : ∀ (b : β), f b ≤ g b) (hi : f i < g i) (hf : HasSum f a₁) (hg : HasSum g a₂) :
  a₁ < a₂ :=
  have  : update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have  : ((0 - f i)+a₁) ≤ (0 - g i)+a₂ := has_sum_le this (hf.update i 0) (hg.update i 0)
  by 
    simpa only [zero_sub, add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this

@[mono]
theorem has_sum_strict_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h 
  has_sum_lt hle hi hf hg

theorem tsum_lt_tsum {i : β} (h : ∀ (b : β), f b ≤ g b) (hi : f i < g i) (hf : Summable f) (hg : Summable g) :
  (∑'n, f n) < ∑'n, g n :=
  has_sum_lt h hi hf.has_sum hg.has_sum

@[mono]
theorem tsum_strict_mono (hf : Summable f) (hg : Summable g) (h : f < g) : (∑'n, f n) < ∑'n, g n :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h 
  tsum_lt_tsum hle hi hf hg

theorem tsum_pos (hsum : Summable g) (hg : ∀ b, 0 ≤ g b) (i : β) (hi : 0 < g i) : 0 < ∑'b, g b :=
  by 
    rw [←tsum_zero]
    exact tsum_lt_tsum hg hi summable_zero hsum

end OrderedTopologicalGroup

section CanonicallyOrdered

variable[CanonicallyOrderedAddMonoid α][TopologicalSpace α][OrderClosedTopology α]

variable{f : β → α}{a : α}

theorem le_has_sum' (hf : HasSum f a) (b : β) : f b ≤ a :=
  le_has_sum hf b$ fun _ _ => zero_le _

theorem le_tsum' (hf : Summable f) (b : β) : f b ≤ ∑'b, f b :=
  le_tsum hf b$ fun _ _ => zero_le _

theorem has_sum_zero_iff : HasSum f 0 ↔ ∀ x, f x = 0 :=
  by 
    refine' ⟨_, fun h => _⟩
    ·
      contrapose! 
      exact fun ⟨x, hx⟩ h => irrefl _ (lt_of_lt_of_leₓ (pos_iff_ne_zero.2 hx) (le_has_sum' h x))
    ·
      convert has_sum_zero 
      exact funext h

theorem tsum_eq_zero_iff (hf : Summable f) : (∑'i, f i) = 0 ↔ ∀ x, f x = 0 :=
  by 
    rw [←has_sum_zero_iff, hf.has_sum_iff]

theorem tsum_ne_zero_iff (hf : Summable f) : (∑'i, f i) ≠ 0 ↔ ∃ x, f x ≠ 0 :=
  by 
    rw [Ne.def, tsum_eq_zero_iff hf, not_forall]

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_lub_has_sum' (hf : has_sum f a) : is_lub (set.range (λ s : finset β, «expr∑ in , »((b), s, f b))) a :=
is_lub_of_tendsto (finset.sum_mono_set f) hf

end CanonicallyOrdered

section UniformGroup

variable[AddCommGroupₓ α][UniformSpace α]

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable_iff_cauchy_seq_finset
[complete_space α]
{f : β → α} : «expr ↔ »(summable f, cauchy_seq (λ s : finset β, «expr∑ in , »((b), s, f b))) :=
cauchy_map_iff_exists_tendsto.symm

variable[UniformAddGroup α]{f g : β → α}{a a₁ a₂ : α}

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cauchy_seq_finset_iff_vanishing : «expr ↔ »(cauchy_seq (λ
  s : finset β, «expr∑ in , »((b), s, f b)), ∀
 e «expr ∈ » expr𝓝() (0 : α), «expr∃ , »((s : finset β), ∀
  t, disjoint t s → «expr ∈ »(«expr∑ in , »((b), t, f b), e))) :=
begin
  simp [] [] ["only"] ["[", expr cauchy_seq, ",", expr cauchy_map_iff, ",", expr and_iff_right at_top_ne_bot, ",", expr prod_at_top_at_top_eq, ",", expr uniformity_eq_comap_nhds_zero α, ",", expr tendsto_comap_iff, ",", expr («expr ∘ »), "]"] [] [],
  rw ["[", expr tendsto_at_top', "]"] [],
  split,
  { assume [binders (h e he)],
    rcases [expr h e he, "with", "⟨", "⟨", ident s₁, ",", ident s₂, "⟩", ",", ident h, "⟩"],
    use ["[", expr «expr ∪ »(s₁, s₂), "]"],
    assume [binders (t ht)],
    specialize [expr h («expr ∪ »(s₁, s₂), «expr ∪ »(«expr ∪ »(s₁, s₂), t)) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩],
    simpa [] [] ["only"] ["[", expr finset.sum_union ht.symm, ",", expr add_sub_cancel', "]"] [] ["using", expr h] },
  { assume [binders (h e he)],
    rcases [expr exists_nhds_half_neg he, "with", "⟨", ident d, ",", ident hd, ",", ident hde, "⟩"],
    rcases [expr h d hd, "with", "⟨", ident s, ",", ident h, "⟩"],
    use ["[", expr (s, s), "]"],
    rintros ["⟨", ident t₁, ",", ident t₂, "⟩", "⟨", ident ht₁, ",", ident ht₂, "⟩"],
    have [] [":", expr «expr = »(«expr - »(«expr∑ in , »((b), t₂, f b), «expr∑ in , »((b), t₁, f b)), «expr - »(«expr∑ in , »((b), «expr \ »(t₂, s), f b), «expr∑ in , »((b), «expr \ »(t₁, s), f b)))] [],
    { simp [] [] ["only"] ["[", expr (finset.sum_sdiff ht₁).symm, ",", expr (finset.sum_sdiff ht₂).symm, ",", expr add_sub_add_right_eq_sub, "]"] [] [] },
    simp [] [] ["only"] ["[", expr this, "]"] [] [],
    exact [expr hde _ (h _ finset.sdiff_disjoint) _ (h _ finset.sdiff_disjoint)] }
end

attribute [local instance] TopologicalAddGroup.regular_space

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_at_top_zero
[t1_space α]
(f : β → α) : tendsto (λ s : finset β, «expr∑' , »((b : {x // «expr ∉ »(x, s)}), f b)) at_top (expr𝓝() 0) :=
begin
  by_cases [expr H, ":", expr summable f],
  { assume [binders (e he)],
    rcases [expr nhds_is_closed he, "with", "⟨", ident o, ",", ident ho, ",", ident oe, ",", ident o_closed, "⟩"],
    simp [] [] ["only"] ["[", expr le_eq_subset, ",", expr set.mem_preimage, ",", expr mem_at_top_sets, ",", expr filter.mem_map, ",", expr ge_iff_le, "]"] [] [],
    obtain ["⟨", ident s, ",", ident hs, "⟩", ":", expr «expr∃ , »((s : finset β), ∀
      t : finset β, disjoint t s → «expr ∈ »(«expr∑ in , »((b : β), t, f b), o)), ":=", expr cauchy_seq_finset_iff_vanishing.1 (tendsto.cauchy_seq H.has_sum) o ho],
    refine [expr ⟨s, λ a sa, oe _⟩],
    have [ident A] [":", expr summable (λ b : {x // «expr ∉ »(x, a)}, f b)] [":=", expr a.summable_compl_iff.2 H],
    apply [expr is_closed.mem_of_tendsto o_closed A.has_sum (eventually_of_forall (λ b, _))],
    have [] [":", expr disjoint (finset.image (λ i : {x // «expr ∉ »(x, a)}, (i : β)) b) s] [],
    { apply [expr disjoint_left.2 (λ i hi his, _)],
      rcases [expr mem_image.1 hi, "with", "⟨", ident i', ",", ident hi', ",", ident rfl, "⟩"],
      exact [expr i'.2 (sa his)] },
    convert [] [expr hs _ this] ["using", 1],
    rw [expr sum_image] [],
    assume [binders (i hi j hj hij)],
    exact [expr subtype.ext hij] },
  { convert [] [expr tendsto_const_nhds] [],
    ext [] [ident s] [],
    apply [expr tsum_eq_zero_of_not_summable],
    rwa [expr finset.summable_compl_iff] [] }
end

variable[CompleteSpace α]

theorem summable_iff_vanishing :
  Summable f ↔ ∀ e (_ : e ∈ 𝓝 (0 : α)), ∃ s : Finset β, ∀ t, Disjoint t s → (∑b in t, f b) ∈ e :=
  by 
    rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing]

theorem Summable.summable_of_eq_zero_or_self (hf : Summable f) (h : ∀ b, g b = 0 ∨ g b = f b) : Summable g :=
  summable_iff_vanishing.2$
    fun e he =>
      let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he
      ⟨s,
        fun t ht =>
          have eq : (∑b in t.filter fun b => g b = f b, f b) = ∑b in t, g b :=
            calc (∑b in t.filter fun b => g b = f b, f b) = ∑b in t.filter fun b => g b = f b, g b :=
              Finset.sum_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm 
              _ = ∑b in t, g b :=
              by 
                refine' Finset.sum_subset (Finset.filter_subset _ _) _ 
                intro b hbt hb 
                simp only [· ∉ ·, Finset.mem_filter, and_iff_right hbt] at hb 
                exact (h b).resolve_right hb 
              
          Eq ▸ hs _$ Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

protected theorem Summable.indicator (hf : Summable f) (s : Set β) : Summable (s.indicator f) :=
  hf.summable_of_eq_zero_or_self$ Set.indicator_eq_zero_or_self _ _

theorem Summable.comp_injective {i : γ → β} (hf : Summable f) (hi : injective i) : Summable (f ∘ i) :=
  by 
    simpa only [Set.indicator_range_comp] using (hi.summable_iff _).2 (hf.indicator (Set.Range i))
    exact fun x hx => Set.indicator_of_not_mem hx _

theorem Summable.subtype (hf : Summable f) (s : Set β) : Summable (f ∘ coeₓ : s → α) :=
  hf.comp_injective Subtype.coe_injective

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable_subtype_and_compl
{s : set β} : «expr ↔ »(«expr ∧ »(summable (λ x : s, f x), summable (λ x : «expr ᶜ»(s), f x)), summable f) :=
⟨and_imp.2 summable.add_compl, λ h, ⟨h.subtype s, h.subtype «expr ᶜ»(s)⟩⟩

theorem Summable.sigma_factor {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) (b : β) :
  Summable fun c => f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective

theorem Summable.sigma [T1Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
  Summable fun b => ∑'c, f ⟨b, c⟩ :=
  ha.sigma' fun b => ha.sigma_factor b

theorem Summable.prod_factor {f : β × γ → α} (h : Summable f) (b : β) : Summable fun c => f (b, c) :=
  h.comp_injective$ fun c₁ c₂ h => (Prod.ext_iff.1 h).2

theorem tsum_sigma [T1Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
  (∑'p, f p) = ∑'b c, f ⟨b, c⟩ :=
  tsum_sigma' (fun b => ha.sigma_factor b) ha

theorem tsum_prod [T1Space α] {f : β × γ → α} (h : Summable f) : (∑'p, f p) = ∑'b c, f ⟨b, c⟩ :=
  tsum_prod' h h.prod_factor

theorem tsum_comm [T1Space α] {f : β → γ → α} (h : Summable (Function.uncurry f)) : (∑'c b, f b c) = ∑'b c, f b c :=
  tsum_comm' h h.prod_factor h.prod_symm.prod_factor

end UniformGroup

section TopologicalGroup

variable{G : Type _}[TopologicalSpace G][AddCommGroupₓ G][TopologicalAddGroup G]{f : α → G}

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem summable.vanishing
(hf : summable f)
{{e : set G}}
(he : «expr ∈ »(e, expr𝓝() (0 : G))) : «expr∃ , »((s : finset α), ∀
 t, disjoint t s → «expr ∈ »(«expr∑ in , »((k), t, f k), e)) :=
begin
  letI [] [":", expr uniform_space G] [":=", expr topological_add_group.to_uniform_space G],
  letI [] [":", expr uniform_add_group G] [":=", expr topological_add_group_is_uniform],
  rcases [expr hf, "with", "⟨", ident y, ",", ident hy, "⟩"],
  exact [expr cauchy_seq_finset_iff_vanishing.1 hy.cauchy_seq e he]
end

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
theorem Summable.tendsto_cofinite_zero (hf : Summable f) : tendsto f cofinite (𝓝 0) :=
  by 
    intro e he 
    rw [Filter.mem_map]
    rcases hf.vanishing he with ⟨s, hs⟩
    refine' s.eventually_cofinite_nmem.mono fun x hx => _
    ·
      simpa using hs {x} (disjoint_singleton_left.2 hx)

theorem Summable.tendsto_at_top_zero {f : ℕ → G} (hf : Summable f) : tendsto f at_top (𝓝 0) :=
  by 
    rw [←Nat.cofinite_eq_at_top]
    exact hf.tendsto_cofinite_zero

theorem Summable.tendsto_top_of_pos {α : Type _} [LinearOrderedField α] [TopologicalSpace α] [OrderTopology α]
  {f : ℕ → α} (hf : Summable (f⁻¹)) (hf' : ∀ n, 0 < f n) : tendsto f at_top at_top :=
  by 
    rw
      [show f = f⁻¹⁻¹by 
        ext 
        simp ]
    apply Filter.Tendsto.inv_tendsto_zero 
    apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (Summable.tendsto_at_top_zero hf)
    rw [eventually_iff_exists_mem]
    refine' ⟨Set.Ioi 0, Ioi_mem_at_top _, fun _ _ => _⟩
    rw [Set.mem_Ioi, inv_eq_one_div, one_div, Pi.inv_apply, _root_.inv_pos]
    exact hf' _

end TopologicalGroup

section LinearOrderₓ

/-! For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/


theorem has_sum_of_is_lub_of_nonneg [LinearOrderedAddCommMonoid β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
  (b : β) (h : ∀ b, 0 ≤ f b) (hf : IsLub (Set.Range fun s => ∑a in s, f a) b) : HasSum f b :=
  tendsto_at_top_is_lub (Finset.sum_mono_set_of_nonneg h) hf

theorem has_sum_of_is_lub [CanonicallyLinearOrderedAddMonoid β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
  (b : β) (hf : IsLub (Set.Range fun s => ∑a in s, f a) b) : HasSum f b :=
  tendsto_at_top_is_lub (Finset.sum_mono_set f) hf

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable_abs_iff
[linear_ordered_add_comm_group β]
[uniform_space β]
[uniform_add_group β]
[complete_space β]
{f : α → β} : «expr ↔ »(summable (λ x, «expr| |»(f x)), summable f) :=
have h1 : ∀ x : {x | «expr ≤ »(0, f x)}, «expr = »(«expr| |»(f x), f x) := λ x, abs_of_nonneg x.2,
have h2 : ∀
x : «expr ᶜ»({x | «expr ≤ »(0, f x)}), «expr = »(«expr| |»(f x), «expr- »(f x)) := λ x, abs_of_neg (not_le.1 x.2),
calc
  «expr ↔ »(summable (λ
    x, «expr| |»(f x)), «expr ∧ »(summable (λ
     x : {x | «expr ≤ »(0, f x)}, «expr| |»(f x)), summable (λ
     x : «expr ᶜ»({x | «expr ≤ »(0, f x)}), «expr| |»(f x)))) : summable_subtype_and_compl.symm
  «expr ↔ »(..., «expr ∧ »(summable (λ
     x : {x | «expr ≤ »(0, f x)}, f x), summable (λ
     x : «expr ᶜ»({x | «expr ≤ »(0, f x)}), «expr- »(f x)))) : by simp [] [] ["only"] ["[", expr h1, ",", expr h2, "]"] [] []
  «expr ↔ »(..., _) : by simp [] [] ["only"] ["[", expr summable_neg_iff, ",", expr summable_subtype_and_compl, "]"] [] []

alias summable_abs_iff ↔ Summable.of_abs Summable.abs

end LinearOrderₓ

section CauchySeq

open Filter

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `nnreal`s, then the original sequence is a Cauchy sequence. -/
theorem cauchy_seq_of_edist_le_of_summable
[pseudo_emetric_space α]
{f : exprℕ() → α}
(d : exprℕ() → «exprℝ≥0»())
(hf : ∀ n, «expr ≤ »(edist (f n) (f n.succ), d n))
(hd : summable d) : cauchy_seq f :=
begin
  refine [expr emetric.cauchy_seq_iff_nnreal.2 (λ ε εpos, _)],
  replace [ident hd] [":", expr cauchy_seq (λ
    n : exprℕ(), «expr∑ in , »((x), range n, d x))] [":=", expr let ⟨_, H⟩ := hd in H.tendsto_sum_nat.cauchy_seq],
  refine [expr (metric.cauchy_seq_iff'.1 hd ε (nnreal.coe_pos.2 εpos)).imp (λ N hN n hn, _)],
  have [ident hsum] [] [":=", expr hN n hn],
  rw ["[", expr dist_nndist, ",", expr nnreal.nndist_eq, ",", "<-", expr sum_range_add_sum_Ico _ hn, ",", expr add_tsub_cancel_left, "]"] ["at", ident hsum],
  norm_cast ["at", ident hsum],
  replace [ident hsum] [] [":=", expr lt_of_le_of_lt (le_max_left _ _) hsum],
  rw [expr edist_comm] [],
  apply [expr lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn (λ k _ _, hf k))],
  assumption_mod_cast
end

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the distance between consecutive points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
theorem cauchy_seq_of_dist_le_of_summable
[pseudo_metric_space α]
{f : exprℕ() → α}
(d : exprℕ() → exprℝ())
(hf : ∀ n, «expr ≤ »(dist (f n) (f n.succ), d n))
(hd : summable d) : cauchy_seq f :=
begin
  refine [expr metric.cauchy_seq_iff'.2 (λ ε εpos, _)],
  replace [ident hd] [":", expr cauchy_seq (λ
    n : exprℕ(), «expr∑ in , »((x), range n, d x))] [":=", expr let ⟨_, H⟩ := hd in H.tendsto_sum_nat.cauchy_seq],
  refine [expr (metric.cauchy_seq_iff'.1 hd ε εpos).imp (λ N hN n hn, _)],
  have [ident hsum] [] [":=", expr hN n hn],
  rw ["[", expr real.dist_eq, ",", "<-", expr sum_Ico_eq_sub _ hn, "]"] ["at", ident hsum],
  calc
    «expr = »(dist (f n) (f N), dist (f N) (f n)) : dist_comm _ _
    «expr ≤ »(..., «expr∑ in , »((x), Ico N n, d x)) : dist_le_Ico_sum_of_dist_le hn (λ k _ _, hf k)
    «expr ≤ »(..., «expr| |»(«expr∑ in , »((x), Ico N n, d x))) : le_abs_self _
    «expr < »(..., ε) : hsum
end

theorem cauchy_seq_of_summable_dist [PseudoMetricSpace α] {f : ℕ → α} (h : Summable fun n => dist (f n) (f n.succ)) :
  CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ (fun _ => le_reflₓ _) h

theorem dist_le_tsum_of_dist_le_of_tendsto [PseudoMetricSpace α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : Summable d) {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ ∑'m, d (n+m) :=
  by 
    refine' le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_at_top.2 ⟨n, fun m hnm => _⟩)
    refine' le_transₓ (dist_le_Ico_sum_of_dist_le hnm fun k _ _ => hf k) _ 
    rw [sum_Ico_eq_sum_range]
    refine' sum_le_tsum (range _) (fun _ _ => le_transₓ dist_nonneg (hf _)) _ 
    exact hd.comp_injective (add_right_injective n)

theorem dist_le_tsum_of_dist_le_of_tendsto₀ [PseudoMetricSpace α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : Summable d) {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ tsum d :=
  by 
    simpa only [zero_addₓ] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0

theorem dist_le_tsum_dist_of_tendsto [PseudoMetricSpace α] {f : ℕ → α} (h : Summable fun n => dist (f n) (f n.succ))
  {a : α} (ha : tendsto f at_top (𝓝 a)) n : dist (f n) a ≤ ∑'m, dist (f (n+m)) (f (n+m).succ) :=
  show dist (f n) a ≤ ∑'m, (fun x => dist (f x) (f x.succ)) (n+m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n => dist (f n) (f n.succ)) (fun _ => le_reflₓ _) h ha n

theorem dist_le_tsum_dist_of_tendsto₀ [PseudoMetricSpace α] {f : ℕ → α} (h : Summable fun n => dist (f n) (f n.succ))
  {a : α} (ha : tendsto f at_top (𝓝 a)) : dist (f 0) a ≤ ∑'n, dist (f n) (f n.succ) :=
  by 
    simpa only [zero_addₓ] using dist_le_tsum_dist_of_tendsto h ha 0

end CauchySeq

/-! ## Multipliying two infinite sums

In this section, we prove various results about `(∑' x : β, f x) * (∑' y : γ, g y)`. Note that we
always assume that the family `λ x : β × γ, f x.1 * g x.2` is summable, since there is no way to
deduce this from the summmabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `analysis/normed_space/basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

### Arbitrary index types
-/


section tsum_mul_tsum

variable[TopologicalSpace α][RegularSpace α][Semiringₓ α][TopologicalRing α]{f : β → α}{g : γ → α}{s t u : α}

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_sum.mul_eq
(hf : has_sum f s)
(hg : has_sum g t)
(hfg : has_sum (λ x : «expr × »(β, γ), «expr * »(f x.1, g x.2)) u) : «expr = »(«expr * »(s, t), u) :=
have key₁ : has_sum (λ b, «expr * »(f b, t)) «expr * »(s, t), from hf.mul_right t,
have this : ∀ b : β, has_sum (λ c : γ, «expr * »(f b, g c)) «expr * »(f b, t), from λ b, hg.mul_left (f b),
have key₂ : has_sum (λ b, «expr * »(f b, t)) u, from has_sum.prod_fiberwise hfg this,
key₁.unique key₂

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_sum.mul
(hf : has_sum f s)
(hg : has_sum g t)
(hfg : summable (λ
  x : «expr × »(β, γ), «expr * »(f x.1, g x.2))) : has_sum (λ
 x : «expr × »(β, γ), «expr * »(f x.1, g x.2)) «expr * »(s, t) :=
let ⟨u, hu⟩ := hfg in
«expr ▸ »((hf.mul_eq hg hu).symm, hu)

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are abolutely summable. -/
theorem tsum_mul_tsum
(hf : summable f)
(hg : summable g)
(hfg : summable (λ
  x : «expr × »(β, γ), «expr * »(f x.1, g x.2))) : «expr = »(«expr * »(«expr∑' , »((x), f x), «expr∑' , »((y), g y)), «expr∑' , »((z : «expr × »(β, γ)), «expr * »(f z.1, g z.2))) :=
hf.has_sum.mul_eq hg.has_sum hfg.has_sum

end tsum_mul_tsum

section CauchyProduct

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `finset.range (n+1)`
involving `nat` substraction.
In order to avoid `nat` substraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n` -/


variable{f : ℕ → α}{g : ℕ → α}

open Finset

variable[TopologicalSpace α][Semiringₓ α]

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal
{f
 g : exprℕ() → α} : «expr ↔ »(summable (λ
  x : «expr × »(exprℕ(), exprℕ()), «expr * »(f x.1, g x.2)), summable (λ
  x : «exprΣ , »((n : exprℕ()), nat.antidiagonal n), «expr * »(f (x.2 : «expr × »(exprℕ(), exprℕ())).1, g (x.2 : «expr × »(exprℕ(), exprℕ())).2))) :=
nat.sigma_antidiagonal_equiv_prod.summable_iff.symm

variable[RegularSpace α][TopologicalRing α]

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable_sum_mul_antidiagonal_of_summable_mul
{f g : exprℕ() → α}
(h : summable (λ
  x : «expr × »(exprℕ(), exprℕ()), «expr * »(f x.1, g x.2))) : summable (λ
 n, «expr∑ in , »((kl), nat.antidiagonal n, «expr * »(f kl.1, g kl.2))) :=
begin
  rw [expr summable_mul_prod_iff_summable_mul_sigma_antidiagonal] ["at", ident h],
  conv [] [] { congr,
    funext,
    rw ["[", "<-", expr finset.sum_finset_coe, ",", "<-", expr tsum_fintype, "]"] },
  exact [expr h.sigma' (λ n, (has_sum_fintype _).summable)]
end

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The Cauchy product formula for the product of two infinites sums indexed by `ℕ`,
    expressed by summing on `finset.nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
    if `f` and `g` are absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal
(hf : summable f)
(hg : summable g)
(hfg : summable (λ
  x : «expr × »(exprℕ(), exprℕ()), «expr * »(f x.1, g x.2))) : «expr = »(«expr * »(«expr∑' , »((n), f n), «expr∑' , »((n), g n)), «expr∑' , »((n), «expr∑ in , »((kl), nat.antidiagonal n, «expr * »(f kl.1, g kl.2)))) :=
begin
  conv_rhs [] [] { congr,
    funext,
    rw ["[", "<-", expr finset.sum_finset_coe, ",", "<-", expr tsum_fintype, "]"] },
  rw ["[", expr tsum_mul_tsum hf hg hfg, ",", "<-", expr nat.sigma_antidiagonal_equiv_prod.tsum_eq (_ : «expr × »(exprℕ(), exprℕ()) → α), "]"] [],
  exact [expr tsum_sigma' (λ
    n, (has_sum_fintype _).summable) (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg)]
end

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable_sum_mul_range_of_summable_mul
{f g : exprℕ() → α}
(h : summable (λ
  x : «expr × »(exprℕ(), exprℕ()), «expr * »(f x.1, g x.2))) : summable (λ
 n, «expr∑ in , »((k), range «expr + »(n, 1), «expr * »(f k, g «expr - »(n, k)))) :=
begin
  simp_rw ["<-", expr nat.sum_antidiagonal_eq_sum_range_succ (λ k l, «expr * »(f k, g l))] [],
  exact [expr summable_sum_mul_antidiagonal_of_summable_mul h]
end

-- error in Topology.Algebra.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The Cauchy product formula for the product of two infinites sums indexed by `ℕ`,
    expressed by summing on `finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`
    if `f` and `g` are absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_range
(hf : summable f)
(hg : summable g)
(hfg : summable (λ
  x : «expr × »(exprℕ(), exprℕ()), «expr * »(f x.1, g x.2))) : «expr = »(«expr * »(«expr∑' , »((n), f n), «expr∑' , »((n), g n)), «expr∑' , »((n), «expr∑ in , »((k), range «expr + »(n, 1), «expr * »(f k, g «expr - »(n, k))))) :=
begin
  simp_rw ["<-", expr nat.sum_antidiagonal_eq_sum_range_succ (λ k l, «expr * »(f k, g l))] [],
  exact [expr tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg]
end

end CauchyProduct

