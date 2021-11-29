import Mathbin.Order.FixedPoints 
import Mathbin.Order.Zorn

/-!
# Schröder-Bernstein theorem, well-ordering of cardinals

This file proves the Schröder-Bernstein theorem (see `schroeder_bernstein`), the well-ordering of
cardinals (see `min_injective`) and the totality of their order (see `total`).

## Notes

Cardinals are naturally ordered by `α ≤ β ↔ ∃ f : a → β, injective f`:
* `schroeder_bernstein` states that, given injections `α → β` and `β → α`, one can get a
  bijection `α → β`. This corresponds to the antisymmetry of the order.
* The order is also well-founded: any nonempty set of cardinals has a minimal element.
  `min_injective` states that by saying that there exists an element of the set that injects into
  all others.

Cardinals are defined and further developed in the file `set_theory.cardinal`.
-/


open Set Function

open_locale Classical

universe u v

namespace Function

namespace Embedding

section antisymm

variable{α : Type u}{β : Type v}

-- error in SetTheory.SchroederBernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α`, we can get a bijection `α → β`. -/
theorem schroeder_bernstein
{f : α → β}
{g : β → α}
(hf : function.injective f)
(hg : function.injective g) : «expr∃ , »((h : α → β), bijective h) :=
begin
  casesI [expr is_empty_or_nonempty β] ["with", ident hβ, ident hβ],
  { haveI [] [":", expr is_empty α] [],
    from [expr function.is_empty f],
    exact [expr ⟨_, ((equiv.equiv_empty α).trans (equiv.equiv_empty β).symm).bijective⟩] },
  set [] [ident F] [":", expr «expr →ₘ »(set α, set α)] [":="] [expr { to_fun := λ
     s, «expr ᶜ»(«expr '' »(g, «expr ᶜ»(«expr '' »(f, s)))),
     monotone' := λ
     s
     t
     hst, «expr $ »(compl_subset_compl.mpr, «expr $ »(image_subset _, «expr $ »(compl_subset_compl.mpr, image_subset _ hst))) }] [],
  set [] [ident s] [":", expr set α] [":="] [expr F.lfp] [],
  have [ident hs] [":", expr «expr = »(«expr ᶜ»(«expr '' »(g, «expr ᶜ»(«expr '' »(f, s)))), s)] [],
  from [expr F.map_lfp],
  have [ident hns] [":", expr «expr = »(«expr '' »(g, «expr ᶜ»(«expr '' »(f, s))), «expr ᶜ»(s))] [],
  from [expr compl_injective (by simp [] [] [] ["[", expr hs, "]"] [] [])],
  set [] [ident g'] [] [":="] [expr inv_fun g] [],
  have [ident g'g] [":", expr left_inverse g' g] [],
  from [expr left_inverse_inv_fun hg],
  have [ident hg'ns] [":", expr «expr = »(«expr '' »(g', «expr ᶜ»(s)), «expr ᶜ»(«expr '' »(f, s)))] [],
  by rw ["[", "<-", expr hns, ",", expr g'g.image_image, "]"] [],
  set [] [ident h] [":", expr α → β] [":="] [expr s.piecewise f g'] [],
  have [] [":", expr surjective h] [],
  by rw ["[", "<-", expr range_iff_surjective, ",", expr range_piecewise, ",", expr hg'ns, ",", expr union_compl_self, "]"] [],
  have [] [":", expr injective h] [],
  { refine [expr (injective_piecewise_iff _).2 ⟨hf.inj_on _, _, _⟩],
    { intros [ident x, ident hx, ident y, ident hy, ident hxy],
      obtain ["⟨", ident x', ",", ident hx', ",", ident rfl, "⟩", ":", expr «expr ∈ »(x, «expr '' »(g, «expr ᶜ»(«expr '' »(f, s))))],
      by rwa [expr hns] [],
      obtain ["⟨", ident y', ",", ident hy', ",", ident rfl, "⟩", ":", expr «expr ∈ »(y, «expr '' »(g, «expr ᶜ»(«expr '' »(f, s))))],
      by rwa [expr hns] [],
      rw ["[", expr g'g _, ",", expr g'g _, "]"] ["at", ident hxy],
      rw [expr hxy] [] },
    { intros [ident x, ident hx, ident y, ident hy, ident hxy],
      obtain ["⟨", ident y', ",", ident hy', ",", ident rfl, "⟩", ":", expr «expr ∈ »(y, «expr '' »(g, «expr ᶜ»(«expr '' »(f, s))))],
      by rwa [expr hns] [],
      rw ["[", expr g'g _, "]"] ["at", ident hxy],
      exact [expr hy' ⟨x, hx, hxy⟩] } },
  exact [expr ⟨h, «expr‹ ›»(injective h), «expr‹ ›»(surjective h)⟩]
end

/-- **The Schröder-Bernstein Theorem**: Given embeddings `α ↪ β` and `β ↪ α`, there exists an
equivalence `α ≃ β`. -/
theorem antisymm : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β)
| ⟨e₁, h₁⟩, ⟨e₂, h₂⟩ =>
  let ⟨f, hf⟩ := schroeder_bernstein h₁ h₂
  ⟨Equiv.ofBijective f hf⟩

end antisymm

section Wo

parameter {ι : Type u}{β : ι → Type v}

@[reducible]
private def sets :=
  { s:Set (∀ i, β i) | ∀ x (_ : x ∈ s) y (_ : y ∈ s) i, (x : ∀ i, β i) i = y i → x = y }

/-- The cardinals are well-ordered. We express it here by the fact that in any set of cardinals
there is an element that injects into the others. See `cardinal.linear_order` for (one of) the
lattice instance. -/
theorem min_injective (I : Nonempty ι) : ∃ i, Nonempty (∀ j, β i ↪ β j) :=
  let ⟨s, hs, ms⟩ :=
    show ∃ (s : _)(_ : s ∈ sets), ∀ a (_ : a ∈ sets), s ⊆ a → a = s from
      Zorn.zorn_subset sets
        fun c hc hcc =>
          ⟨⋃₀c,
            fun x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ i hi =>
              (hcc.total hpc hqc).elim (fun h => hc hqc x (h hxp) y hyq i hi) fun h => hc hpc x hxp y (h hyq) i hi,
            fun _ => subset_sUnion_of_mem⟩
  let ⟨i, e⟩ :=
    show ∃ i, ∀ y, ∃ (x : _)(_ : x ∈ s), (x : ∀ i, β i) i = y from
      Classical.by_contradiction$
        fun h =>
          have h : ∀ i, ∃ y, ∀ x (_ : x ∈ s), (x : ∀ i, β i) i ≠ y :=
            by 
              simpa only [not_exists, not_forall] using h 
          let ⟨f, hf⟩ := Classical.axiom_of_choice h 
          have  : f ∈ s :=
            have  : insert f s ∈ sets :=
              fun x hx y hy =>
                by 
                  cases hx <;> cases hy
                  ·
                    simp [hx, hy]
                  ·
                    subst x 
                    exact fun i e => (hf i y hy e.symm).elim
                  ·
                    subst y 
                    exact fun i e => (hf i x hx e).elim
                  ·
                    exact hs x hx y hy 
            ms _ this (subset_insert f s) ▸ mem_insert _ _ 
          let ⟨i⟩ := I 
          hf i f this rfl 
  let ⟨f, hf⟩ := Classical.axiom_of_choice e
  ⟨i,
    ⟨fun j =>
        ⟨fun a => f a j,
          fun a b e' =>
            let ⟨sa, ea⟩ := hf a 
            let ⟨sb, eb⟩ := hf b 
            by 
              rw [←ea, ←eb, hs _ sa _ sb _ e']⟩⟩⟩

end Wo

/-- The cardinals are totally ordered. See `cardinal.linear_order` for (one of) the lattice
instance. -/
theorem Total {α : Type u} {β : Type v} : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α) :=
  match @min_injective Bool (fun b => cond b (Ulift α) (Ulift.{max u v, v} β)) ⟨tt⟩ with 
  | ⟨tt, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h ff 
    Or.inl ⟨embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
  | ⟨ff, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h tt 
    Or.inr ⟨embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩

end Embedding

end Function

