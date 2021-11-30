import Mathbin.Algebra.Group.Pi 
import Mathbin.Algebra.Ring.Opposite 
import Mathbin.Data.Equiv.MulAdd 
import Mathbin.Data.Finset.Fold 
import Mathbin.Data.Fintype.Basic 
import Mathbin.Data.Set.Pairwise

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `finset`).

## Notation

We introduce the following notation, localized in `big_operators`.
To enable the notation, use `open_locale big_operators`.

Let `s` be a `finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `finset.prod s f` (assuming `β` is a `comm_monoid`)
* `∑ x in s, f x` is notation for `finset.sum s f` (assuming `β` is an `add_comm_monoid`)
* `∏ x, f x` is notation for `finset.prod finset.univ f`
  (assuming `α` is a `fintype` and `β` is a `comm_monoid`)
* `∑ x, f x` is notation for `finset.sum finset.univ f`
  (assuming `α` is a `fintype` and `β` is an `add_comm_monoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/


universe u v w

variable {β : Type u} {α : Type v} {γ : Type w}

namespace Finset

/--
`∏ x in s, f x` is the product of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
@[toAdditive "`∑ x in s, f x` is the sum of `f x` as `x` ranges over the elements\nof the finite set `s`."]
protected def Prod [CommMonoidₓ β] (s : Finset α) (f : α → β) : β :=
  (s.1.map f).Prod

@[simp, toAdditive]
theorem prod_mk [CommMonoidₓ β] (s : Multiset α) (hs : s.nodup) (f : α → β) :
  (⟨s, hs⟩ : Finset α).Prod f = (s.map f).Prod :=
  rfl

end Finset

/--
There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k in K, (a k + b k) = ∑ k in K, a k + ∑ k in K, b k →
  ∏ k in K, a k * b k = (∏ k in K, a k) * (∏ k in K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/
library_note "operator precedence of big operators"

localized [BigOperators] notation3  "∑" (...) ", " r:(scoped f => Finset.sum Finset.univ f) => r

localized [BigOperators] notation3  "∏" (...) ", " r:(scoped f => Finset.prod Finset.univ f) => r

localized [BigOperators] notation3  "∑" (...) " in " s ", " r:(scoped f => Finset.sum s f) => r

localized [BigOperators] notation3  "∏" (...) " in " s ", " r:(scoped f => Finset.prod s f) => r

open_locale BigOperators

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

@[toAdditive]
theorem prod_eq_multiset_prod [CommMonoidₓ β] (s : Finset α) (f : α → β) : (∏x in s, f x) = (s.1.map f).Prod :=
  rfl

@[toAdditive]
theorem prod_eq_fold [CommMonoidₓ β] (s : Finset α) (f : α → β) : (∏x in s, f x) = s.fold (·*·) 1 f :=
  rfl

@[simp]
theorem sum_multiset_singleton (s : Finset α) : (s.sum fun x => {x}) = s.val :=
  by 
    simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

end Finset

@[toAdditive]
theorem MonoidHom.map_prod [CommMonoidₓ β] [CommMonoidₓ γ] (g : β →* γ) (f : α → β) (s : Finset α) :
  g (∏x in s, f x) = ∏x in s, g (f x) :=
  by 
    simp only [Finset.prod_eq_multiset_prod, g.map_multiset_prod, Multiset.map_map]

@[toAdditive]
theorem MulEquiv.map_prod [CommMonoidₓ β] [CommMonoidₓ γ] (g : β ≃* γ) (f : α → β) (s : Finset α) :
  g (∏x in s, f x) = ∏x in s, g (f x) :=
  g.to_monoid_hom.map_prod f s

theorem RingHom.map_list_prod [Semiringₓ β] [Semiringₓ γ] (f : β →+* γ) (l : List β) : f l.prod = (l.map f).Prod :=
  f.to_monoid_hom.map_list_prod l

theorem RingHom.map_list_sum [NonAssocSemiring β] [NonAssocSemiring γ] (f : β →+* γ) (l : List β) :
  f l.sum = (l.map f).Sum :=
  f.to_add_monoid_hom.map_list_sum l

/-- A morphism into the opposite ring acts on the product by acting on the reversed elements -/
theorem RingHom.unop_map_list_prod [Semiringₓ β] [Semiringₓ γ] (f : β →+* «expr ᵐᵒᵖ» γ) (l : List β) :
  MulOpposite.unop (f l.prod) = (l.map (MulOpposite.unop ∘ f)).reverse.Prod :=
  f.to_monoid_hom.unop_map_list_prod l

theorem RingHom.map_multiset_prod [CommSemiringₓ β] [CommSemiringₓ γ] (f : β →+* γ) (s : Multiset β) :
  f s.prod = (s.map f).Prod :=
  f.to_monoid_hom.map_multiset_prod s

theorem RingHom.map_multiset_sum [NonAssocSemiring β] [NonAssocSemiring γ] (f : β →+* γ) (s : Multiset β) :
  f s.sum = (s.map f).Sum :=
  f.to_add_monoid_hom.map_multiset_sum s

theorem RingHom.map_prod [CommSemiringₓ β] [CommSemiringₓ γ] (g : β →+* γ) (f : α → β) (s : Finset α) :
  g (∏x in s, f x) = ∏x in s, g (f x) :=
  g.to_monoid_hom.map_prod f s

theorem RingHom.map_sum [NonAssocSemiring β] [NonAssocSemiring γ] (g : β →+* γ) (f : α → β) (s : Finset α) :
  g (∑x in s, f x) = ∑x in s, g (f x) :=
  g.to_add_monoid_hom.map_sum f s

@[toAdditive]
theorem MonoidHom.coe_prod [MulOneClass β] [CommMonoidₓ γ] (f : α → β →* γ) (s : Finset α) :
  «expr⇑ » (∏x in s, f x) = ∏x in s, f x :=
  (MonoidHom.coeFn β γ).map_prod _ _

@[simp, toAdditive]
theorem MonoidHom.finset_prod_apply [MulOneClass β] [CommMonoidₓ γ] (f : α → β →* γ) (s : Finset α) (b : β) :
  (∏x in s, f x) b = ∏x in s, f x b :=
  (MonoidHom.eval b).map_prod _ _

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoidₓ

variable [CommMonoidₓ β]

@[simp, toAdditive]
theorem prod_empty {f : α → β} : (∏x in (∅ : Finset α), f x) = 1 :=
  rfl

@[simp, toAdditive]
theorem prod_cons (h : a ∉ s) : (∏x in cons a s h, f x) = f a*∏x in s, f x :=
  fold_cons h

@[simp, toAdditive]
theorem prod_insert [DecidableEq α] : a ∉ s → (∏x in insert a s, f x) = f a*∏x in s, f x :=
  fold_insert

/--
The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`.
-/
@[simp,
  toAdditive
      "The sum of `f` over `insert a s` is the same as\nthe sum over `s`, as long as `a` is in `s` or `f a = 0`."]
theorem prod_insert_of_eq_one_if_not_mem [DecidableEq α] (h : a ∉ s → f a = 1) :
  (∏x in insert a s, f x) = ∏x in s, f x :=
  by 
    byCases' hm : a ∈ s
    ·
      simpRw [insert_eq_of_mem hm]
    ·
      rw [prod_insert hm, h hm, one_mulₓ]

/--
The product of `f` over `insert a s` is the same as the product over `s`, as long as `f a = 1`.
-/
@[simp, toAdditive "The sum of `f` over `insert a s` is the same as\nthe sum over `s`, as long as `f a = 0`."]
theorem prod_insert_one [DecidableEq α] (h : f a = 1) : (∏x in insert a s, f x) = ∏x in s, f x :=
  prod_insert_of_eq_one_if_not_mem fun _ => h

@[simp, toAdditive]
theorem prod_singleton : (∏x in singleton a, f x) = f a :=
  Eq.trans fold_singleton$ mul_oneₓ _

@[toAdditive]
theorem prod_pair [DecidableEq α] {a b : α} (h : a ≠ b) : (∏x in ({a, b} : Finset α), f x) = f a*f b :=
  by 
    rw [prod_insert (not_mem_singleton.2 h), prod_singleton]

@[simp, toAdditive]
theorem prod_const_one : (∏x in s, (1 : β)) = 1 :=
  by 
    simp only [Finset.prod, Multiset.map_const, Multiset.prod_repeat, one_pow]

@[simp, toAdditive]
theorem prod_image [DecidableEq α] {s : Finset γ} {g : γ → α} :
  (∀ x _ : x ∈ s, ∀ y _ : y ∈ s, g x = g y → x = y) → (∏x in s.image g, f x) = ∏x in s, f (g x) :=
  fold_image

@[simp, toAdditive]
theorem prod_mapₓ (s : Finset α) (e : α ↪ γ) (f : γ → β) : (∏x in s.map e, f x) = ∏x in s, f (e x) :=
  by 
    rw [Finset.prod, Finset.map_val, Multiset.map_map] <;> rfl

@[congr, toAdditive]
theorem prod_congr (h : s₁ = s₂) : (∀ x _ : x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g :=
  by 
    rw [h] <;> exact fold_congr

attribute [congr] Finset.sum_congr

@[toAdditive]
theorem prod_union_inter [DecidableEq α] : ((∏x in s₁ ∪ s₂, f x)*∏x in s₁ ∩ s₂, f x) = (∏x in s₁, f x)*∏x in s₂, f x :=
  fold_union_inter

@[toAdditive]
theorem prod_union [DecidableEq α] (h : Disjoint s₁ s₂) : (∏x in s₁ ∪ s₂, f x) = (∏x in s₁, f x)*∏x in s₂, f x :=
  by 
    rw [←prod_union_inter, disjoint_iff_inter_eq_empty.mp h] <;> exact (mul_oneₓ _).symm

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_filter_mul_prod_filter_not
(s : finset α)
(p : α → exprProp())
[decidable_pred p]
[decidable_pred (λ x, «expr¬ »(p x))]
(f : α → β) : «expr = »(«expr * »(«expr∏ in , »((x), s.filter p, f x), «expr∏ in , »((x), s.filter (λ
    x, «expr¬ »(p x)), f x)), «expr∏ in , »((x), s, f x)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α],
  rw ["[", "<-", expr prod_union (filter_inter_filter_neg_eq p s).le, ",", expr filter_union_filter_neg_eq, "]"] []
end

end CommMonoidₓ

end Finset

section 

open Finset

variable [Fintype α] [DecidableEq α] [CommMonoidₓ β]

@[toAdditive]
theorem IsCompl.prod_mul_prod {s t : Finset α} (h : IsCompl s t) (f : α → β) :
  ((∏i in s, f i)*∏i in t, f i) = ∏i, f i :=
  (Finset.prod_union h.disjoint).symm.trans$
    by 
      rw [←Finset.sup_eq_union, h.sup_eq_top] <;> rfl

end 

namespace Finset

section CommMonoidₓ

variable [CommMonoidₓ β]

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `fintype.prod_subtype_mul_prod_subtype`. -/
@[toAdditive
      "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.\nFor a version expressed with subtypes, see `fintype.sum_subtype_add_sum_subtype`. "]
theorem prod_mul_prod_compl [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
  ((∏i in s, f i)*∏i in «expr ᶜ» s, f i) = ∏i, f i :=
  IsCompl.prod_mul_prod is_compl_compl f

@[toAdditive]
theorem prod_compl_mul_prod [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
  ((∏i in «expr ᶜ» s, f i)*∏i in s, f i) = ∏i, f i :=
  (@is_compl_compl _ s _).symm.prod_mul_prod f

@[toAdditive]
theorem prod_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) : ((∏x in s₂ \ s₁, f x)*∏x in s₁, f x) = ∏x in s₂, f x :=
  by 
    rw [←prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[simp, toAdditive]
theorem prod_sum_elim [DecidableEq (Sum α γ)] (s : Finset α) (t : Finset γ) (f : α → β) (g : γ → β) :
  (∏x in s.map Function.Embedding.inl ∪ t.map Function.Embedding.inr, Sum.elim f g x) = (∏x in s, f x)*∏x in t, g x :=
  by 
    rw [prod_union, prod_mapₓ, prod_mapₓ]
    ·
      simp only [Sum.elim_inl, Function.Embedding.inl_apply, Function.Embedding.inr_apply, Sum.elim_inr]
    ·
      simp only [disjoint_left, Finset.mem_map, Finset.mem_map]
      rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, H⟩
      cases H

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_bUnion
[decidable_eq α]
{s : finset γ}
{t : γ → finset α}
(hs : set.pairwise_disjoint «expr↑ »(s) t) : «expr = »(«expr∏ in , »((x), s.bUnion t, f x), «expr∏ in , »((x), s, «expr∏ in , »((i), t x, f i))) :=
begin
  haveI [] [] [":=", expr classical.dec_eq γ],
  induction [expr s] ["using", ident finset.induction_on] ["with", ident x, ident s, ident hxs, ident ih, ident hd] [],
  { simp_rw ["[", expr bUnion_empty, ",", expr prod_empty, "]"] [] },
  { simp_rw ["[", expr coe_insert, ",", expr set.pairwise_disjoint_insert, ",", expr mem_coe, "]"] ["at", ident hs],
    have [] [":", expr disjoint (t x) (finset.bUnion s t)] [],
    { exact [expr (disjoint_bUnion_right _ _ _).mpr (λ y hy, «expr $ »(hs.2 y hy, λ H, «expr $ »(hxs, H.substr hy)))] },
    rw ["[", expr bUnion_insert, ",", expr prod_insert hxs, ",", expr prod_union this, ",", expr ih hs.1, "]"] [] }
end

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_product
{s : finset γ}
{t : finset α}
{f : «expr × »(γ, α) → β} : «expr = »(«expr∏ in , »((x), s.product t, f x), «expr∏ in , »((x), s, «expr∏ in , »((y), t, f (x, y)))) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α],
  haveI [] [] [":=", expr classical.dec_eq γ],
  rw ["[", expr product_eq_bUnion, ",", expr prod_bUnion, "]"] [],
  { congr,
    funext [],
    exact [expr prod_image (λ _ _ _ _ H, (prod.mk.inj H).2)] },
  simp [] [] ["only"] ["[", expr disjoint_iff_ne, ",", expr mem_image, "]"] [] [],
  rintro [ident x, "_", ident y, "_", ident h, "⟨", ident i, ",", ident z, "⟩", ident hz],
  rw ["[", expr inf_eq_inter, ",", expr mem_inter, ",", expr mem_image, ",", expr mem_image, "]"] ["at", ident hz],
  obtain ["⟨", "⟨", "_", ",", "_", ",", ident rfl, ",", "_", "⟩", ",", "_", ",", "_", ",", ident rfl, ",", "_", "⟩", ":=", expr hz],
  exact [expr h rfl]
end

/-- An uncurried version of `finset.prod_product`. -/
@[toAdditive "An uncurried version of `finset.sum_product`"]
theorem prod_product' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
  (∏x in s.product t, f x.1 x.2) = ∏x in s, ∏y in t, f x y :=
  prod_product

/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `finset.prod_sigma'`.  -/
@[toAdditive
      "Sum over a sigma type equals the sum of fiberwise sums. For rewriting\nin the reverse direction, use `finset.sum_sigma'`"]
theorem prod_sigma {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
  (∏x in s.sigma t, f x) = ∏a in s, ∏s in t a, f ⟨a, s⟩ :=
  by 
    classical <;>
      calc (∏x in s.sigma t, f x) = ∏x in s.bUnion fun a => (t a).map (Function.Embedding.sigmaMk a), f x :=
        by 
          rw [sigma_eq_bUnion]_ = ∏a in s, ∏x in (t a).map (Function.Embedding.sigmaMk a), f x :=
        prod_bUnion$
          fun a₁ ha a₂ ha₂ h x hx =>
            by 
              simp only [inf_eq_inter, mem_inter, mem_map, Function.Embedding.sigma_mk_apply] at hx 
              rcases hx with ⟨⟨y, hy, rfl⟩, ⟨z, hz, hz'⟩⟩
              cc _ = ∏a in s, ∏s in t a, f ⟨a, s⟩ :=
        prod_congr rfl$ fun _ _ => prod_mapₓ _ _ _

@[toAdditive]
theorem prod_sigma' {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
  (∏a in s, ∏s in t a, f a s) = ∏x in s.sigma t, f x.1 x.2 :=
  Eq.symm$ prod_sigma s t fun x => f x.1 x.2

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_fiberwise_of_maps_to
[decidable_eq γ]
{s : finset α}
{t : finset γ}
{g : α → γ}
(h : ∀ x «expr ∈ » s, «expr ∈ »(g x, t))
(f : α → β) : «expr = »(«expr∏ in , »((y), t, «expr∏ in , »((x), s.filter (λ
    x, «expr = »(g x, y)), f x)), «expr∏ in , »((x), s, f x)) :=
begin
  letI [] [] [":=", expr classical.dec_eq α],
  rw ["[", "<-", expr bUnion_filter_eq_of_maps_to h, "]"] [] { occs := occurrences.pos «expr[ , ]»([2]) },
  refine [expr «expr $ »(prod_bUnion, λ x' hx y' hy hne, _).symm],
  rw ["[", expr function.on_fun, ",", expr disjoint_filter, "]"] [],
  rintros [ident x, ident hx, ident rfl],
  exact [expr hne]
end

@[toAdditive]
theorem prod_image' [DecidableEq α] {s : Finset γ} {g : γ → α} (h : γ → β)
  (eq : ∀ c _ : c ∈ s, f (g c) = ∏x in s.filter fun c' => g c' = g c, h x) : (∏x in s.image g, f x) = ∏x in s, h x :=
  calc (∏x in s.image g, f x) = ∏x in s.image g, ∏x in s.filter fun c' => g c' = x, h x :=
    prod_congr rfl$
      fun x hx =>
        let ⟨c, hcs, hc⟩ := mem_image.1 hx 
        hc ▸ Eq c hcs 
    _ = ∏x in s, h x := prod_fiberwise_of_maps_to (fun x => mem_image_of_mem g) _
    

@[toAdditive]
theorem prod_mul_distrib : (∏x in s, f x*g x) = (∏x in s, f x)*∏x in s, g x :=
  Eq.trans
    (by 
      rw [one_mulₓ] <;> rfl)
    fold_op_distrib

@[toAdditive]
theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} : (∏x in s, ∏y in t, f x y) = ∏y in t, ∏x in s, f x y :=
  by 
    classical 
    apply Finset.induction_on s
    ·
      simp only [prod_empty, prod_const_one]
    ·
      intro _ _ H ih 
      simp only [prod_insert H, prod_mul_distrib, ih]

@[toAdditive]
theorem prod_product_right {s : Finset γ} {t : Finset α} {f : γ × α → β} :
  (∏x in s.product t, f x) = ∏y in t, ∏x in s, f (x, y) :=
  by 
    rw [prod_product, prod_comm]

/-- An uncurried version of `finset.prod_product_right`. -/
@[toAdditive "An uncurried version of `finset.prod_product_right`"]
theorem prod_product_right' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
  (∏x in s.product t, f x.1 x.2) = ∏y in t, ∏x in s, f x y :=
  prod_product_right

@[toAdditive]
theorem prod_hom_rel [CommMonoidₓ γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : Finset α} (h₁ : r 1 1)
  (h₂ : ∀ a b c, r b c → r (f a*b) (g a*c)) : r (∏x in s, f x) (∏x in s, g x) :=
  by 
    delta' Finset.prod 
    apply Multiset.prod_hom_rel <;> assumption

@[toAdditive]
theorem prod_eq_one {f : α → β} {s : Finset α} (h : ∀ x _ : x ∈ s, f x = 1) : (∏x in s, f x) = 1 :=
  calc (∏x in s, f x) = ∏x in s, 1 := Finset.prod_congr rfl h 
    _ = 1 := Finset.prod_const_one
    

@[toAdditive]
theorem prod_subset_one_on_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) (hg : ∀ x _ : x ∈ s₂ \ s₁, g x = 1)
  (hfg : ∀ x _ : x ∈ s₁, f x = g x) : (∏i in s₁, f i) = ∏i in s₂, g i :=
  by 
    rw [←prod_sdiff h, prod_eq_one hg, one_mulₓ]
    exact prod_congr rfl hfg

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_subset
(h : «expr ⊆ »(s₁, s₂))
(hf : ∀
 x «expr ∈ » s₂, «expr ∉ »(x, s₁) → «expr = »(f x, 1)) : «expr = »(«expr∏ in , »((x), s₁, f x), «expr∏ in , »((x), s₂, f x)) :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr prod_subset_one_on_sdiff h (by simpa [] [] [] [] [] []) (λ
  _ _, rfl)]

@[toAdditive]
theorem prod_filter_of_ne {p : α → Prop} [DecidablePred p] (hp : ∀ x _ : x ∈ s, f x ≠ 1 → p x) :
  (∏x in s.filter p, f x) = ∏x in s, f x :=
  prod_subset (filter_subset _ _)$
    fun x =>
      by 
        classical 
        rw [not_imp_comm, mem_filter]
        exact fun h₁ h₂ => ⟨h₁, hp _ h₁ h₂⟩

@[toAdditive]
theorem prod_filter_ne_one [∀ x, Decidable (f x ≠ 1)] : (∏x in s.filter$ fun x => f x ≠ 1, f x) = ∏x in s, f x :=
  prod_filter_of_ne$ fun _ _ => id

@[toAdditive]
theorem prod_filter (p : α → Prop) [DecidablePred p] (f : α → β) :
  (∏a in s.filter p, f a) = ∏a in s, if p a then f a else 1 :=
  calc (∏a in s.filter p, f a) = ∏a in s.filter p, if p a then f a else 1 :=
    prod_congr rfl
      fun a h =>
        by 
          rw [if_pos (mem_filter.1 h).2]
    _ = ∏a in s, if p a then f a else 1 :=
    by 
      refine' prod_subset (filter_subset _ s) fun x hs h => _ 
      rw [mem_filter, not_and] at h 
      exact if_neg (h hs)
    

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_eq_single_of_mem
{s : finset α}
{f : α → β}
(a : α)
(h : «expr ∈ »(a, s))
(h₀ : ∀ b «expr ∈ » s, «expr ≠ »(b, a) → «expr = »(f b, 1)) : «expr = »(«expr∏ in , »((x), s, f x), f a) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α],
  calc
    «expr = »(«expr∏ in , »((x), s, f x), «expr∏ in , »((x), {a}, f x)) : begin
      refine [expr (prod_subset _ _).symm],
      { intros ["_", ident H],
        rwa [expr mem_singleton.1 H] [] },
      { simpa [] [] ["only"] ["[", expr mem_singleton, "]"] [] [] }
    end
    «expr = »(..., f a) : prod_singleton
end

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_eq_single
{s : finset α}
{f : α → β}
(a : α)
(h₀ : ∀ b «expr ∈ » s, «expr ≠ »(b, a) → «expr = »(f b, 1))
(h₁ : «expr ∉ »(a, s) → «expr = »(f a, 1)) : «expr = »(«expr∏ in , »((x), s, f x), f a) :=
by haveI [] [] [":=", expr classical.dec_eq α]; from [expr classical.by_cases (assume: «expr ∈ »(a, s), prod_eq_single_of_mem a this h₀) (assume: «expr ∉ »(a, s), «expr $ »(«expr $ »(prod_congr rfl, λ
    b hb, «expr $ »(h₀ b hb, by rintro [ident rfl]; cc)).trans, prod_const_one.trans (h₁ this).symm))]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_eq_mul_of_mem
{s : finset α}
{f : α → β}
(a b : α)
(ha : «expr ∈ »(a, s))
(hb : «expr ∈ »(b, s))
(hn : «expr ≠ »(a, b))
(h₀ : ∀
 c «expr ∈ » s, «expr ∧ »(«expr ≠ »(c, a), «expr ≠ »(c, b)) → «expr = »(f c, 1)) : «expr = »(«expr∏ in , »((x), s, f x), «expr * »(f a, f b)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α]; let [ident s'] [] [":=", expr ({a, b} : finset α)],
  have [ident hu] [":", expr «expr ⊆ »(s', s)] [],
  { refine [expr insert_subset.mpr _],
    apply [expr and.intro ha],
    apply [expr singleton_subset_iff.mpr hb] },
  have [ident hf] [":", expr ∀ c «expr ∈ » s, «expr ∉ »(c, s') → «expr = »(f c, 1)] [],
  { intros [ident c, ident hc, ident hcs],
    apply [expr h₀ c hc],
    apply [expr not_or_distrib.mp],
    intro [ident hab],
    apply [expr hcs],
    apply [expr mem_insert.mpr],
    rw [expr mem_singleton] [],
    exact [expr hab] },
  rw ["<-", expr prod_subset hu hf] [],
  exact [expr finset.prod_pair hn]
end

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_eq_mul
{s : finset α}
{f : α → β}
(a b : α)
(hn : «expr ≠ »(a, b))
(h₀ : ∀ c «expr ∈ » s, «expr ∧ »(«expr ≠ »(c, a), «expr ≠ »(c, b)) → «expr = »(f c, 1))
(ha : «expr ∉ »(a, s) → «expr = »(f a, 1))
(hb : «expr ∉ »(b, s) → «expr = »(f b, 1)) : «expr = »(«expr∏ in , »((x), s, f x), «expr * »(f a, f b)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α]; by_cases [expr h₁, ":", expr «expr ∈ »(a, s)]; by_cases [expr h₂, ":", expr «expr ∈ »(b, s)],
  { exact [expr prod_eq_mul_of_mem a b h₁ h₂ hn h₀] },
  { rw ["[", expr hb h₂, ",", expr mul_one, "]"] [],
    apply [expr prod_eq_single_of_mem a h₁],
    exact [expr λ c hc hca, h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩] },
  { rw ["[", expr ha h₁, ",", expr one_mul, "]"] [],
    apply [expr prod_eq_single_of_mem b h₂],
    exact [expr λ c hc hcb, h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩] },
  { rw ["[", expr ha h₁, ",", expr hb h₂, ",", expr mul_one, "]"] [],
    exact [expr trans (prod_congr rfl (λ
       c hc, h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)) prod_const_one] }
end

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_attach {f : α → β} : «expr = »(«expr∏ in , »((x), s.attach, f x), «expr∏ in , »((x), s, f x)) :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr calc
   «expr = »(«expr∏ in , »((x), s.attach, f x.val), «expr∏ in , »((x), s.attach.image subtype.val, f x)) : by rw ["[", expr prod_image, "]"] []; exact [expr assume
    x _ y _, subtype.eq]
   «expr = »(..., _) : by rw ["[", expr attach_image_val, "]"] []]

/-- A product over `s.subtype p` equals one over `s.filter p`. -/
@[simp, toAdditive "A sum over `s.subtype p` equals one over `s.filter p`."]
theorem prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [DecidablePred p] :
  (∏x in s.subtype p, f x) = ∏x in s.filter p, f x :=
  by 
    convLHS => erw [←prod_mapₓ (s.subtype p) (Function.Embedding.subtype _) f]
    exact prod_congr (subtype_map _) fun x hx => rfl

/-- If all elements of a `finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[toAdditive
      "If all elements of a `finset` satisfy the predicate `p`, a sum\nover `s.subtype p` equals that sum over `s`."]
theorem prod_subtype_of_mem (f : α → β) {p : α → Prop} [DecidablePred p] (h : ∀ x _ : x ∈ s, p x) :
  (∏x in s.subtype p, f x) = ∏x in s, f x :=
  by 
    simpRw [prod_subtype_eq_prod_filter, filter_true_of_mem h]

/-- A product of a function over a `finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `finset`. -/
@[toAdditive
      "A sum of a function over a `finset` in a subtype equals a\nsum in the main type of a function that agrees with the first\nfunction on that `finset`."]
theorem prod_subtype_map_embedding {p : α → Prop} {s : Finset { x // p x }} {f : { x // p x } → β} {g : α → β}
  (h : ∀ x : { x // p x }, x ∈ s → g x = f x) : (∏x in s.map (Function.Embedding.subtype _), g x) = ∏x in s, f x :=
  by 
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl h

@[toAdditive]
theorem prod_finset_coe (f : α → β) (s : Finset α) : (∏i : (s : Set α), f i) = ∏i in s, f i :=
  prod_attach

@[toAdditive]
theorem prod_subtype {p : α → Prop} {F : Fintype (Subtype p)} (s : Finset α) (h : ∀ x, x ∈ s ↔ p x) (f : α → β) :
  (∏a in s, f a) = ∏a : Subtype p, f a :=
  have  : (· ∈ s) = p := Set.ext h 
  by 
    subst p 
    rw [←prod_finset_coe]
    congr

@[toAdditive]
theorem prod_apply_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} [DecidablePred fun x => ¬p x]
  (f : ∀ x : α, p x → γ) (g : ∀ x : α, ¬p x → γ) (h : γ → β) :
  (∏x in s, h (if hx : p x then f x hx else g x hx)) =
    (∏x in (s.filter p).attach,
        h (f x.1 (mem_filter.mp x.2).2))*∏x in (s.filter fun x => ¬p x).attach, h (g x.1 (mem_filter.mp x.2).2) :=
  calc
    (∏x in s, h (if hx : p x then f x hx else g x hx)) =
      (∏x in s.filter p,
          h
            (if hx : p x then f x hx else
              g x hx))*∏x in s.filter fun x => ¬p x, h (if hx : p x then f x hx else g x hx) :=
    (prod_filter_mul_prod_filter_not s p _).symm 
    _ =
      (∏x in (s.filter p).attach,
          h
            (if hx : p x.1 then f x.1 hx else
              g x.1 hx))*∏x in (s.filter fun x => ¬p x).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
    congr_arg2ₓ _ prod_attach.symm prod_attach.symm 
    _ =
      (∏x in (s.filter p).attach,
          h (f x.1 (mem_filter.mp x.2).2))*∏x in (s.filter fun x => ¬p x).attach, h (g x.1 (mem_filter.mp x.2).2) :=
    congr_arg2ₓ _ (prod_congr rfl fun x hx => congr_argₓ h (dif_pos (mem_filter.mp x.2).2))
      (prod_congr rfl fun x hx => congr_argₓ h (dif_neg (mem_filter.mp x.2).2))
    

@[toAdditive]
theorem prod_apply_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (h : γ → β) :
  (∏x in s, h (if p x then f x else g x)) = (∏x in s.filter p, h (f x))*∏x in s.filter fun x => ¬p x, h (g x) :=
  trans (prod_apply_dite _ _ _) (congr_arg2ₓ _ (@prod_attach _ _ _ _ (h ∘ f)) (@prod_attach _ _ _ _ (h ∘ g)))

@[toAdditive]
theorem prod_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f : ∀ x : α, p x → β) (g : ∀ x : α, ¬p x → β) :
  (∏x in s, if hx : p x then f x hx else g x hx) =
    (∏x in (s.filter p).attach,
        f x.1 (mem_filter.mp x.2).2)*∏x in (s.filter fun x => ¬p x).attach, g x.1 (mem_filter.mp x.2).2 :=
  by 
    simp [prod_apply_dite _ _ fun x => x]

@[toAdditive]
theorem prod_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → β) :
  (∏x in s, if p x then f x else g x) = (∏x in s.filter p, f x)*∏x in s.filter fun x => ¬p x, g x :=
  by 
    simp [prod_apply_ite _ _ fun x => x]

@[toAdditive]
theorem prod_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x _ : x ∈ s, ¬p x) :
  (∏x in s, if p x then f x else g x) = ∏x in s, g x :=
  by 
    rw [prod_ite]
    simp [filter_false_of_mem h, filter_true_of_mem h]

@[toAdditive]
theorem prod_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x _ : x ∈ s, p x) :
  (∏x in s, if p x then f x else g x) = ∏x in s, f x :=
  by 
    simpRw [←ite_not (p _)]
    apply prod_ite_of_false 
    simpa

@[toAdditive]
theorem prod_apply_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
  (h : ∀ x _ : x ∈ s, ¬p x) : (∏x in s, k (if p x then f x else g x)) = ∏x in s, k (g x) :=
  by 
    simpRw [apply_ite k]
    exact prod_ite_of_false _ _ h

@[toAdditive]
theorem prod_apply_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
  (h : ∀ x _ : x ∈ s, p x) : (∏x in s, k (if p x then f x else g x)) = ∏x in s, k (f x) :=
  by 
    simpRw [apply_ite k]
    exact prod_ite_of_true _ _ h

@[toAdditive]
theorem prod_extend_by_one [DecidableEq α] (s : Finset α) (f : α → β) :
  (∏i in s, if i ∈ s then f i else 1) = ∏i in s, f i :=
  prod_congr rfl$ fun i hi => if_pos hi

@[simp, toAdditive]
theorem prod_dite_eq [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, a = x → β) :
  (∏x in s, if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 :=
  by 
    splitIfs with h
    ·
      rw [Finset.prod_eq_single a, dif_pos rfl]
      ·
        intros 
        rw [dif_neg]
        cc
      ·
        cc
    ·
      rw [Finset.prod_eq_one]
      intros 
      rw [dif_neg]
      intro 
      cc

@[simp, toAdditive]
theorem prod_dite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, x = a → β) :
  (∏x in s, if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 :=
  by 
    splitIfs with h
    ·
      rw [Finset.prod_eq_single a, dif_pos rfl]
      ·
        intros 
        rw [dif_neg]
        cc
      ·
        cc
    ·
      rw [Finset.prod_eq_one]
      intros 
      rw [dif_neg]
      intro 
      cc

@[simp, toAdditive]
theorem prod_ite_eq [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
  (∏x in s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/--
  When a product is taken over a conditional whose condition is an equality test on the index
  and whose alternative is 1, then the product's value is either the term at that index or `1`.

  The difference with `prod_ite_eq` is that the arguments to `eq` are swapped.
-/
@[simp, toAdditive]
theorem prod_ite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
  (∏x in s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[toAdditive]
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset α) (f : α → β) :
  (∏x in if p then s else t, f x) = if p then ∏x in s, f x else ∏x in t, f x :=
  apply_ite (fun s => ∏x in s, f x) _ _ _

@[simp, toAdditive]
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset α) (f : p → α → β) (g : ¬p → α → β) :
  (∏x in s, if h : p then f h x else g h x) = if h : p then ∏x in s, f h x else ∏x in s, g h x :=
  by 
    splitIfs with h <;> rfl

@[simp]
theorem sum_pi_single' {ι M : Type _} [DecidableEq ι] [AddCommMonoidₓ M] (i : ι) (x : M) (s : Finset ι) :
  (∑j in s, Pi.single i x j) = if i ∈ s then x else 0 :=
  sum_dite_eq' _ _ _

@[simp]
theorem sum_pi_single {ι : Type _} {M : ι → Type _} [DecidableEq ι] [∀ i, AddCommMonoidₓ (M i)] (i : ι) (f : ∀ i, M i)
  (s : Finset ι) : (∑j in s, Pi.single j (f j) i) = if i ∈ s then f i else 0 :=
  sum_dite_eq _ _ _

/--
  Reorder a product.

  The difference with `prod_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
-/
@[toAdditive
      "\n  Reorder a sum.\n\n  The difference with `sum_bij'` is that the bijection is specified as a surjective injection,\n  rather than by an inverse function.\n"]
theorem prod_bij {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a _ : a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t)
  (h : ∀ a ha, f a = g (i a ha)) (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
  (i_surj : ∀ b _ : b ∈ t, ∃ a ha, b = i a ha) : (∏x in s, f x) = ∏x in t, g x :=
  congr_argₓ Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi h i_inj i_surj)

/--
  Reorder a product.

  The difference with `prod_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
-/
@[toAdditive
      "\n  Reorder a sum.\n\n  The difference with `sum_bij` is that the bijection is specified with an inverse, rather than\n  as a surjective injection.\n"]
theorem prod_bij' {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a _ : a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t)
  (h : ∀ a ha, f a = g (i a ha)) (j : ∀ a _ : a ∈ t, α) (hj : ∀ a ha, j a ha ∈ s)
  (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a) (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) :
  (∏x in s, f x) = ∏x in t, g x :=
  by 
    refine' prod_bij i hi h _ _
    ·
      intro a1 a2 h1 h2 eq 
      rw [←left_inv a1 h1, ←left_inv a2 h2]
      cc
    ·
      intro b hb 
      use j b hb 
      use hj b hb 
      exact (right_inv b hb).symm

@[toAdditive]
theorem prod_bij_ne_one {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a _ : a ∈ s, f a ≠ 1 → γ)
  (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t) (i_inj : ∀ a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
  (i_surj : ∀ b _ : b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, b = i a h₁ h₂) (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
  (∏x in s, f x) = ∏x in t, g x :=
  by 
    classical <;>
      exact
        calc (∏x in s, f x) = ∏x in s.filter$ fun x => f x ≠ 1, f x := prod_filter_ne_one.symm 
          _ = ∏x in t.filter$ fun x => g x ≠ 1, g x :=
          prod_bij (fun a ha => i a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
            (fun a ha =>
              (mem_filter.mp ha).elim$ fun h₁ h₂ => mem_filter.mpr ⟨hi a h₁ h₂, fun hg => h₂ (hg ▸ h a h₁ h₂)⟩)
            (fun a ha => (mem_filter.mp ha).elim$ h a)
            (fun a₁ a₂ ha₁ ha₂ =>
              (mem_filter.mp ha₁).elim$ fun ha₁₁ ha₁₂ => (mem_filter.mp ha₂).elim$ fun ha₂₁ ha₂₂ => i_inj a₁ a₂ _ _ _ _)
            fun b hb =>
              (mem_filter.mp hb).elim$
                fun h₁ h₂ =>
                  let ⟨a, ha₁, ha₂, Eq⟩ := i_surj b h₁ h₂
                  ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, Eq⟩
          _ = ∏x in t, g x := prod_filter_ne_one
          

@[toAdditive]
theorem prod_dite_of_false {p : α → Prop} {hp : DecidablePred p} (h : ∀ x _ : x ∈ s, ¬p x) (f : ∀ x : α, p x → β)
  (g : ∀ x : α, ¬p x → β) : (∏x in s, if hx : p x then f x hx else g x hx) = ∏x : s, g x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩)
    (fun x hx =>
      by 
        simp )
    (fun a ha =>
      by 
        dsimp 
        rw [dif_neg])
    (fun a₁ a₂ h₁ h₂ hh => congr_argₓ coeₓ hh)
    fun b hb =>
      ⟨b.1, b.2,
        by 
          simp ⟩

@[toAdditive]
theorem prod_dite_of_true {p : α → Prop} {hp : DecidablePred p} (h : ∀ x _ : x ∈ s, p x) (f : ∀ x : α, p x → β)
  (g : ∀ x : α, ¬p x → β) : (∏x in s, if hx : p x then f x hx else g x hx) = ∏x : s, f x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩)
    (fun x hx =>
      by 
        simp )
    (fun a ha =>
      by 
        dsimp 
        rw [dif_pos])
    (fun a₁ a₂ h₁ h₂ hh => congr_argₓ coeₓ hh)
    fun b hb =>
      ⟨b.1, b.2,
        by 
          simp ⟩

@[toAdditive]
theorem nonempty_of_prod_ne_one (h : (∏x in s, f x) ≠ 1) : s.nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim$ h$ H.symm ▸ prod_empty) id

@[toAdditive]
theorem exists_ne_one_of_prod_ne_one (h : (∏x in s, f x) ≠ 1) : ∃ (a : _)(_ : a ∈ s), f a ≠ 1 :=
  by 
    classical 
    rw [←prod_filter_ne_one] at h 
    rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩
    exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩

@[toAdditive]
theorem prod_range_succ_comm (f : ℕ → β) (n : ℕ) : (∏x in range (n+1), f x) = f n*∏x in range n, f x :=
  by 
    rw [range_succ, prod_insert not_mem_range_self]

@[toAdditive]
theorem prod_range_succ (f : ℕ → β) (n : ℕ) : (∏x in range (n+1), f x) = (∏x in range n, f x)*f n :=
  by 
    simp only [mul_commₓ, prod_range_succ_comm]

@[toAdditive]
theorem prod_range_succ' (f : ℕ → β) : ∀ n : ℕ, (∏k in range (n+1), f k) = (∏k in range n, f (k+1))*f 0
| 0 => prod_range_succ _ _
| n+1 =>
  by 
    rw [prod_range_succ _ n, mul_right_commₓ, ←prod_range_succ', prod_range_succ]

@[toAdditive]
theorem eventually_constant_prod {u : ℕ → β} {N : ℕ} (hu : ∀ n _ : n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
  (∏k in range (n+1), u k) = ∏k in range (N+1), u k :=
  by 
    obtain ⟨m, rfl : n = N+m⟩ := le_iff_exists_add.mp hn 
    clear hn 
    induction' m with m hm
    ·
      simp 
    erw [prod_range_succ, hm]
    simp [hu]

@[toAdditive]
theorem prod_range_add (f : ℕ → β) (n m : ℕ) : (∏x in range (n+m), f x) = (∏x in range n, f x)*∏x in range m, f (n+x) :=
  by 
    induction' m with m hm
    ·
      simp 
    ·
      rw [Nat.add_succ, prod_range_succ, hm, prod_range_succ, mul_assocₓ]

@[toAdditive]
theorem prod_range_add_div_prod_range {α : Type _} [CommGroupₓ α] (f : ℕ → α) (n m : ℕ) :
  ((∏k in range (n+m), f k) / ∏k in range n, f k) = ∏k in Finset.range m, f (n+k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[toAdditive]
theorem prod_range_zero (f : ℕ → β) : (∏k in range 0, f k) = 1 :=
  by 
    rw [range_zero, prod_empty]

@[toAdditive sum_range_one]
theorem prod_range_one (f : ℕ → β) : (∏k in range 1, f k) = f 0 :=
  by 
    rw [range_one]
    apply @prod_singleton β ℕ 0 f

open Multiset

@[toAdditive]
theorem prod_multiset_map_count [DecidableEq α] (s : Multiset α) {M : Type _} [CommMonoidₓ M] (f : α → M) :
  (s.map f).Prod = ∏m in s.to_finset, f m ^ s.count m :=
  by 
    induction' s using Multiset.induction_on with a s ih
    ·
      simp only [prod_const_one, count_zero, prod_zero, pow_zeroₓ, map_zero]
    simp only [Multiset.prod_cons, map_cons, to_finset_cons, ih]
    byCases' has : a ∈ s.to_finset
    ·
      rw [insert_eq_of_mem has, ←insert_erase has, prod_insert (not_mem_erase _ _), prod_insert (not_mem_erase _ _),
        ←mul_assocₓ, count_cons_self, pow_succₓ]
      congr 1
      refine' prod_congr rfl fun x hx => _ 
      rw [count_cons_of_ne (ne_of_mem_erase hx)]
    rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_to_finset.2 has), pow_oneₓ]
    congr 1
    refine' prod_congr rfl fun x hx => _ 
    rw [count_cons_of_ne]
    rintro rfl 
    exact has hx

@[toAdditive]
theorem prod_multiset_count [DecidableEq α] [CommMonoidₓ α] (s : Multiset α) :
  s.prod = ∏m in s.to_finset, m ^ s.count m :=
  by 
    convert prod_multiset_map_count s id 
    rw [map_id]

@[toAdditive]
theorem prod_mem_multiset [DecidableEq α] (m : Multiset α) (f : { x // x ∈ m } → β) (g : α → β) (hfg : ∀ x, f x = g x) :
  (∏x : { x // x ∈ m }, f x) = ∏x in m.to_finset, g x :=
  prod_bij (fun x _ => x.1) (fun x _ => Multiset.mem_to_finset.mpr x.2) (fun _ _ => hfg _)
    (fun _ _ _ _ h =>
      by 
        ext 
        assumption)
    fun y hy => ⟨⟨y, Multiset.mem_to_finset.mp hy⟩, Finset.mem_univ _, rfl⟩

/--
To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[toAdditive "To prove a property of a sum, it suffices to prove that\nthe property is additive and holds on summands."]
theorem prod_induction {M : Type _} [CommMonoidₓ M] (f : α → M) (p : M → Prop) (p_mul : ∀ a b, p a → p b → p (a*b))
  (p_one : p 1) (p_s : ∀ x _ : x ∈ s, p$ f x) : p$ ∏x in s, f x :=
  Multiset.prod_induction _ _ p_mul p_one (Multiset.forall_mem_map_iff.mpr p_s)

/--
To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[toAdditive "To prove a property of a sum, it suffices to prove that\nthe property is additive and holds on summands."]
theorem prod_induction_nonempty {M : Type _} [CommMonoidₓ M] (f : α → M) (p : M → Prop)
  (p_mul : ∀ a b, p a → p b → p (a*b)) (hs_nonempty : s.nonempty) (p_s : ∀ x _ : x ∈ s, p$ f x) : p$ ∏x in s, f x :=
  Multiset.prod_induction_nonempty p p_mul
    (by 
      simp [nonempty_iff_ne_empty.mp hs_nonempty])
    (Multiset.forall_mem_map_iff.mpr p_s)

/--
For any product along `{0, ..., n-1}` of a commutative-monoid-valued function, we can verify that
it's equal to a different function just by checking ratios of adjacent terms.
This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
theorem prod_range_induction {M : Type _} [CommMonoidₓ M] (f s : ℕ → M) (h0 : s 0 = 1) (h : ∀ n, s (n+1) = s n*f n)
  (n : ℕ) : (∏k in Finset.range n, f k) = s n :=
  by 
    induction' n with k hk
    ·
      simp only [h0, Finset.prod_range_zero]
    ·
      simp only [hk, Finset.prod_range_succ, h, mul_commₓ]

/--
For any sum along `{0, ..., n-1}` of a commutative-monoid-valued function,
we can verify that it's equal to a different function
just by checking differences of adjacent terms.
This is a discrete analogue
of the fundamental theorem of calculus.
-/
theorem sum_range_induction {M : Type _} [AddCommMonoidₓ M] (f s : ℕ → M) (h0 : s 0 = 0) (h : ∀ n, s (n+1) = s n+f n)
  (n : ℕ) : (∑k in Finset.range n, f k) = s n :=
  @prod_range_induction (Multiplicative M) _ f s h0 h n

/-- A telescoping sum along `{0, ..., n-1}` of an additive commutative group valued function
reduces to the difference of the last and first terms.-/
theorem sum_range_sub {G : Type _} [AddCommGroupₓ G] (f : ℕ → G) (n : ℕ) : (∑i in range n, f (i+1) - f i) = f n - f 0 :=
  by 
    apply sum_range_induction <;> simp 

theorem sum_range_sub' {G : Type _} [AddCommGroupₓ G] (f : ℕ → G) (n : ℕ) :
  (∑i in range n, f i - f (i+1)) = f 0 - f n :=
  by 
    apply sum_range_induction <;> simp 

/-- A telescoping product along `{0, ..., n-1}` of a commutative group valued function
reduces to the ratio of the last and first factors.-/
@[toAdditive]
theorem prod_range_div {M : Type _} [CommGroupₓ M] (f : ℕ → M) (n : ℕ) : (∏i in range n, f (i+1)*f i⁻¹) = f n*f 0⁻¹ :=
  by 
    simpa only [←div_eq_mul_inv] using @sum_range_sub (Additive M) _ f n

@[toAdditive]
theorem prod_range_div' {M : Type _} [CommGroupₓ M] (f : ℕ → M) (n : ℕ) : (∏i in range n, f i*f (i+1)⁻¹) = f 0*f n⁻¹ :=
  by 
    simpa only [←div_eq_mul_inv] using @sum_range_sub' (Additive M) _ f n

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
theorem sum_range_sub_of_monotone
{f : exprℕ() → exprℕ()}
(h : monotone f)
(n : exprℕ()) : «expr = »(«expr∑ in , »((i), range n, «expr - »(f «expr + »(i, 1), f i)), «expr - »(f n, f 0)) :=
begin
  refine [expr sum_range_induction _ _ (tsub_self _) (λ n, _) _],
  have [ident h₁] [":", expr «expr ≤ »(f n, f «expr + »(n, 1))] [":=", expr h (nat.le_succ _)],
  have [ident h₂] [":", expr «expr ≤ »(f 0, f n)] [":=", expr h (nat.zero_le _)],
  rw ["[", expr tsub_add_eq_add_tsub h₂, ",", expr add_tsub_cancel_of_le h₁, "]"] []
end

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp, to_additive #[]] theorem prod_const (b : β) : «expr = »(«expr∏ in , »((x), s, b), «expr ^ »(b, s.card)) :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr finset.induction_on s (by simp [] [] [] [] [] []) (λ
  a
  s
  has
  ih, by rw ["[", expr prod_insert has, ",", expr card_insert_of_not_mem has, ",", expr pow_succ, ",", expr ih, "]"] [])]

@[toAdditive]
theorem pow_eq_prod_const (b : β) : ∀ n, b ^ n = ∏k in range n, b :=
  by 
    simp 

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident sum_nsmul]]
theorem prod_pow
(s : finset α)
(n : exprℕ())
(f : α → β) : «expr = »(«expr∏ in , »((x), s, «expr ^ »(f x, n)), «expr ^ »(«expr∏ in , »((x), s, f x), n)) :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr finset.induction_on s (by simp [] [] [] [] [] []) (by simp [] [] [] ["[", expr mul_pow, "]"] [] [] { contextual := tt })]

@[toAdditive]
theorem prod_flip {n : ℕ} (f : ℕ → β) : (∏r in range (n+1), f (n - r)) = ∏k in range (n+1), f k :=
  by 
    induction' n with n ih
    ·
      rw [prod_range_one, prod_range_one]
    ·
      rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
      simp [←ih]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_involution
{s : finset α}
{f : α → β} : ∀
(g : ∀ a «expr ∈ » s, α)
(h : ∀ a ha, «expr = »(«expr * »(f a, f (g a ha)), 1))
(g_ne : ∀ a ha, «expr ≠ »(f a, 1) → «expr ≠ »(g a ha, a))
(g_mem : ∀ a ha, «expr ∈ »(g a ha, s))
(g_inv : ∀ a ha, «expr = »(g (g a ha) (g_mem a ha), a)), «expr = »(«expr∏ in , »((x), s, f x), 1) :=
by haveI [] [] [":=", expr classical.dec_eq α]; haveI [] [] [":=", expr classical.dec_eq β]; exact [expr finset.strong_induction_on s (λ
  s
  ih
  g
  h
  g_ne
  g_mem
  g_inv, s.eq_empty_or_nonempty.elim (λ
   hs, «expr ▸ »(hs.symm, rfl)) (λ
   ⟨x, hx⟩, have hmem : ∀
   y «expr ∈ » (s.erase x).erase (g x hx), «expr ∈ »(y, s), from λ y hy, mem_of_mem_erase (mem_of_mem_erase hy),
   have g_inj : ∀
   {x
    hx
    y
    hy}, «expr = »(g x hx, g y hy) → «expr = »(x, y), from λ
   x
   hx
   y
   hy
   h, by rw ["[", "<-", expr g_inv x hx, ",", "<-", expr g_inv y hy, "]"] []; simp [] [] [] ["[", expr h, "]"] [] [],
   have ih' : «expr = »(«expr∏ in , »((y), erase (erase s x) (g x hx), f y), (1 : β)) := ih ((s.erase x).erase (g x hx)) ⟨subset.trans (erase_subset _ _) (erase_subset _ _), λ
    h, not_mem_erase (g x hx) (s.erase x) (h (g_mem x hx))⟩ (λ
    y
    hy, g y (hmem y hy)) (λ
    y
    hy, h y (hmem y hy)) (λ
    y
    hy, g_ne y (hmem y hy)) (λ
    y
    hy, mem_erase.2 ⟨λ
     h : «expr = »(g y _, g x hx), by simpa [] [] [] ["[", expr g_inj h, "]"] [] ["using", expr hy], mem_erase.2 ⟨λ
      h : «expr = »(g y _, x), have «expr = »(y, g x hx), from «expr ▸ »(g_inv y (hmem y hy), by simp [] [] [] ["[", expr h, "]"] [] []),
      by simpa [] [] [] ["[", expr this, "]"] [] ["using", expr hy], g_mem y (hmem y hy)⟩⟩) (λ
    y hy, g_inv y (hmem y hy)),
   if hx1 : «expr = »(f x, 1) then «expr ▸ »(ih', eq.symm (prod_subset hmem (λ
      y
      hy
      hy₁, have «expr ∨ »(«expr = »(y, x), «expr = »(y, g x hx)), by simp [] [] [] ["[", expr hy, "]"] [] ["at", ident hy₁]; tauto [],
      this.elim (λ
       hy, «expr ▸ »(hy.symm, hx1)) (λ
       hy, «expr ▸ »(h x hx, «expr ▸ »(hy, «expr ▸ »(hx1.symm, (one_mul _).symm))))))) else by rw ["[", "<-", expr insert_erase hx, ",", expr prod_insert (not_mem_erase _ _), ",", "<-", expr insert_erase (mem_erase.2 ⟨g_ne x hx hx1, g_mem x hx⟩), ",", expr prod_insert (not_mem_erase _ _), ",", expr ih', ",", expr mul_one, ",", expr h x hx, "]"] []))]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product of the composition of functions `f` and `g`, is the product
over `b ∈ s.image g` of `f b` to the power of the cardinality of the fibre of `b`. See also
`finset.prod_image`. -/
theorem prod_comp
[decidable_eq γ]
(f : γ → β)
(g : α → γ) : «expr = »(«expr∏ in , »((a), s, f (g a)), «expr∏ in , »((b), s.image g, «expr ^ »(f b, (s.filter (λ
     a, «expr = »(g a, b))).card))) :=
calc
  «expr = »(«expr∏ in , »((a), s, f (g a)), «expr∏ in , »((x), (s.image g).sigma (λ
     b : γ, s.filter (λ
      a, «expr = »(g a, b))), f (g x.2))) : prod_bij (λ
   a ha, ⟨g a, a⟩) (by simp [] [] [] [] [] []; tauto []) (λ _ _, rfl) (by simp [] [] [] [] [] []) (by finish [] [])
  «expr = »(..., «expr∏ in , »((b), s.image g, «expr∏ in , »((a), s.filter (λ
      a, «expr = »(g a, b)), f (g a)))) : prod_sigma _ _ _
  «expr = »(..., «expr∏ in , »((b), s.image g, «expr∏ in , »((a), s.filter (λ
      a, «expr = »(g a, b)), f b))) : prod_congr rfl (λ
   b hb, prod_congr rfl (by simp [] [] [] [] [] [] { contextual := tt }))
  «expr = »(..., «expr∏ in , »((b), s.image g, «expr ^ »(f b, (s.filter (λ
       a, «expr = »(g a, b))).card))) : prod_congr rfl (λ _ _, prod_const _)

@[toAdditive]
theorem prod_piecewise [DecidableEq α] (s t : Finset α) (f g : α → β) :
  (∏x in s, (t.piecewise f g) x) = (∏x in s ∩ t, f x)*∏x in s \ t, g x :=
  by 
    rw [piecewise, prod_ite, filter_mem_eq_inter, ←sdiff_eq_filter]

@[toAdditive]
theorem prod_inter_mul_prod_diff [DecidableEq α] (s t : Finset α) (f : α → β) :
  ((∏x in s ∩ t, f x)*∏x in s \ t, f x) = ∏x in s, f x :=
  by 
    convert (s.prod_piecewise t f f).symm 
    simp [Finset.piecewise]

@[toAdditive]
theorem prod_eq_mul_prod_diff_singleton [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) :
  (∏x in s, f x) = f i*∏x in s \ {i}, f x :=
  by 
    convert (s.prod_inter_mul_prod_diff {i} f).symm 
    simp [h]

@[toAdditive]
theorem prod_eq_prod_diff_singleton_mul [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) :
  (∏x in s, f x) = (∏x in s \ {i}, f x)*f i :=
  by 
    rw [prod_eq_mul_prod_diff_singleton h, mul_commₓ]

@[toAdditive]
theorem _root_.fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
  (∏i, f i) = f a*∏i in «expr ᶜ» {a}, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[toAdditive]
theorem _root_.fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
  (∏i, f i) = (∏i in «expr ᶜ» {a}, f i)*f a :=
  prod_eq_prod_diff_singleton_mul (mem_univ a) f

theorem dvd_prod_of_mem (f : α → β) {a : α} {s : Finset α} (ha : a ∈ s) : f a ∣ ∏i in s, f i :=
  by 
    classical 
    rw [Finset.prod_eq_mul_prod_diff_singleton ha]
    exact dvd_mul_right _ _

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[toAdditive "A sum can be partitioned into a sum of sums, each equivalent under a setoid."]
theorem prod_partition (R : Setoidₓ α) [DecidableRel R.r] :
  (∏x in s, f x) = ∏xbar in s.image Quotientₓ.mk, ∏y in s.filter fun y => «expr⟦ ⟧» y = xbar, f y :=
  by 
    refine' (Finset.prod_image' f fun x hx => _).symm 
    rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[toAdditive "If we can partition a sum into subsets that cancel out, then the whole sum cancels."]
theorem prod_cancels_of_partition_cancels (R : Setoidₓ α) [DecidableRel R.r]
  (h : ∀ x _ : x ∈ s, (∏a in s.filter fun y => y ≈ x, f a) = 1) : (∏x in s, f x) = 1 :=
  by 
    rw [prod_partition R, ←Finset.prod_eq_one]
    intro xbar xbar_in_s 
    obtain ⟨x, x_in_s, xbar_eq_x⟩ := mem_image.mp xbar_in_s 
    rw [←xbar_eq_x, filter_congr fun y _ => @Quotientₓ.eq _ R y x]
    apply h x x_in_s

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_update_of_not_mem
[decidable_eq α]
{s : finset α}
{i : α}
(h : «expr ∉ »(i, s))
(f : α → β)
(b : β) : «expr = »(«expr∏ in , »((x), s, function.update f i b x), «expr∏ in , »((x), s, f x)) :=
begin
  apply [expr prod_congr rfl (λ j hj, _)],
  have [] [":", expr «expr ≠ »(j, i)] [],
  by { assume [binders (eq)],
    rw [expr eq] ["at", ident hj],
    exact [expr h hj] },
  simp [] [] [] ["[", expr this, "]"] [] []
end

@[toAdditive]
theorem prod_update_of_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
  (∏x in s, Function.update f i b x) = b*∏x in s \ singleton i, f x :=
  by 
    rw [update_eq_piecewise, prod_piecewise]
    simp [h]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a product of a `finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive #[ident eq_of_card_le_one_of_sum_eq,
   expr "If a sum of a `finset` of size at most 1 has a given\nvalue, so do the terms in that sum."]]
theorem eq_of_card_le_one_of_prod_eq
{s : finset α}
(hc : «expr ≤ »(s.card, 1))
{f : α → β}
{b : β}
(h : «expr = »(«expr∏ in , »((x), s, f x), b)) : ∀ x «expr ∈ » s, «expr = »(f x, b) :=
begin
  intros [ident x, ident hx],
  by_cases [expr hc0, ":", expr «expr = »(s.card, 0)],
  { exact [expr false.elim (card_ne_zero_of_mem hx hc0)] },
  { have [ident h1] [":", expr «expr = »(s.card, 1)] [":=", expr le_antisymm hc (nat.one_le_of_lt (nat.pos_of_ne_zero hc0))],
    rw [expr card_eq_one] ["at", ident h1],
    cases [expr h1] ["with", ident x2, ident hx2],
    rw ["[", expr hx2, ",", expr mem_singleton, "]"] ["at", ident hx],
    simp_rw [expr hx2] ["at", ident h],
    rw [expr hx] [],
    rw [expr prod_singleton] ["at", ident h],
    exact [expr h] }
end

/-- Taking a product over `s : finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`. -/
@[toAdditive
      "Taking a sum over `s : finset α` is the same as adding the value on a single element\n`f a` to the sum over `s.erase a`."]
theorem mul_prod_erase [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
  (f a*∏x in s.erase a, f x) = ∏x in s, f x :=
  by 
    rw [←prod_insert (not_mem_erase a s), insert_erase h]

/-- A variant of `finset.mul_prod_erase` with the multiplication swapped. -/
@[toAdditive "A variant of `finset.add_sum_erase` with the addition swapped."]
theorem prod_erase_mul [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
  ((∏x in s.erase a, f x)*f a) = ∏x in s, f x :=
  by 
    rw [mul_commₓ, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `finset`. -/
@[toAdditive
      "If a function applied at a point is 0, a sum is unchanged by\nremoving that point, if present, from a `finset`."]
theorem prod_erase [DecidableEq α] (s : Finset α) {f : α → β} {a : α} (h : f a = 1) :
  (∏x in s.erase a, f x) = ∏x in s, f x :=
  by 
    rw [←sdiff_singleton_eq_erase]
    refine' prod_subset (sdiff_subset _ _) fun x hx hnx => _ 
    rw [sdiff_singleton_eq_erase] at hnx 
    rwa [eq_of_mem_of_not_mem_erase hx hnx]

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `finset`. -/
@[toAdditive "If a sum is 0 and the function is 0 except possibly at one\npoint, it is 0 everywhere on the `finset`."]
theorem eq_one_of_prod_eq_one {s : Finset α} {f : α → β} {a : α} (hp : (∏x in s, f x) = 1)
  (h1 : ∀ x _ : x ∈ s, x ≠ a → f x = 1) : ∀ x _ : x ∈ s, f x = 1 :=
  by 
    intro x hx 
    classical 
    byCases' h : x = a
    ·
      rw [h]
      rw [h] at hx 
      rw [←prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (not_mem_singleton.1 ha), prod_singleton] at
        hp 
      exact hp
    ·
      exact h1 x hx h

theorem prod_pow_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
  (∏x in s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 :=
  by 
    simp 

end CommMonoidₓ

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
theorem prod_add_prod_eq [CommSemiringₓ β] {s : Finset α} {i : α} {f g h : α → β} (hi : i ∈ s) (h1 : (g i+h i) = f i)
  (h2 : ∀ j _ : j ∈ s, j ≠ i → g j = f j) (h3 : ∀ j _ : j ∈ s, j ≠ i → h j = f j) :
  ((∏i in s, g i)+∏i in s, h i) = ∏i in s, f i :=
  by 
    classical 
    simpRw [prod_eq_mul_prod_diff_singleton hi, ←h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa

theorem card_eq_sum_ones (s : Finset α) : s.card = ∑_ in s, 1 :=
  by 
    simp 

theorem sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀ x _ : x ∈ s, f x = m) : (∑x in s, f x) = card s*m :=
  by 
    rw [←Nat.nsmul_eq_mul, ←sum_const]
    apply sum_congr rfl h₁

@[simp]
theorem sum_boole {s : Finset α} {p : α → Prop} [NonAssocSemiring β] {hp : DecidablePred p} :
  (∑x in s, if p x then (1 : β) else (0 : β)) = (s.filter p).card :=
  by 
    simp [sum_ite]

theorem sum_comp [AddCommMonoidₓ β] [DecidableEq γ] (f : γ → β) (g : α → γ) :
  (∑a in s, f (g a)) = ∑b in s.image g, (s.filter fun a => g a = b).card • f b :=
  @prod_comp (Multiplicative β) _ _ _ _ _ _ _

attribute
  [toAdditive
      "The sum of the composition of functions `f` and `g`, is the sum\nover `b ∈ s.image g` of `f b` times of the cardinality of the fibre of `b`. See also\n`finset.sum_image`."]
  prod_comp

theorem eq_sum_range_sub [AddCommGroupₓ β] (f : ℕ → β) (n : ℕ) : f n = f 0+∑i in range n, f (i+1) - f i :=
  by 
    rw [Finset.sum_range_sub, add_sub_cancel'_right]

theorem eq_sum_range_sub' [AddCommGroupₓ β] (f : ℕ → β) (n : ℕ) :
  f n = ∑i in range (n+1), if i = 0 then f 0 else f i - f (i - 1) :=
  by 
    convLHS => rw [Finset.eq_sum_range_sub f]
    simp [Finset.sum_range_succ', add_commₓ]

section Opposite

open MulOpposite

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp]
theorem op_sum [AddCommMonoidₓ β] {s : Finset α} (f : α → β) : op (∑x in s, f x) = ∑x in s, op (f x) :=
  (op_add_equiv : β ≃+ «expr ᵐᵒᵖ» β).map_sum _ _

@[simp]
theorem unop_sum [AddCommMonoidₓ β] {s : Finset α} (f : α → «expr ᵐᵒᵖ» β) : unop (∑x in s, f x) = ∑x in s, unop (f x) :=
  (op_add_equiv : β ≃+ «expr ᵐᵒᵖ» β).symm.map_sum _ _

end Opposite

section CommGroupₓ

variable [CommGroupₓ β]

@[simp, toAdditive]
theorem prod_inv_distrib : (∏x in s, f x⁻¹) = (∏x in s, f x)⁻¹ :=
  (MonoidHom.map_prod (CommGroupₓ.invMonoidHom : β →* β) f s).symm

@[toAdditive zsmul_sum]
theorem prod_zpow (f : α → β) (s : Finset α) (n : ℤ) : (∏a in s, f a) ^ n = ∏a in s, f a ^ n :=
  (zpowGroupHom n : β →* β).map_prod f s

end CommGroupₓ

@[simp]
theorem card_sigma {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) : card (s.sigma t) = ∑a in s, card (t a) :=
  Multiset.card_sigma _ _

theorem card_bUnion [DecidableEq β] {s : Finset α} {t : α → Finset β}
  (h : ∀ x _ : x ∈ s, ∀ y _ : y ∈ s, x ≠ y → Disjoint (t x) (t y)) : (s.bUnion t).card = ∑u in s, card (t u) :=
  calc (s.bUnion t).card = ∑i in s.bUnion t, 1 :=
    by 
      simp 
    _ = ∑a in s, ∑i in t a, 1 := Finset.sum_bUnion h 
    _ = ∑u in s, card (t u) :=
    by 
      simp 
    

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_bUnion_le
[decidable_eq β]
{s : finset α}
{t : α → finset β} : «expr ≤ »((s.bUnion t).card, «expr∑ in , »((a), s, (t a).card)) :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr finset.induction_on s (by simp [] [] [] [] [] []) (λ
  a s has ih, calc
    «expr ≤ »(((insert a s).bUnion t).card, «expr + »((t a).card, (s.bUnion t).card)) : by rw [expr bUnion_insert] []; exact [expr finset.card_union_le _ _]
    «expr ≤ »(..., «expr∑ in , »((a), insert a s, card (t a))) : by rw [expr sum_insert has] []; exact [expr add_le_add_left ih _])]

theorem card_eq_sum_card_fiberwise [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
  (H : ∀ x _ : x ∈ s, f x ∈ t) : s.card = ∑a in t, (s.filter fun x => f x = a).card :=
  by 
    simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

theorem card_eq_sum_card_image [DecidableEq β] (f : α → β) (s : Finset α) :
  s.card = ∑a in s.image f, (s.filter fun x => f x = a).card :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

@[simp]
theorem sum_sub_distrib [AddCommGroupₓ β] : (∑x in s, f x - g x) = (∑x in s, f x) - ∑x in s, g x :=
  by 
    simpa only [sub_eq_add_neg] using sum_add_distrib.trans (congr_argₓ _ sum_neg_distrib)

section ProdEqZero

variable [CommMonoidWithZero β]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_eq_zero (ha : «expr ∈ »(a, s)) (h : «expr = »(f a, 0)) : «expr = »(«expr∏ in , »((x), s, f x), 0) :=
by { haveI [] [] [":=", expr classical.dec_eq α],
  rw ["[", "<-", expr prod_erase_mul _ _ ha, ",", expr h, ",", expr mul_zero, "]"] [] }

theorem prod_boole {s : Finset α} {p : α → Prop} [DecidablePred p] :
  (∏i in s, ite (p i) (1 : β) (0 : β)) = ite (∀ i _ : i ∈ s, p i) 1 0 :=
  by 
    splitIfs
    ·
      apply prod_eq_one 
      intro i hi 
      rw [if_pos (h i hi)]
    ·
      pushNeg  at h 
      rcases h with ⟨i, hi, hq⟩
      apply prod_eq_zero hi 
      rw [if_neg hq]

variable [Nontrivial β] [NoZeroDivisors β]

theorem prod_eq_zero_iff : (∏x in s, f x) = 0 ↔ ∃ (a : _)(_ : a ∈ s), f a = 0 :=
  by 
    classical 
    apply Finset.induction_on s 
    exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => H.elim⟩
    intro a s ha ih 
    rw [prod_insert ha, mul_eq_zero, bex_def, exists_mem_insert, ih, ←bex_def]

theorem prod_ne_zero_iff : (∏x in s, f x) ≠ 0 ↔ ∀ a _ : a ∈ s, f a ≠ 0 :=
  by 
    rw [Ne, prod_eq_zero_iff]
    pushNeg

end ProdEqZero

section CommGroupWithZero

variable [CommGroupWithZero β]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem prod_inv_distrib' : «expr = »(«expr∏ in , »((x), s, «expr ⁻¹»(f x)), «expr ⁻¹»(«expr∏ in , »((x), s, f x))) :=
begin
  classical,
  by_cases [expr h, ":", expr «expr∃ , »((x «expr ∈ » s), «expr = »(f x, 0))],
  { simpa [] [] [] ["[", expr prod_eq_zero_iff.mpr h, ",", expr prod_eq_zero_iff, "]"] [] ["using", expr h] },
  { push_neg ["at", ident h],
    have [ident h'] [] [":=", expr prod_ne_zero_iff.mpr h],
    have [ident hf] [":", expr ∀
     x «expr ∈ » s, «expr = »(«expr * »(«expr ⁻¹»(f x), f x), 1)] [":=", expr λ x hx, inv_mul_cancel (h x hx)],
    apply [expr mul_right_cancel₀ h'],
    simp [] [] [] ["[", expr h, ",", expr h', ",", "<-", expr finset.prod_mul_distrib, ",", expr prod_congr rfl hf, "]"] [] [] }
end

end CommGroupWithZero

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_unique_nonempty
{α β : Type*}
[comm_monoid β]
[unique α]
(s : finset α)
(f : α → β)
(h : s.nonempty) : «expr = »(«expr∏ in , »((x), s, f x), f (default α)) :=
begin
  obtain ["⟨", ident a, ",", ident ha, "⟩", ":=", expr h],
  have [] [":", expr «expr = »(s, {a})] [],
  { ext [] [ident b] [],
    simpa [] [] [] ["[", expr subsingleton.elim a b, "]"] [] ["using", expr ha] },
  rw ["[", expr this, ",", expr finset.prod_singleton, ",", expr subsingleton.elim a (default α), "]"] []
end

end Finset

namespace Fintype

open Finset

/-- `fintype.prod_bijective` is a variant of `finset.prod_bij` that accepts `function.bijective`.

See `function.bijective.prod_comp` for a version without `h`. -/
@[toAdditive
      "`fintype.sum_equiv` is a variant of `finset.sum_bij` that accepts\n`function.bijective`.\n\nSee `function.bijective.sum_comp` for a version without `h`. "]
theorem prod_bijective {α β M : Type _} [Fintype α] [Fintype β] [CommMonoidₓ M] (e : α → β) (he : Function.Bijective e)
  (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) : (∏x : α, f x) = ∏x : β, g x :=
  prod_bij (fun x _ => e x) (fun x _ => mem_univ (e x)) (fun x _ => h x) (fun x x' _ _ h => he.injective h)
    fun y _ => (he.surjective y).imp$ fun a h => ⟨mem_univ _, h.symm⟩

/-- `fintype.prod_equiv` is a specialization of `finset.prod_bij` that
automatically fills in most arguments.

See `equiv.prod_comp` for a version without `h`.
-/
@[toAdditive
      "`fintype.sum_equiv` is a specialization of `finset.sum_bij` that\nautomatically fills in most arguments.\n\nSee `equiv.sum_comp` for a version without `h`.\n"]
theorem prod_equiv {α β M : Type _} [Fintype α] [Fintype β] [CommMonoidₓ M] (e : α ≃ β) (f : α → M) (g : β → M)
  (h : ∀ x, f x = g (e x)) : (∏x : α, f x) = ∏x : β, g x :=
  prod_bijective e e.bijective f g h

@[toAdditive]
theorem prod_finset_coe [CommMonoidₓ β] : (∏i : (s : Set α), f i) = ∏i in s, f i :=
  (Finset.prod_subtype s (fun _ => Iff.rfl) f).symm

@[toAdditive]
theorem prod_unique {α β : Type _} [CommMonoidₓ β] [Unique α] (f : α → β) : (∏x : α, f x) = f (default α) :=
  by 
    rw [univ_unique, prod_singleton]

@[toAdditive]
theorem prod_empty {α β : Type _} [CommMonoidₓ β] [IsEmpty α] (f : α → β) : (∏x : α, f x) = 1 :=
  by 
    rw [eq_empty_of_is_empty (univ : Finset α), Finset.prod_empty]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_subsingleton
{α β : Type*}
[comm_monoid β]
[subsingleton α]
(f : α → β)
(a : α) : «expr = »(«expr∏ , »((x : α), f x), f a) :=
begin
  haveI [] [":", expr unique α] [":=", expr unique_of_subsingleton a],
  convert [] [expr prod_unique f] []
end

@[toAdditive]
theorem prod_subtype_mul_prod_subtype {α β : Type _} [Fintype α] [CommMonoidₓ β] (p : α → Prop) (f : α → β)
  [DecidablePred p] : ((∏i : { x // p x }, f i)*∏i : { x // ¬p x }, f i) = ∏i, f i :=
  by 
    classical 
    let s := { x | p x }.toFinset 
    rw [←Finset.prod_subtype s, ←Finset.prod_subtype («expr ᶜ» s)]
    ·
      exact Finset.prod_mul_prod_compl _ _
    ·
      simp 
    ·
      simp 

end Fintype

namespace List

@[toAdditive]
theorem prod_to_finset {M : Type _} [DecidableEq α] [CommMonoidₓ M] (f : α → M) :
  ∀ {l : List α} hl : l.nodup, l.to_finset.prod f = (l.map f).Prod
| [], _ =>
  by 
    simp 
| a :: l, hl =>
  let ⟨not_mem, hl⟩ := List.nodup_cons.mp hl 
  by 
    simp [Finset.prod_insert (mt list.mem_to_finset.mp not_mem), prod_to_finset hl]

end List

namespace Multiset

variable [DecidableEq α]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem to_finset_sum_count_eq (s : multiset α) : «expr = »(«expr∑ in , »((a), s.to_finset, s.count a), s.card) :=
multiset.induction_on s rfl (assume a s ih, calc
   «expr = »(«expr∑ in , »((x), to_finset «expr ::ₘ »(a, s), count x «expr ::ₘ »(a, s)), «expr∑ in , »((x), to_finset «expr ::ₘ »(a, s), «expr + »(if «expr = »(x, a) then 1 else 0, count x s))) : «expr $ »(finset.sum_congr rfl, λ
    _
    _, by split_ifs [] []; [simp [] [] ["only"] ["[", expr h, ",", expr count_cons_self, ",", expr nat.one_add, "]"] [] [], simp [] [] ["only"] ["[", expr count_cons_of_ne h, ",", expr zero_add, "]"] [] []])
   «expr = »(..., card «expr ::ₘ »(a, s)) : begin
     by_cases [expr «expr ∈ »(a, s.to_finset)],
     { have [] [":", expr «expr = »(«expr∑ in , »((x), s.to_finset, ite «expr = »(x, a) 1 0), «expr∑ in , »((x), {a}, ite «expr = »(x, a) 1 0))] [],
       { rw ["[", expr finset.sum_ite_eq', ",", expr if_pos h, ",", expr finset.sum_singleton, ",", expr if_pos rfl, "]"] [] },
       rw ["[", expr to_finset_cons, ",", expr finset.insert_eq_of_mem h, ",", expr finset.sum_add_distrib, ",", expr ih, ",", expr this, ",", expr finset.sum_singleton, ",", expr if_pos rfl, ",", expr add_comm, ",", expr card_cons, "]"] [] },
     { have [ident ha] [":", expr «expr ∉ »(a, s)] [],
       by rwa [expr mem_to_finset] ["at", ident h],
       have [] [":", expr «expr = »(«expr∑ in , »((x), to_finset s, ite «expr = »(x, a) 1 0), «expr∑ in , »((x), to_finset s, 0))] [],
       from [expr finset.sum_congr rfl (λ x hx, «expr $ »(if_neg, by rintro [ident rfl]; cc))],
       rw ["[", expr to_finset_cons, ",", expr finset.sum_insert h, ",", expr if_pos rfl, ",", expr finset.sum_add_distrib, ",", expr this, ",", expr finset.sum_const_zero, ",", expr ih, ",", expr count_eq_zero_of_not_mem ha, ",", expr zero_add, ",", expr add_comm, ",", expr card_cons, "]"] [] }
   end)

theorem count_sum' {s : Finset β} {a : α} {f : β → Multiset α} : count a (∑x in s, f x) = ∑x in s, count a (f x) :=
  by 
    dunfold Finset.sum 
    rw [count_sum]

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem to_finset_sum_count_nsmul_eq
(s : multiset α) : «expr = »(«expr∑ in , »((a), s.to_finset, «expr • »(s.count a, {a})), s) :=
begin
  apply [expr ext'],
  intro [ident b],
  rw [expr count_sum'] [],
  have [ident h] [":", expr «expr = »(count b s, count b «expr • »(count b s, {b}))] [],
  { rw ["[", expr count_nsmul, ",", expr count_singleton_self, ",", expr mul_one, "]"] [] },
  rw [expr h] [],
  clear [ident h],
  apply [expr finset.sum_eq_single b],
  { intros [ident c, ident h, ident hcb],
    rw [expr count_nsmul] [],
    convert [] [expr mul_zero (count c s)] [],
    apply [expr count_eq_zero.mpr],
    exact [expr finset.not_mem_singleton.mpr (ne.symm hcb)] },
  { intro [ident hb],
    rw ["[", expr count_eq_zero_of_not_mem (mt mem_to_finset.2 hb), ",", expr count_nsmul, ",", expr zero_mul, "]"] [] }
end

-- error in Algebra.BigOperators.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_smul_of_dvd_count
(s : multiset α)
{k : exprℕ()}
(h : ∀
 a : α, «expr ∈ »(a, s) → «expr ∣ »(k, multiset.count a s)) : «expr∃ , »((u : multiset α), «expr = »(s, «expr • »(k, u))) :=
begin
  use [expr «expr∑ in , »((a), s.to_finset, «expr • »(«expr / »(s.count a, k), {a}))],
  have [ident h₂] [":", expr «expr = »(«expr∑ in , »((x : α), s.to_finset, «expr • »(k, «expr • »(«expr / »(count x s, k), ({x} : multiset α)))), «expr∑ in , »((x : α), s.to_finset, «expr • »(count x s, {x})))] [],
  { apply [expr finset.sum_congr rfl],
    intros [ident x, ident hx],
    rw ["[", "<-", expr mul_nsmul, ",", expr nat.mul_div_cancel' (h x (mem_to_finset.mp hx)), "]"] [] },
  rw ["[", "<-", expr finset.sum_nsmul, ",", expr h₂, ",", expr to_finset_sum_count_nsmul_eq, "]"] []
end

end Multiset

@[simp, normCast]
theorem Nat.cast_sum [AddCommMonoidₓ β] [HasOne β] (s : Finset α) (f : α → ℕ) :
  «expr↑ » (∑x in s, f x : ℕ) = ∑x in s, (f x : β) :=
  (Nat.castAddMonoidHom β).map_sum f s

@[simp, normCast]
theorem Int.cast_sum [AddCommGroupₓ β] [HasOne β] (s : Finset α) (f : α → ℤ) :
  «expr↑ » (∑x in s, f x : ℤ) = ∑x in s, (f x : β) :=
  (Int.castAddHom β).map_sum f s

@[simp, normCast]
theorem Nat.cast_prod {R : Type _} [CommSemiringₓ R] (f : α → ℕ) (s : Finset α) :
  («expr↑ » (∏i in s, f i) : R) = ∏i in s, f i :=
  (Nat.castRingHom R).map_prod _ _

@[simp, normCast]
theorem Int.cast_prod {R : Type _} [CommRingₓ R] (f : α → ℤ) (s : Finset α) :
  («expr↑ » (∏i in s, f i) : R) = ∏i in s, f i :=
  (Int.castRingHom R).map_prod _ _

@[simp, normCast]
theorem Units.coe_prod {M : Type _} [CommMonoidₓ M] (f : α → Units M) (s : Finset α) :
  («expr↑ » (∏i in s, f i) : M) = ∏i in s, f i :=
  (Units.coeHom M).map_prod _ _

theorem nat_abs_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℤ) : (∑i in s, f i).natAbs ≤ ∑i in s, (f i).natAbs :=
  by 
    classical 
    apply Finset.induction_on s
    ·
      simp only [Finset.sum_empty, Int.nat_abs_zero]
    ·
      intro i s his IH 
      simp only [his, Finset.sum_insert, not_false_iff]
      exact (Int.nat_abs_add_le _ _).trans (add_le_add le_rfl IH)

