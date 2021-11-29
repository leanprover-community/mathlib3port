import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Data.Finset.Pi 
import Mathbin.Data.Finset.Powerset

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/


universe u v w

open_locale BigOperators

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {b : β} {f g : α → β}

section Semiringₓ

variable [NonUnitalNonAssocSemiring β]

theorem sum_mul : ((∑x in s, f x)*b) = ∑x in s, f x*b :=
  AddMonoidHom.map_sum (AddMonoidHom.mulRight b) _ s

theorem mul_sum : (b*∑x in s, f x) = ∑x in s, b*f x :=
  AddMonoidHom.map_sum (AddMonoidHom.mulLeft b) _ s

theorem sum_mul_sum {ι₁ : Type _} {ι₂ : Type _} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (f₁ : ι₁ → β) (f₂ : ι₂ → β) :
  ((∑x₁ in s₁, f₁ x₁)*∑x₂ in s₂, f₂ x₂) = ∑p in s₁.product s₂, f₁ p.1*f₂ p.2 :=
  by 
    rw [sum_product, sum_mul, sum_congr rfl]
    intros 
    rw [mul_sum]

end Semiringₓ

section Semiringₓ

variable [NonAssocSemiring β]

theorem sum_mul_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
  (∑x in s, f x*ite (a = x) 1 0) = ite (a ∈ s) (f a) 0 :=
  by 
    simp 

theorem sum_boole_mul [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
  (∑x in s, ite (a = x) 1 0*f x) = ite (a ∈ s) (f a) 0 :=
  by 
    simp 

end Semiringₓ

theorem sum_div [DivisionRing β] {s : Finset α} {f : α → β} {b : β} : (∑x in s, f x) / b = ∑x in s, f x / b :=
  by 
    simp only [div_eq_mul_inv, sum_mul]

section CommSemiringₓ

variable [CommSemiringₓ β]

-- error in Algebra.BigOperators.Ring: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product over a sum can be written as a sum over the product of sets, `finset.pi`.
  `finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
theorem prod_sum
{δ : α → Type*}
[decidable_eq α]
[∀ a, decidable_eq (δ a)]
{s : finset α}
{t : ∀ a, finset (δ a)}
{f : ∀
 a, δ a → β} : «expr = »(«expr∏ in , »((a), s, «expr∑ in , »((b), t a, f a b)), «expr∑ in , »((p), s.pi t, «expr∏ in , »((x), s.attach, f x.1 (p x.1 x.2)))) :=
begin
  induction [expr s] ["using", ident finset.induction] ["with", ident a, ident s, ident ha, ident ih] [],
  { rw ["[", expr pi_empty, ",", expr sum_singleton, "]"] [],
    refl },
  { have [ident h₁] [":", expr ∀
     x «expr ∈ » t a, ∀
     y «expr ∈ » t a, ∀
     h : «expr ≠ »(x, y), disjoint (image (pi.cons s a x) (pi s t)) (image (pi.cons s a y) (pi s t))] [],
    { assume [binders (x hx y hy h)],
      simp [] [] ["only"] ["[", expr disjoint_iff_ne, ",", expr mem_image, "]"] [] [],
      rintros ["_", "⟨", ident p₂, ",", ident hp, ",", ident eq₂, "⟩", "_", "⟨", ident p₃, ",", ident hp₃, ",", ident eq₃, "⟩", ident eq],
      have [] [":", expr «expr = »(pi.cons s a x p₂ a (mem_insert_self _ _), pi.cons s a y p₃ a (mem_insert_self _ _))] [],
      { rw ["[", expr eq₂, ",", expr eq₃, ",", expr eq, "]"] [] },
      rw ["[", expr pi.cons_same, ",", expr pi.cons_same, "]"] ["at", ident this],
      exact [expr h this] },
    rw ["[", expr prod_insert ha, ",", expr pi_insert ha, ",", expr ih, ",", expr sum_mul, ",", expr sum_bUnion h₁, "]"] [],
    refine [expr sum_congr rfl (λ b _, _)],
    have [ident h₂] [":", expr ∀
     p₁ «expr ∈ » pi s t, ∀ p₂ «expr ∈ » pi s t, «expr = »(pi.cons s a b p₁, pi.cons s a b p₂) → «expr = »(p₁, p₂)] [],
    from [expr assume p₁ h₁ p₂ h₂ eq, pi_cons_injective ha eq],
    rw ["[", expr sum_image h₂, ",", expr mul_sum, "]"] [],
    refine [expr sum_congr rfl (λ g _, _)],
    rw ["[", expr attach_insert, ",", expr prod_insert, ",", expr prod_image, "]"] [],
    { simp [] [] ["only"] ["[", expr pi.cons_same, "]"] [] [],
      congr' [] ["with", "⟨", ident v, ",", ident hv, "⟩"],
      congr' [] [],
      exact [expr (pi.cons_ne (by rintro [ident rfl]; exact [expr ha hv])).symm] },
    { exact [expr λ _ _ _ _, «expr ∘ »(subtype.eq, subtype.mk.inj)] },
    { simp [] [] ["only"] ["[", expr mem_image, "]"] [] [],
      rintro ["⟨", "⟨", "_", ",", ident hm, "⟩", ",", "_", ",", ident rfl, "⟩"],
      exact [expr ha hm] } }
end

open_locale Classical

/-- The product of `f a + g a` over all of `s` is the sum
  over the powerset of `s` of the product of `f` over a subset `t` times
  the product of `g` over the complement of `t`  -/
theorem prod_add (f g : α → β) (s : Finset α) :
  (∏a in s, f a+g a) = ∑t in s.powerset, (∏a in t, f a)*∏a in s \ t, g a :=
  calc (∏a in s, f a+g a) = ∏a in s, ∑p in ({True, False} : Finset Prop), if p then f a else g a :=
    by 
      simp 
    _ =
      ∑p in (s.pi fun _ => {True, False} : Finset (∀ a _ : a ∈ s, Prop)),
        ∏a in s.attach, if p a.1 a.2 then f a.1 else g a.1 :=
    prod_sum 
    _ = ∑t in s.powerset, (∏a in t, f a)*∏a in s \ t, g a :=
    by 
      refine' Eq.symm (sum_bij (fun t _ a _ => a ∈ t) _ _ _ _)
      ·
        simp [subset_iff] <;> tauto
      ·
        intro t ht 
        erw [prod_ite (fun a : { a // a ∈ s } => f a.1) fun a : { a // a ∈ s } => g a.1]
        refine'
            congr_arg2 _
              (prod_bij (fun a : α ha : a ∈ t => ⟨a, mem_powerset.1 ht ha⟩) _ _ _
                fun b hb =>
                  ⟨b,
                    by 
                      cases b <;> finish⟩)
              (prod_bij
                (fun a : α ha : a ∈ s \ t =>
                  ⟨a,
                    by 
                      simp_all ⟩)
                _ _ _
                fun b hb =>
                  ⟨b,
                    by 
                      cases b <;> finish⟩) <;>
          intros  <;> simp_all  <;> simp_all 
      ·
        finish [Function.funext_iffₓ, Finset.ext_iff, subset_iff]
      ·
        intro f hf 
        exact
          ⟨s.filter fun a : α => ∃ h : a ∈ s, f a h,
            by 
              simp ,
            by 
              funext  <;> intros  <;> simp ⟩
    

-- error in Algebra.BigOperators.Ring: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j)`. -/
theorem prod_add_ordered
{ι R : Type*}
[comm_semiring R]
[linear_order ι]
(s : finset ι)
(f
 g : ι → R) : «expr = »(«expr∏ in , »((i), s, «expr + »(f i, g i)), «expr + »(«expr∏ in , »((i), s, f i), «expr∑ in , »((i), s, «expr * »(«expr * »(g i, «expr∏ in , »((j), s.filter ((«expr < » i)), «expr + »(f j, g j))), «expr∏ in , »((j), s.filter (λ
      j, «expr < »(i, j)), f j))))) :=
begin
  refine [expr finset.induction_on_max s (by simp [] [] [] [] [] []) _],
  clear [ident s],
  intros [ident a, ident s, ident ha, ident ihs],
  have [ident ha'] [":", expr «expr ∉ »(a, s)] [],
  from [expr λ ha', (ha a ha').false],
  rw ["[", expr prod_insert ha', ",", expr prod_insert ha', ",", expr sum_insert ha', ",", expr filter_insert, ",", expr if_neg (lt_irrefl a), ",", expr filter_true_of_mem ha, ",", expr ihs, ",", expr add_mul, ",", expr mul_add, ",", expr mul_add, ",", expr add_assoc, "]"] [],
  congr' [1] [],
  rw [expr add_comm] [],
  congr' [1] [],
  { rw ["[", expr filter_false_of_mem, ",", expr prod_empty, ",", expr mul_one, "]"] [],
    exact [expr (forall_mem_insert _ _ _).2 ⟨lt_irrefl a, λ i hi, (ha i hi).not_lt⟩] },
  { rw [expr mul_sum] [],
    refine [expr sum_congr rfl (λ i hi, _)],
    rw ["[", expr filter_insert, ",", expr if_neg (ha i hi).not_lt, ",", expr filter_insert, ",", expr if_pos (ha i hi), ",", expr prod_insert, ",", expr mul_left_comm, "]"] [],
    exact [expr mt (λ ha, (mem_filter.1 ha).1) ha'] }
end

/-- `∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j)`. -/
theorem prod_sub_ordered {ι R : Type _} [CommRingₓ R] [LinearOrderₓ ι] (s : Finset ι) (f g : ι → R) :
  (∏i in s, f i - g i) =
    (∏i in s, f i) - ∑i in s, (g i*∏j in s.filter (· < i), f j - g j)*∏j in s.filter fun j => i < j, f j :=
  by 
    simp only [sub_eq_add_neg]
    convert prod_add_ordered s f fun i => -g i 
    simp 

/-- `∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in construction of
a partition of unity from a collection of “bump” functions.  -/
theorem prod_one_sub_ordered {ι R : Type _} [CommRingₓ R] [LinearOrderₓ ι] (s : Finset ι) (f : ι → R) :
  (∏i in s, 1 - f i) = 1 - ∑i in s, f i*∏j in s.filter (· < i), 1 - f j :=
  by 
    rw [prod_sub_ordered]
    simp 

/--  Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `finset`
gives `(a + b)^s.card`.-/
theorem sum_pow_mul_eq_add_pow {α R : Type _} [CommSemiringₓ R] (a b : R) (s : Finset α) :
  (∑t in s.powerset, (a ^ t.card)*b ^ (s.card - t.card)) = (a+b) ^ s.card :=
  by 
    rw [←prod_const, prod_add]
    refine' Finset.sum_congr rfl fun t ht => _ 
    rw [prod_const, prod_const, ←card_sdiff (mem_powerset.1 ht)]

theorem prod_pow_eq_pow_sum {x : β} {f : α → ℕ} : ∀ {s : Finset α}, (∏i in s, x ^ f i) = x ^ ∑x in s, f x :=
  by 
    apply Finset.induction
    ·
      simp 
    ·
      intro a s has H 
      rw [Finset.prod_insert has, Finset.sum_insert has, pow_addₓ, H]

theorem dvd_sum {b : β} {s : Finset α} {f : α → β} (h : ∀ x _ : x ∈ s, b ∣ f x) : b ∣ ∑x in s, f x :=
  Multiset.dvd_sum
    fun y hy =>
      by 
        rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩ <;> exact h x hx

@[normCast]
theorem prod_nat_cast (s : Finset α) (f : α → ℕ) : «expr↑ » (∏x in s, f x : ℕ) = ∏x in s, (f x : β) :=
  (Nat.castRingHom β).map_prod f s

end CommSemiringₓ

section CommRingₓ

variable {R : Type _} [CommRingₓ R]

theorem prod_range_cast_nat_sub (n k : ℕ) : (∏i in range k, (n - i : R)) = (∏i in range k, n - i : ℕ) :=
  by 
    rw [prod_nat_cast]
    cases' le_or_ltₓ k n with hkn hnk
    ·
      exact prod_congr rfl fun i hi => (Nat.cast_sub$ (mem_range.1 hi).le.trans hkn).symm
    ·
      rw [←mem_range] at hnk 
      rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp 

end CommRingₓ

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[toAdditive]
theorem prod_powerset_insert [DecidableEq α] [CommMonoidₓ β] {s : Finset α} {x : α} (h : x ∉ s) (f : Finset α → β) :
  (∏a in (insert x s).Powerset, f a) = (∏a in s.powerset, f a)*∏t in s.powerset, f (insert x t) :=
  by 
    rw [powerset_insert, Finset.prod_union, Finset.prod_image]
    ·
      intro t₁ h₁ t₂ h₂ heq 
      rw [←Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₁ h),
        ←Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₂ h), HEq]
    ·
      rw [Finset.disjoint_iff_ne]
      intro t₁ h₁ t₂ h₂ 
      rcases Finset.mem_image.1 h₂ with ⟨t₃, h₃, H₃₂⟩
      rw [←H₃₂]
      exact ne_insert_of_not_mem _ _ (not_mem_of_mem_powerset_of_not_mem h₁ h)

/-- A product over `powerset s` is equal to the double product over
sets of subsets of `s` with `card s = k`, for `k = 1, ... , card s`. -/
@[toAdditive]
theorem prod_powerset [CommMonoidₓ β] (s : Finset α) (f : Finset α → β) :
  (∏t in powerset s, f t) = ∏j in range (card s+1), ∏t in powerset_len j s, f t :=
  by 
    classical 
    rw [powerset_card_bUnion, prod_bUnion]
    intro i hi j hj hij 
    rw [Function.onFun, powerset_len_eq_filter, powerset_len_eq_filter, disjoint_filter]
    intro x hx hc hnc 
    apply hij 
    rwa [←hc]

end Finset

