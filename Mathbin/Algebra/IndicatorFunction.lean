import Mathbin.Algebra.Support

/-!
# Indicator function

- `indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `mul_indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.


## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `λx, 1`.

## Tags
indicator, characteristic
-/


noncomputable theory

open_locale Classical BigOperators

open Function

variable{α β ι M N : Type _}

namespace Set

section HasOne

variable[HasOne M][HasOne N]{s t : Set α}{f g : α → M}{a : α}

/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
def indicator {M} [HasZero M] (s : Set α) (f : α → M) : α → M :=
  fun x => if x ∈ s then f x else 0

/-- `mul_indicator s f a` is `f a` if `a ∈ s`, `1` otherwise.  -/
@[toAdditive]
def mul_indicator (s : Set α) (f : α → M) : α → M :=
  fun x => if x ∈ s then f x else 1

@[simp, toAdditive]
theorem piecewise_eq_mul_indicator : s.piecewise f 1 = s.mul_indicator f :=
  rfl

@[toAdditive]
theorem mul_indicator_apply (s : Set α) (f : α → M) (a : α) : mul_indicator s f a = if a ∈ s then f a else 1 :=
  rfl

@[simp, toAdditive]
theorem mul_indicator_of_mem (h : a ∈ s) (f : α → M) : mul_indicator s f a = f a :=
  if_pos h

@[simp, toAdditive]
theorem mul_indicator_of_not_mem (h : a ∉ s) (f : α → M) : mul_indicator s f a = 1 :=
  if_neg h

@[toAdditive]
theorem mul_indicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
  mul_indicator s f a = 1 ∨ mul_indicator s f a = f a :=
  if h : a ∈ s then Or.inr (mul_indicator_of_mem h f) else Or.inl (mul_indicator_of_not_mem h f)

@[simp, toAdditive]
theorem mul_indicator_apply_eq_self : s.mul_indicator f a = f a ↔ a ∉ s → f a = 1 :=
  ite_eq_left_iff.trans$
    by 
      rw [@eq_comm _ (f a)]

@[simp, toAdditive]
theorem mul_indicator_eq_self : s.mul_indicator f = f ↔ mul_support f ⊆ s :=
  by 
    simp only [funext_iff, subset_def, mem_mul_support, mul_indicator_apply_eq_self, not_imp_comm]

@[toAdditive]
theorem mul_indicator_eq_self_of_superset (h1 : s.mul_indicator f = f) (h2 : s ⊆ t) : t.mul_indicator f = f :=
  by 
    rw [mul_indicator_eq_self] at h1⊢
    exact subset.trans h1 h2

@[simp, toAdditive]
theorem mul_indicator_apply_eq_one : mul_indicator s f a = 1 ↔ a ∈ s → f a = 1 :=
  ite_eq_right_iff

@[simp, toAdditive]
theorem mul_indicator_eq_one : (mul_indicator s f = fun x => 1) ↔ Disjoint (mul_support f) s :=
  by 
    simp only [funext_iff, mul_indicator_apply_eq_one, Set.disjoint_left, mem_mul_support, not_imp_not]

@[simp, toAdditive]
theorem mul_indicator_eq_one' : mul_indicator s f = 1 ↔ Disjoint (mul_support f) s :=
  mul_indicator_eq_one

@[toAdditive]
theorem mul_indicator_eq_one_iff (a : α) : s.mul_indicator f a ≠ 1 ↔ a ∈ s ∩ mul_support f :=
  by 
    split  <;> intro h
    ·
      byContra hmem 
      simp only [Set.mem_inter_eq, not_and, not_not, Function.mem_mul_support] at hmem 
      refine' h _ 
      byCases' a ∈ s
      ·
        simpRw [Set.mulIndicator, if_pos h]
        exact hmem h
      ·
        simpRw [Set.mulIndicator, if_neg h]
    ·
      simpRw [Set.mulIndicator, if_pos h.1]
      exact h.2

@[simp, toAdditive]
theorem mul_support_mul_indicator : Function.MulSupport (s.mul_indicator f) = s ∩ Function.MulSupport f :=
  ext$
    fun x =>
      by 
        simp [Function.mem_mul_support, mul_indicator_apply_eq_one]

/-- If a multiplicative indicator function is not equal to one at a point, then that
point is in the set. -/
@[toAdditive]
theorem mem_of_mul_indicator_ne_one (h : mul_indicator s f a ≠ 1) : a ∈ s :=
  not_imp_comm.1 (fun hn => mul_indicator_of_not_mem hn f) h

@[toAdditive]
theorem eq_on_mul_indicator : eq_on (mul_indicator s f) f s :=
  fun x hx => mul_indicator_of_mem hx f

@[toAdditive]
theorem mul_support_mul_indicator_subset : mul_support (s.mul_indicator f) ⊆ s :=
  fun x hx => hx.imp_symm fun h => mul_indicator_of_not_mem h f

@[simp, toAdditive]
theorem mul_indicator_mul_support : mul_indicator (mul_support f) f = f :=
  mul_indicator_eq_self.2 subset.rfl

@[simp, toAdditive]
theorem mul_indicator_range_comp {ι : Sort _} (f : ι → α) (g : α → M) : mul_indicator (range f) g ∘ f = g ∘ f :=
  piecewise_range_comp _ _ _

@[toAdditive]
theorem mul_indicator_congr (h : eq_on f g s) : mul_indicator s f = mul_indicator s g :=
  funext$
    fun x =>
      by 
        simp only [mul_indicator]
        splitIfs
        ·
          exact h h_1 
        rfl

@[simp, toAdditive]
theorem mul_indicator_univ (f : α → M) : mul_indicator (univ : Set α) f = f :=
  mul_indicator_eq_self.2$ subset_univ _

@[simp, toAdditive]
theorem mul_indicator_empty (f : α → M) : mul_indicator (∅ : Set α) f = fun a => 1 :=
  mul_indicator_eq_one.2$ disjoint_empty _

@[toAdditive]
theorem mul_indicator_empty' (f : α → M) : mul_indicator (∅ : Set α) f = 1 :=
  mul_indicator_empty f

variable(M)

@[simp, toAdditive]
theorem mul_indicator_one (s : Set α) : (mul_indicator s fun x => (1 : M)) = fun x => (1 : M) :=
  mul_indicator_eq_one.2$
    by 
      simp only [mul_support_one, empty_disjoint]

@[simp, toAdditive]
theorem mul_indicator_one' {s : Set α} : s.mul_indicator (1 : α → M) = 1 :=
  mul_indicator_one M s

variable{M}

-- error in Algebra.IndicatorFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem mul_indicator_mul_indicator
(s t : set α)
(f : α → M) : «expr = »(mul_indicator s (mul_indicator t f), mul_indicator «expr ∩ »(s, t) f) :=
«expr $ »(funext, λ x, by { simp [] [] ["only"] ["[", expr mul_indicator, "]"] [] [],
   split_ifs [] [],
   repeat { simp [] [] [] ["*"] [] ["at", "*"] { contextual := tt } } })

@[simp, toAdditive]
theorem mul_indicator_inter_mul_support (s : Set α) (f : α → M) :
  mul_indicator (s ∩ mul_support f) f = mul_indicator s f :=
  by 
    rw [←mul_indicator_mul_indicator, mul_indicator_mul_support]

@[toAdditive]
theorem comp_mul_indicator (h : M → β) (f : α → M) {s : Set α} {x : α} :
  h (s.mul_indicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x :=
  s.apply_piecewise _ _ fun _ => h

@[toAdditive]
theorem mul_indicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
  mul_indicator (f ⁻¹' s) (g ∘ f) x = mul_indicator s g (f x) :=
  by 
    simp only [mul_indicator]
    splitIfs <;> rfl

@[toAdditive]
theorem mul_indicator_comp_of_one {g : M → N} (hg : g 1 = 1) : mul_indicator s (g ∘ f) = g ∘ mul_indicator s f :=
  by 
    funext 
    simp only [mul_indicator]
    splitIfs <;> simp 

@[toAdditive]
theorem comp_mul_indicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
  (fun x => f (s.mul_indicator (fun x => c) x)) = s.mul_indicator fun x => f c :=
  (mul_indicator_comp_of_one hf).symm

@[toAdditive]
theorem mul_indicator_preimage (s : Set α) (f : α → M) (B : Set M) :
  mul_indicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) :=
  piecewise_preimage s f 1 B

@[toAdditive]
theorem mul_indicator_preimage_of_not_mem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
  mul_indicator s f ⁻¹' t = f ⁻¹' t ∩ s :=
  by 
    simp [mul_indicator_preimage, Pi.one_def, Set.preimage_const_of_not_mem ht]

@[toAdditive]
theorem mem_range_mul_indicator {r : M} {s : Set α} {f : α → M} :
  r ∈ range (mul_indicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s :=
  by 
    simp [mul_indicator, ite_eq_iff, exists_or_distrib, eq_univ_iff_forall, and_comm, or_comm, @eq_comm _ r 1]

@[toAdditive]
theorem mul_indicator_rel_mul_indicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
  r (mul_indicator s f a) (mul_indicator s g a) :=
  by 
    simp only [mul_indicator]
    splitIfs with has has 
    exacts[ha has, h1]

end HasOne

section Monoidₓ

variable[MulOneClass M]{s t : Set α}{f g : α → M}{a : α}

@[toAdditive]
theorem mul_indicator_union_mul_inter_apply (f : α → M) (s t : Set α) (a : α) :
  (mul_indicator (s ∪ t) f a*mul_indicator (s ∩ t) f a) = mul_indicator s f a*mul_indicator t f a :=
  by 
    byCases' hs : a ∈ s <;> byCases' ht : a ∈ t <;> simp 

@[toAdditive]
theorem mul_indicator_union_mul_inter (f : α → M) (s t : Set α) :
  (mul_indicator (s ∪ t) f*mul_indicator (s ∩ t) f) = mul_indicator s f*mul_indicator t f :=
  funext$ mul_indicator_union_mul_inter_apply f s t

@[toAdditive]
theorem mul_indicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → M) :
  mul_indicator (s ∪ t) f a = mul_indicator s f a*mul_indicator t f a :=
  by 
    rw [←mul_indicator_union_mul_inter_apply f s t, mul_indicator_of_not_mem h, mul_oneₓ]

@[toAdditive]
theorem mul_indicator_union_of_disjoint (h : Disjoint s t) (f : α → M) :
  mul_indicator (s ∪ t) f = fun a => mul_indicator s f a*mul_indicator t f a :=
  funext$ fun a => mul_indicator_union_of_not_mem_inter (fun ha => h ha) _

@[toAdditive]
theorem mul_indicator_mul (s : Set α) (f g : α → M) :
  (mul_indicator s fun a => f a*g a) = fun a => mul_indicator s f a*mul_indicator s g a :=
  by 
    funext 
    simp only [mul_indicator]
    splitIfs
    ·
      rfl 
    rw [mul_oneₓ]

@[simp, toAdditive]
theorem mul_indicator_compl_mul_self_apply (s : Set α) (f : α → M) (a : α) :
  (mul_indicator («expr ᶜ» s) f a*mul_indicator s f a) = f a :=
  Classical.by_cases
    (fun ha : a ∈ s =>
      by 
        simp [ha])
    fun ha =>
      by 
        simp [ha]

@[simp, toAdditive]
theorem mul_indicator_compl_mul_self (s : Set α) (f : α → M) : (mul_indicator («expr ᶜ» s) f*mul_indicator s f) = f :=
  funext$ mul_indicator_compl_mul_self_apply s f

@[simp, toAdditive]
theorem mul_indicator_self_mul_compl_apply (s : Set α) (f : α → M) (a : α) :
  (mul_indicator s f a*mul_indicator («expr ᶜ» s) f a) = f a :=
  Classical.by_cases
    (fun ha : a ∈ s =>
      by 
        simp [ha])
    fun ha =>
      by 
        simp [ha]

@[simp, toAdditive]
theorem mul_indicator_self_mul_compl (s : Set α) (f : α → M) : (mul_indicator s f*mul_indicator («expr ᶜ» s) f) = f :=
  funext$ mul_indicator_self_mul_compl_apply s f

-- error in Algebra.IndicatorFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem mul_indicator_mul_eq_left
{f g : α → M}
(h : disjoint (mul_support f) (mul_support g)) : «expr = »((mul_support f).mul_indicator «expr * »(f, g), f) :=
begin
  refine [expr «expr $ »(mul_indicator_congr, λ x hx, _).trans mul_indicator_mul_support],
  have [] [":", expr «expr = »(g x, 1)] [],
  from [expr nmem_mul_support.1 (disjoint_left.1 h hx)],
  rw ["[", expr pi.mul_apply, ",", expr this, ",", expr mul_one, "]"] []
end

-- error in Algebra.IndicatorFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem mul_indicator_mul_eq_right
{f g : α → M}
(h : disjoint (mul_support f) (mul_support g)) : «expr = »((mul_support g).mul_indicator «expr * »(f, g), g) :=
begin
  refine [expr «expr $ »(mul_indicator_congr, λ x hx, _).trans mul_indicator_mul_support],
  have [] [":", expr «expr = »(f x, 1)] [],
  from [expr nmem_mul_support.1 (disjoint_right.1 h hx)],
  rw ["[", expr pi.mul_apply, ",", expr this, ",", expr one_mul, "]"] []
end

/-- `set.mul_indicator` as a `monoid_hom`. -/
@[toAdditive "`set.indicator` as an `add_monoid_hom`."]
def mul_indicator_hom {α} M [MulOneClass M] (s : Set α) : (α → M) →* α → M :=
  { toFun := mul_indicator s, map_one' := mul_indicator_one M s, map_mul' := mul_indicator_mul s }

end Monoidₓ

section DistribMulAction

variable{A : Type _}[AddMonoidₓ A][Monoidₓ M][DistribMulAction M A]

theorem indicator_smul_apply (s : Set α) (r : M) (f : α → A) (x : α) :
  indicator s (fun x => r • f x) x = r • indicator s f x :=
  by 
    dunfold indicator 
    splitIfs 
    exacts[rfl, (smul_zero r).symm]

theorem indicator_smul (s : Set α) (r : M) (f : α → A) :
  (indicator s fun x : α => r • f x) = fun x : α => r • indicator s f x :=
  funext$ indicator_smul_apply s r f

end DistribMulAction

section Groupₓ

variable{G : Type _}[Groupₓ G]{s t : Set α}{f g : α → G}{a : α}

@[toAdditive]
theorem mul_indicator_inv' (s : Set α) (f : α → G) : mul_indicator s (f⁻¹) = mul_indicator s f⁻¹ :=
  (mul_indicator_hom G s).map_inv f

@[toAdditive]
theorem mul_indicator_inv (s : Set α) (f : α → G) : (mul_indicator s fun a => f a⁻¹) = fun a => mul_indicator s f a⁻¹ :=
  mul_indicator_inv' s f

theorem indicator_sub {G} [AddGroupₓ G] (s : Set α) (f g : α → G) :
  (indicator s fun a => f a - g a) = fun a => indicator s f a - indicator s g a :=
  (indicator_hom G s).map_sub f g

@[toAdditive indicator_compl']
theorem mul_indicator_compl (s : Set α) (f : α → G) : mul_indicator («expr ᶜ» s) f = f*mul_indicator s f⁻¹ :=
  eq_mul_inv_of_mul_eq$ s.mul_indicator_compl_mul_self f

theorem indicator_compl {G} [AddGroupₓ G] (s : Set α) (f : α → G) : indicator («expr ᶜ» s) f = f - indicator s f :=
  by 
    rw [sub_eq_add_neg, indicator_compl']

@[toAdditive indicator_diff']
theorem mul_indicator_diff (h : s ⊆ t) (f : α → G) : mul_indicator (t \ s) f = mul_indicator t f*mul_indicator s f⁻¹ :=
  eq_mul_inv_of_mul_eq$
    by 
      rw [Pi.mul_def, ←mul_indicator_union_of_disjoint disjoint_diff.symm f, diff_union_self,
        union_eq_self_of_subset_right h]

theorem indicator_diff {G : Type _} [AddGroupₓ G] {s t : Set α} (h : s ⊆ t) (f : α → G) :
  indicator (t \ s) f = indicator t f - indicator s f :=
  by 
    rw [indicator_diff' h, sub_eq_add_neg]

end Groupₓ

section CommMonoidₓ

variable[CommMonoidₓ M]

/-- Consider a product of `g i (f i)` over a `finset`.  Suppose `g` is a
function such as `pow`, which maps a second argument of `1` to
`1`. Then if `f` is replaced by the corresponding multiplicative indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
@[toAdditive]
theorem prod_mul_indicator_subset_of_eq_one [HasOne N] (f : α → N) (g : α → N → M) {s t : Finset α} (h : s ⊆ t)
  (hg : ∀ a, g a 1 = 1) : (∏i in s, g i (f i)) = ∏i in t, g i (mul_indicator («expr↑ » s) f i) :=
  by 
    rw [←Finset.prod_subset h _]
    ·
      apply Finset.prod_congr rfl 
      intro i hi 
      congr 
      symm 
      exact mul_indicator_of_mem hi _
    ·
      refine' fun i hi hn => _ 
      convert hg i 
      exact mul_indicator_of_not_mem hn _

/-- Consider a sum of `g i (f i)` over a `finset`.  Suppose `g` is a
function such as multiplication, which maps a second argument of 0 to
0.  (A typical use case would be a weighted sum of `f i * h i` or `f i
• h i`, where `f` gives the weights that are multiplied by some other
function `h`.)  Then if `f` is replaced by the corresponding indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
add_decl_doc Set.sum_indicator_subset_of_eq_zero

@[toAdditive]
theorem prod_mul_indicator_subset (f : α → M) {s t : Finset α} (h : s ⊆ t) :
  (∏i in s, f i) = ∏i in t, mul_indicator («expr↑ » s) f i :=
  prod_mul_indicator_subset_of_eq_one _ (fun a b => b) h fun _ => rfl

/-- Summing an indicator function over a possibly larger `finset` is
the same as summing the original function over the original
`finset`. -/
add_decl_doc sum_indicator_subset

@[toAdditive]
theorem _root_.finset.prod_mul_indicator_eq_prod_filter (s : Finset ι) (f : ι → α → M) (t : ι → Set α) (g : ι → α) :
  (∏i in s, mul_indicator (t i) (f i) (g i)) = ∏i in s.filter fun i => g i ∈ t i, f i (g i) :=
  by 
    refine' (Finset.prod_filter_mul_prod_filter_not s (fun i => g i ∈ t i) _).symm.trans _ 
    refine' Eq.trans _ (mul_oneₓ _)
    exact
      congr_arg2 (·*·) (Finset.prod_congr rfl$ fun x hx => mul_indicator_of_mem (Finset.mem_filter.1 hx).2 _)
        (Finset.prod_eq_one$ fun x hx => mul_indicator_of_not_mem (Finset.mem_filter.1 hx).2 _)

@[toAdditive]
theorem mul_indicator_finset_prod (I : Finset ι) (s : Set α) (f : ι → α → M) :
  mul_indicator s (∏i in I, f i) = ∏i in I, mul_indicator s (f i) :=
  (mul_indicator_hom M s).map_prod _ _

@[toAdditive]
theorem mul_indicator_finset_bUnion {ι} (I : Finset ι) (s : ι → Set α) {f : α → M} :
  (∀ i _ : i ∈ I j _ : j ∈ I, i ≠ j → Disjoint (s i) (s j)) →
    mul_indicator (⋃(i : _)(_ : i ∈ I), s i) f = fun a => ∏i in I, mul_indicator (s i) f a :=
  by 
    refine' Finset.induction_on I _ _
    ·
      intro h 
      funext 
      simp 
    intro a I haI ih hI 
    funext 
    rw [Finset.prod_insert haI, Finset.set_bUnion_insert, mul_indicator_union_of_not_mem_inter, ih _]
    ·
      intro i hi j hj hij 
      exact hI i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij 
    simp only [not_exists, exists_prop, mem_Union, mem_inter_eq, not_and]
    intro hx a' ha' 
    refine' disjoint_left.1 (hI a (Finset.mem_insert_self _ _) a' (Finset.mem_insert_of_mem ha') _) hx 
    exact (ne_of_mem_of_not_mem ha' haI).symm

end CommMonoidₓ

section MulZeroClass

variable[MulZeroClass M]{s t : Set α}{f g : α → M}{a : α}

theorem indicator_mul (s : Set α) (f g : α → M) :
  (indicator s fun a => f a*g a) = fun a => indicator s f a*indicator s g a :=
  by 
    funext 
    simp only [indicator]
    splitIfs
    ·
      rfl 
    rw [mul_zero]

theorem indicator_mul_left (s : Set α) (f g : α → M) : indicator s (fun a => f a*g a) a = indicator s f a*g a :=
  by 
    simp only [indicator]
    splitIfs
    ·
      rfl 
    rw [zero_mul]

theorem indicator_mul_right (s : Set α) (f g : α → M) : indicator s (fun a => f a*g a) a = f a*indicator s g a :=
  by 
    simp only [indicator]
    splitIfs
    ·
      rfl 
    rw [mul_zero]

theorem inter_indicator_mul {t1 t2 : Set α} (f g : α → M) (x : α) :
  (t1 ∩ t2).indicator (fun x => f x*g x) x = t1.indicator f x*t2.indicator g x :=
  by 
    rw [←Set.indicator_indicator]
    simp [indicator]

end MulZeroClass

section MonoidWithZeroₓ

variable[MonoidWithZeroₓ M]

theorem indicator_prod_one {s : Set α} {t : Set β} {x : α} {y : β} :
  (s.prod t).indicator (1 : _ → M) (x, y) = s.indicator 1 x*t.indicator 1 y :=
  by 
    simp [indicator, ←ite_and]

end MonoidWithZeroₓ

section Order

variable[HasOne M][Preorderₓ M]{s t : Set α}{f g : α → M}{a : α}{y : M}

@[toAdditive]
theorem mul_indicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) : mul_indicator s f a ≤ y :=
  if ha : a ∈ s then
    by 
      simpa [ha] using hfg ha
  else
    by 
      simpa [ha] using hg ha

@[toAdditive]
theorem mul_indicator_le' (hfg : ∀ a _ : a ∈ s, f a ≤ g a) (hg : ∀ a _ : a ∉ s, 1 ≤ g a) : mul_indicator s f ≤ g :=
  fun a => mul_indicator_apply_le' (hfg _) (hg _)

@[toAdditive]
theorem le_mul_indicator_apply {y} (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) : y ≤ mul_indicator s g a :=
  @mul_indicator_apply_le' α (OrderDual M) ‹_› _ _ _ _ _ hfg hf

@[toAdditive]
theorem le_mul_indicator (hfg : ∀ a _ : a ∈ s, f a ≤ g a) (hf : ∀ a _ : a ∉ s, f a ≤ 1) : f ≤ mul_indicator s g :=
  fun a => le_mul_indicator_apply (hfg _) (hf _)

@[toAdditive indicator_apply_nonneg]
theorem one_le_mul_indicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mul_indicator s f a :=
  le_mul_indicator_apply h fun _ => le_rfl

@[toAdditive indicator_nonneg]
theorem one_le_mul_indicator (h : ∀ a _ : a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mul_indicator s f a :=
  one_le_mul_indicator_apply (h a)

@[toAdditive]
theorem mul_indicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mul_indicator s f a ≤ 1 :=
  mul_indicator_apply_le' h fun _ => le_rfl

@[toAdditive]
theorem mul_indicator_le_one (h : ∀ a _ : a ∈ s, f a ≤ 1) (a : α) : mul_indicator s f a ≤ 1 :=
  mul_indicator_apply_le_one (h a)

@[toAdditive]
theorem mul_indicator_le_mul_indicator (h : f a ≤ g a) : mul_indicator s f a ≤ mul_indicator s g a :=
  mul_indicator_rel_mul_indicator (le_reflₓ _) fun _ => h

attribute [mono] mul_indicator_le_mul_indicator indicator_le_indicator

@[toAdditive]
theorem mul_indicator_le_mul_indicator_of_subset (h : s ⊆ t) (hf : ∀ a, 1 ≤ f a) (a : α) :
  mul_indicator s f a ≤ mul_indicator t f a :=
  mul_indicator_apply_le' (fun ha => le_mul_indicator_apply (fun _ => le_rfl) fun hat => (hat$ h ha).elim)
    fun ha => one_le_mul_indicator_apply fun _ => hf _

@[toAdditive]
theorem mul_indicator_le_self' (hf : ∀ x _ : x ∉ s, 1 ≤ f x) : mul_indicator s f ≤ f :=
  mul_indicator_le' (fun _ _ => le_reflₓ _) hf

@[toAdditive]
theorem mul_indicator_Union_apply {ι M} [CompleteLattice M] [HasOne M] (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M)
  (x : α) : mul_indicator (⋃i, s i) f x = ⨆i, mul_indicator (s i) f x :=
  by 
    byCases' hx : x ∈ ⋃i, s i
    ·
      rw [mul_indicator_of_mem hx]
      rw [mem_Union] at hx 
      refine' le_antisymmₓ _ (supr_le$ fun i => mul_indicator_le_self' (fun x hx => h1 ▸ bot_le) x)
      rcases hx with ⟨i, hi⟩
      exact le_supr_of_le i (ge_of_eq$ mul_indicator_of_mem hi _)
    ·
      rw [mul_indicator_of_not_mem hx]
      simp only [mem_Union, not_exists] at hx 
      simp [hx, ←h1]

end Order

section CanonicallyOrderedMonoid

variable[CanonicallyOrderedMonoid M]

@[toAdditive]
theorem mul_indicator_le_self (s : Set α) (f : α → M) : mul_indicator s f ≤ f :=
  mul_indicator_le_self'$ fun _ _ => one_le _

@[toAdditive]
theorem mul_indicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
  mul_indicator s f a ≤ g a :=
  mul_indicator_apply_le' hfg$ fun _ => one_le _

@[toAdditive]
theorem mul_indicator_le {s : Set α} {f g : α → M} (hfg : ∀ a _ : a ∈ s, f a ≤ g a) : mul_indicator s f ≤ g :=
  mul_indicator_le' hfg$ fun _ _ => one_le _

end CanonicallyOrderedMonoid

theorem indicator_le_indicator_nonneg {β} [LinearOrderₓ β] [HasZero β] (s : Set α) (f : α → β) :
  s.indicator f ≤ { x | 0 ≤ f x }.indicator f :=
  by 
    intro x 
    simpRw [indicator_apply]
    splitIfs
    ·
      exact le_rfl
    ·
      exact (not_le.mp h_1).le
    ·
      exact h_1
    ·
      exact le_rfl

theorem indicator_nonpos_le_indicator {β} [LinearOrderₓ β] [HasZero β] (s : Set α) (f : α → β) :
  { x | f x ≤ 0 }.indicator f ≤ s.indicator f :=
  @indicator_le_indicator_nonneg α (OrderDual β) _ _ s f

end Set

@[toAdditive]
theorem MonoidHom.map_mul_indicator {M N : Type _} [Monoidₓ M] [Monoidₓ N] (f : M →* N) (s : Set α) (g : α → M)
  (x : α) : f (s.mul_indicator g x) = s.mul_indicator (f ∘ g) x :=
  congr_funₓ (Set.mul_indicator_comp_of_one f.map_one).symm x

