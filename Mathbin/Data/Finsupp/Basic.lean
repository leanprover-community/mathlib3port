import Mathbin.Data.Finset.Preimage 
import Mathbin.Algebra.IndicatorFunction 
import Mathbin.Algebra.GroupActionHom

/-!
# Type of functions with finite support

For any type `α` and a type `M` with zero, we define the type `finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `monoid_algebra R M` and `add_monoid_algebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `add_monoid_algebra`s, hence they use
  `finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `linear_independent`) is defined as a map
  `finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `multiset α ≃+ α →₀ ℕ`;
* `free_abelian_group α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `finsupp` elements.

Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `monoid_algebra`, `add_monoid_algebra`, and types based on these two have
non-pointwise multiplication.

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`. We also use the following convention
for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## TODO

* This file is currently ~2K lines long, so possibly it should be splitted into smaller chunks;

* Add the list of definitions and important lemmas to the module docstring.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## Notation

This file defines `α →₀ β` as notation for `finsupp α β`.

-/


noncomputable theory

open_locale Classical BigOperators

open Finset

variable {α β γ ι M M' N P G H R S : Type _}

/-- `finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure Finsupp (α : Type _) (M : Type _) [HasZero M] where 
  Support : Finset α 
  toFun : α → M 
  mem_support_to_fun : ∀ a, a ∈ support ↔ to_fun a ≠ 0

infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `finsupp` -/


section Basic

variable [HasZero M]

instance : CoeFun (α →₀ M) fun _ => α → M :=
  ⟨to_fun⟩

@[simp]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) : «expr⇑ » (⟨s, f, h⟩ : α →₀ M) = f :=
  rfl

instance : HasZero (α →₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨False.elim, fun H => H rfl⟩⟩⟩

@[simp]
theorem coe_zero : «expr⇑ » (0 : α →₀ M) = 0 :=
  rfl

theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl

@[simp]
theorem support_zero : (0 : α →₀ M).Support = ∅ :=
  rfl

instance : Inhabited (α →₀ M) :=
  ⟨0⟩

@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 :=
  f.mem_support_to_fun

@[simp, normCast]
theorem fun_support_eq (f : α →₀ M) : Function.Support f = f.support :=
  Set.ext$ fun x => mem_support_iff.symm

theorem not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_fn_injective : @function.injective «expr →₀ »(α, M) (α → M) coe_fn
| ⟨s, f, hf⟩, ⟨t, g, hg⟩, h := begin
  change [expr «expr = »(f, g)] [] ["at", ident h],
  subst [expr h],
  have [] [":", expr «expr = »(s, t)] [],
  { ext [] [ident a] [],
    exact [expr (hf a).trans (hg a).symm] },
  subst [expr this]
end

@[simp, normCast]
theorem coe_fn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g :=
  coe_fn_injective.eq_iff

@[simp, normCast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 :=
  by 
    rw [←coe_zero, coe_fn_inj]

@[ext]
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  coe_fn_injective (funext h)

theorem ext_iff {f g : α →₀ M} : f = g ↔ ∀ a : α, f a = g a :=
  ⟨by 
      rintro rfl a <;> rfl,
    ext⟩

theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x _ : x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩,
    fun ⟨h₁, h₂⟩ =>
      ext$
        fun a =>
          if h : a ∈ f.support then h₂ a h else
            have hf : f a = 0 := not_mem_support_iff.1 h 
            have hg : g a = 0 :=
              by 
                rwa [h₁, not_mem_support_iff] at h 
            by 
              rw [hf, hg]⟩

theorem congr_funₓ {f g : α →₀ M} (h : f = g) (a : α) : f a = g a :=
  congr_funₓ (congr_argₓ Finsupp.toFun h) a

@[simp]
theorem support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 :=
  by 
    exactModCast @Function.support_eq_empty_iff _ _ _ f

theorem support_nonempty_iff {f : α →₀ M} : f.support.nonempty ↔ f ≠ 0 :=
  by 
    simp only [Finsupp.support_eq_empty, Finset.nonempty_iff_ne_empty, Ne.def]

theorem nonzero_iff_exists {f : α →₀ M} : f ≠ 0 ↔ ∃ a : α, f a ≠ 0 :=
  by 
    simp [←Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_not_mem]

theorem card_support_eq_zero {f : α →₀ M} : card f.support = 0 ↔ f = 0 :=
  by 
    simp 

instance [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) :=
  fun f g => decidableOfIff (f.support = g.support ∧ ∀ a _ : a ∈ f.support, f a = g a) ext_iff'.symm

theorem finite_support (f : α →₀ M) : Set.Finite (Function.Support f) :=
  f.fun_support_eq.symm ▸ f.support.finite_to_set

theorem support_subset_iff {s : Set α} {f : α →₀ M} : «expr↑ » f.support ⊆ s ↔ ∀ a _ : a ∉ s, f a = 0 :=
  by 
    simp only [Set.subset_def, mem_coe, mem_support_iff] <;> exact forall_congrₓ fun a => not_imp_comm

/-- Given `fintype α`, `equiv_fun_on_fintype` is the `equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equiv_fun_on_fintype [Fintype α] : (α →₀ M) ≃ (α → M) :=
  ⟨fun f a => f a,
    fun f =>
      mk (Finset.univ.filter$ fun a => f a ≠ 0) f
        (by 
          simp only [true_andₓ, Finset.mem_univ, iff_selfₓ, Finset.mem_filter, Finset.filter_congr_decidable,
            forall_true_iff]),
    by 
      intro f 
      ext a 
      rfl,
    by 
      intro f 
      ext a 
      rfl⟩

@[simp]
theorem equiv_fun_on_fintype_symm_coe {α} [Fintype α] (f : α →₀ M) : equiv_fun_on_fintype.symm f = f :=
  by 
    ext 
    simp [equiv_fun_on_fintype]

end Basic

/-! ### Declarations about `single` -/


section Single

variable [HasZero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function which has
  value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M :=
  ⟨if b = 0 then ∅ else {a}, fun a' => if a = a' then b else 0,
    fun a' =>
      by 
        byCases' hb : b = 0 <;> byCases' a = a' <;> simp only [hb, h, if_pos, if_false, mem_singleton]
        ·
          exact ⟨False.elim, fun H => H rfl⟩
        ·
          exact ⟨False.elim, fun H => H rfl⟩
        ·
          exact ⟨fun _ => hb, fun _ => rfl⟩
        ·
          exact ⟨fun H _ => h H.symm, fun H => (H rfl).elim⟩⟩

theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 :=
  by 
    convert rfl

theorem single_eq_indicator : «expr⇑ » (single a b) = Set.indicator {a} fun _ => b :=
  by 
    ext 
    simp [single_apply, Set.indicator, @eq_comm _ a]

@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b :=
  if_pos rfl

@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 :=
  if_neg h

theorem single_eq_update : «expr⇑ » (single a b) = Function.update 0 a b :=
  by 
    rw [single_eq_indicator, ←Set.piecewise_eq_indicator, Set.piecewise_singleton]

theorem single_eq_pi_single : «expr⇑ » (single a b) = Pi.single a b :=
  single_eq_update

@[simp]
theorem single_zero : (single a 0 : α →₀ M) = 0 :=
  coe_fn_injective$
    by 
      simpa only [single_eq_update, coe_zero] using Function.update_eq_self a (0 : α → M)

theorem single_of_single_apply (a a' : α) (b : M) : single a ((single a' b) a) = single a' (single a' b) a :=
  by 
    rw [single_apply, single_apply]
    ext 
    splitIfs
    ·
      rw [h]
    ·
      rw [zero_apply, single_apply, if_t_t]

theorem support_single_ne_zero (hb : b ≠ 0) : (single a b).Support = {a} :=
  if_neg hb

theorem support_single_subset : (single a b).Support ⊆ {a} :=
  show ite _ _ _ ⊆ _ by 
    splitIfs <;> [exact empty_subset _, exact subset.refl _]

theorem single_apply_mem x : single a b x ∈ ({0, b} : Set M) :=
  by 
    rcases em (a = x) with (rfl | hx) <;> [simp , simp [single_eq_of_ne hx]]

theorem range_single_subset : Set.Range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) :=
  fun b₁ b₂ eq =>
    have  : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a :=
      by 
        rw [Eq]
    by 
      rwa [single_eq_same, single_eq_same] at this

theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 :=
  by 
    simp [single_eq_indicator]

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).Support ↔ a = a' ∧ b ≠ 0 :=
  by 
    simp [single_apply_eq_zero, not_or_distrib]

theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b :=
  by 
    refine' ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩
    rintro ⟨h, rfl⟩
    ext x 
    byCases' hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne.def, not_false_iff]
    exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem single_eq_single_iff
(a₁ a₂ : α)
(b₁
 b₂ : M) : «expr ↔ »(«expr = »(single a₁ b₁, single a₂ b₂), «expr ∨ »(«expr ∧ »(«expr = »(a₁, a₂), «expr = »(b₁, b₂)), «expr ∧ »(«expr = »(b₁, 0), «expr = »(b₂, 0)))) :=
begin
  split,
  { assume [binders (eq)],
    by_cases [expr «expr = »(a₁, a₂)],
    { refine [expr or.inl ⟨h, _⟩],
      rwa ["[", expr h, ",", expr (single_injective a₂).eq_iff, "]"] ["at", ident eq] },
    { rw ["[", expr ext_iff, "]"] ["at", ident eq],
      have [ident h₁] [] [":=", expr eq a₁],
      have [ident h₂] [] [":=", expr eq a₂],
      simp [] [] ["only"] ["[", expr single_eq_same, ",", expr single_eq_of_ne h, ",", expr single_eq_of_ne (ne.symm h), "]"] [] ["at", ident h₁, ident h₂],
      exact [expr or.inr ⟨h₁, h₂.symm⟩] } },
  { rintros ["(", "⟨", ident rfl, ",", ident rfl, "⟩", "|", "⟨", ident rfl, ",", ident rfl, "⟩", ")"],
    { refl },
    { rw ["[", expr single_zero, ",", expr single_zero, "]"] [] } }
end

/-- `finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b :=
  fun a a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right$ fun hb => h hb.1).left

theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem support_single_ne_bot (i : α) (h : «expr ≠ »(b, 0)) : «expr ≠ »((single i b).support, «expr⊥»()) :=
begin
  have [] [":", expr «expr ∈ »(i, (single i b).support)] [":=", expr by simpa [] [] [] [] [] ["using", expr h]],
  intro [ident H],
  simpa [] [] [] ["[", expr H, "]"] [] []
end

theorem support_single_disjoint {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
  Disjoint (single i b).Support (single j b').Support ↔ i ≠ j :=
  by 
    rw [support_single_ne_zero hb, support_single_ne_zero hb', disjoint_singleton]

@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 :=
  by 
    simp [ext_iff, single_eq_indicator]

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ :=
  by 
    simp only [single_apply] <;> acRfl

instance [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) :=
  by 
    inhabit α 
    rcases exists_ne (0 : M) with ⟨x, hx⟩
    exact nontrivial_of_ne (single (default α) x) 0 (mt single_eq_zero.1 hx)

theorem unique_single [Unique α] (x : α →₀ M) : x = single (default α) (x (default α)) :=
  ext$ Unique.forall_iff.2 single_eq_same.symm

theorem unique_ext [Unique α] {f g : α →₀ M} (h : f (default α) = g (default α)) : f = g :=
  ext$
    fun a =>
      by 
        rwa [Unique.eq_default a]

theorem unique_ext_iff [Unique α] {f g : α →₀ M} : f = g ↔ f (default α) = g (default α) :=
  ⟨fun h => h ▸ rfl, unique_ext⟩

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' :=
  by 
    rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]

theorem support_eq_singleton {f : α →₀ M} {a : α} : f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h => ⟨mem_support_iff.1$ h.symm ▸ Finset.mem_singleton_self a, eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_zero h.1⟩

theorem support_eq_singleton' {f : α →₀ M} {a : α} : f.support = {a} ↔ ∃ (b : _)(_ : b ≠ 0), f = single a b :=
  ⟨fun h =>
      let h := support_eq_singleton.1 h
      ⟨_, h.1, h.2⟩,
    fun ⟨b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero hb⟩

theorem card_support_eq_one {f : α →₀ M} : card f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) :=
  by 
    simp only [card_eq_one, support_eq_singleton]

theorem card_support_eq_one' {f : α →₀ M} : card f.support = 1 ↔ ∃ (a : _)(b : _)(_ : b ≠ 0), f = single a b :=
  by 
    simp only [card_eq_one, support_eq_singleton']

theorem support_subset_singleton {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩,
    fun ⟨b, hb⟩ =>
      by 
        rw [hb, support_subset_singleton, single_eq_same]⟩

theorem card_support_le_one [Nonempty α] {f : α →₀ M} : card f.support ≤ 1 ↔ ∃ a, f = single a (f a) :=
  by 
    simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

theorem card_support_le_one' [Nonempty α] {f : α →₀ M} : card f.support ≤ 1 ↔ ∃ a b, f = single a b :=
  by 
    simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

@[simp]
theorem equiv_fun_on_fintype_single [Fintype α] (x : α) (m : M) :
  (@Finsupp.equivFunOnFintype α M _ _) (Finsupp.single x m) = Pi.single x m :=
  by 
    ext 
    simp [Finsupp.single_eq_pi_single, Finsupp.equivFunOnFintype]

@[simp]
theorem equiv_fun_on_fintype_symm_single [Fintype α] (x : α) (m : M) :
  (@Finsupp.equivFunOnFintype α M _ _).symm (Pi.single x m) = Finsupp.single x m :=
  by 
    ext 
    simp [Finsupp.single_eq_pi_single, Finsupp.equivFunOnFintype]

end Single

/-! ### Declarations about `update` -/


section Update

variable [HasZero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `finsupp.support`.
Otherwise, if `a` was not in the `finsupp.support`, it is added to it.

This is the finitely-supported version of `function.update`. -/
def update : α →₀ M :=
  ⟨if b = 0 then f.support.erase a else insert a f.support, Function.update f a b,
    fun i =>
      by 
        simp only [Function.update_apply, Ne.def]
        splitIfs with hb ha ha hb <;> simp [ha, hb]⟩

@[simp]
theorem coe_update : (f.update a b : α → M) = Function.update f a b :=
  rfl

@[simp]
theorem update_self : f.update a (f a) = f :=
  by 
    ext 
    simp 

theorem support_update : support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support :=
  rfl

@[simp]
theorem support_update_zero : support (f.update a 0) = f.support.erase a :=
  if_pos rfl

variable {b}

theorem support_update_ne_zero (h : b ≠ 0) : support (f.update a b) = insert a f.support :=
  if_neg h

end Update

/-! ### Declarations about `on_finset` -/


section OnFinset

variable [HasZero M]

/-- `on_finset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
  The function needs to be `0` outside of `s`. Use this when the set needs to be filtered anyways,
  otherwise a better set representation is often available. -/
def on_finset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M :=
  ⟨s.filter fun a => f a ≠ 0, f,
    by 
      simpa⟩

@[simp]
theorem on_finset_apply {s : Finset α} {f : α → M} {hf a} : (on_finset s f hf : α →₀ M) a = f a :=
  rfl

@[simp]
theorem support_on_finset_subset {s : Finset α} {f : α → M} {hf} : (on_finset s f hf).Support ⊆ s :=
  filter_subset _ _

@[simp]
theorem mem_support_on_finset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) {a : α} :
  a ∈ (Finsupp.onFinset s f hf).Support ↔ f a ≠ 0 :=
  by 
    rw [Finsupp.mem_support_iff, Finsupp.on_finset_apply]

theorem support_on_finset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) :
  (Finsupp.onFinset s f hf).Support = s.filter fun a => f a ≠ 0 :=
  rfl

end OnFinset

section OfSupportFinite

variable [HasZero M]

/-- The natural `finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def of_support_finite (f : α → M) (hf : (Function.Support f).Finite) : α →₀ M :=
  { Support := hf.to_finset, toFun := f, mem_support_to_fun := fun _ => hf.mem_to_finset }

theorem of_support_finite_coe {f : α → M} {hf : (Function.Support f).Finite} : (of_support_finite f hf : α → M) = f :=
  rfl

instance : CanLift (α → M) (α →₀ M) :=
  { coe := coeFn, cond := fun f => (Function.Support f).Finite, prf := fun f hf => ⟨of_support_finite f hf, rfl⟩ }

end OfSupportFinite

/-! ### Declarations about `map_range` -/


section MapRange

variable [HasZero M] [HasZero N] [HasZero P]

/-- The composition of `f : M → N` and `g : α →₀ M` is
`map_range f hf g : α →₀ N`, well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `finsupp.map_range.equiv`
* `finsupp.map_range.zero_hom`
* `finsupp.map_range.add_monoid_hom`
* `finsupp.map_range.add_equiv`
* `finsupp.map_range.linear_map`
* `finsupp.map_range.linear_equiv`
-/
def map_range (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  on_finset g.support (f ∘ g)$
    fun a =>
      by 
        rw [mem_support_iff, not_imp_not] <;> exact fun H => (congr_argₓ f H).trans hf

@[simp]
theorem map_range_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} : map_range f hf g a = f (g a) :=
  rfl

@[simp]
theorem map_range_zero {f : M → N} {hf : f 0 = 0} : map_range f hf (0 : α →₀ M) = 0 :=
  ext$
    fun a =>
      by 
        simp only [hf, zero_apply, map_range_apply]

@[simp]
theorem map_range_id (g : α →₀ M) : map_range id rfl g = g :=
  ext$ fun _ => rfl

theorem map_range_comp (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0) (g : α →₀ M) :
  map_range (f ∘ f₂) h g = map_range f hf (map_range f₂ hf₂ g) :=
  ext$ fun _ => rfl

theorem support_map_range {f : M → N} {hf : f 0 = 0} {g : α →₀ M} : (map_range f hf g).Support ⊆ g.support :=
  support_on_finset_subset

@[simp]
theorem map_range_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} : map_range f hf (single a b) = single a (f b) :=
  ext$
    fun a' =>
      show f (ite _ _ _) = ite _ _ _ by 
        splitIfs <;> [rfl, exact hf]

end MapRange

/-! ### Declarations about `emb_domain` -/


section EmbDomain

variable [HasZero M] [HasZero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `emb_domain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def emb_domain (f : α ↪ β) (v : α →₀ M) : β →₀ M :=
  by 
    refine'
      ⟨v.support.map f, fun a₂ => if h : a₂ ∈ v.support.map f then v (v.support.choose (fun a₁ => f a₁ = a₂) _) else 0,
        _⟩
    ·
      rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
      exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb
    ·
      intro a₂ 
      splitIfs
      ·
        simp only [h, true_iffₓ, Ne.def]
        rw [←not_mem_support_iff, not_not]
        apply Finset.choose_mem
      ·
        simp only [h, Ne.def, ne_self_iff_false]

@[simp]
theorem support_emb_domain (f : α ↪ β) (v : α →₀ M) : (emb_domain f v).Support = v.support.map f :=
  rfl

@[simp]
theorem emb_domain_zero (f : α ↪ β) : (emb_domain f 0 : β →₀ M) = 0 :=
  rfl

@[simp]
theorem emb_domain_apply (f : α ↪ β) (v : α →₀ M) (a : α) : emb_domain f v (f a) = v a :=
  by 
    change dite _ _ _ = _ 
    splitIfs <;> rw [Finset.mem_map' f] at h
    ·
      refine' congr_argₓ (v : α → M) (f.inj' _)
      exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    ·
      exact (not_mem_support_iff.1 h).symm

theorem emb_domain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.Range f) : emb_domain f v a = 0 :=
  by 
    refine' dif_neg (mt (fun h => _) h)
    rcases Finset.mem_map.1 h with ⟨a, h, rfl⟩
    exact Set.mem_range_self a

theorem emb_domain_injective (f : α ↪ β) : Function.Injective (emb_domain f : (α →₀ M) → β →₀ M) :=
  fun l₁ l₂ h =>
    ext$
      fun a =>
        by 
          simpa only [emb_domain_apply] using ext_iff.1 h (f a)

@[simp]
theorem emb_domain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : emb_domain f l₁ = emb_domain f l₂ ↔ l₁ = l₂ :=
  (emb_domain_injective f).eq_iff

@[simp]
theorem emb_domain_eq_zero {f : α ↪ β} {l : α →₀ M} : emb_domain f l = 0 ↔ l = 0 :=
  (emb_domain_injective f).eq_iff'$ emb_domain_zero f

theorem emb_domain_map_range (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
  emb_domain f (map_range g hg p) = map_range g hg (emb_domain f p) :=
  by 
    ext a 
    byCases' a ∈ Set.Range f
    ·
      rcases h with ⟨a', rfl⟩
      rw [map_range_apply, emb_domain_apply, emb_domain_apply, map_range_apply]
    ·
      rw [map_range_apply, emb_domain_notin_range, emb_domain_notin_range, ←hg] <;> assumption

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem single_of_emb_domain_single
(l : «expr →₀ »(α, M))
(f : «expr ↪ »(α, β))
(a : β)
(b : M)
(hb : «expr ≠ »(b, 0))
(h : «expr = »(l.emb_domain f, single a b)) : «expr∃ , »((x), «expr ∧ »(«expr = »(l, single x b), «expr = »(f x, a))) :=
begin
  have [ident h_map_support] [":", expr «expr = »(finset.map f l.support, {a})] [],
  by rw ["[", "<-", expr support_emb_domain, ",", expr h, ",", expr support_single_ne_zero hb, "]"] []; refl,
  have [ident ha] [":", expr «expr ∈ »(a, finset.map f l.support)] [],
  by simp [] [] ["only"] ["[", expr h_map_support, ",", expr finset.mem_singleton, "]"] [] [],
  rcases [expr finset.mem_map.1 ha, "with", "⟨", ident c, ",", ident hc₁, ",", ident hc₂, "⟩"],
  use [expr c],
  split,
  { ext [] [ident d] [],
    rw ["[", "<-", expr emb_domain_apply f l, ",", expr h, "]"] [],
    by_cases [expr h_cases, ":", expr «expr = »(c, d)],
    { simp [] [] ["only"] ["[", expr eq.symm h_cases, ",", expr hc₂, ",", expr single_eq_same, "]"] [] [] },
    { rw ["[", expr single_apply, ",", expr single_apply, ",", expr if_neg, ",", expr if_neg h_cases, "]"] [],
      by_contra [ident hfd],
      exact [expr h_cases (f.injective (hc₂.trans hfd))] } },
  { exact [expr hc₂] }
end

@[simp]
theorem emb_domain_single (f : α ↪ β) (a : α) (m : M) : emb_domain f (single a m) = single (f a) m :=
  by 
    ext b 
    byCases' h : b ∈ Set.Range f
    ·
      rcases h with ⟨a', rfl⟩
      simp [single_apply]
    ·
      simp only [emb_domain_notin_range, h, single_apply, not_false_iff]
      rw [if_neg]
      rintro rfl 
      simpa using h

end EmbDomain

/-! ### Declarations about `zip_with` -/


section ZipWith

variable [HasZero M] [HasZero N] [HasZero P]

/-- `zip_with f hf g₁ g₂` is the finitely supported function satisfying
  `zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, and it is well-defined when `f 0 0 = 0`. -/
def zip_with (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  (on_finset (g₁.support ∪ g₂.support) fun a => f (g₁ a) (g₂ a))$
    fun a H =>
      by 
        simp only [mem_union, mem_support_iff, Ne]
        rw [←not_and_distrib]
        rintro ⟨h₁, h₂⟩
        rw [h₁, h₂] at H 
        exact H hf

@[simp]
theorem zip_with_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
  zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem support_zip_with [D : DecidableEq α] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} :
  (zip_with f hf g₁ g₂).Support ⊆ g₁.support ∪ g₂.support :=
  by 
    rw [Subsingleton.elimₓ D] <;> exact support_on_finset_subset

end ZipWith

/-! ### Declarations about `erase` -/


section Erase

variable [HasZero M]

/-- `erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to
  `0`. -/
def erase (a : α) (f : α →₀ M) : α →₀ M :=
  ⟨f.support.erase a, fun a' => if a' = a then 0 else f a',
    fun a' =>
      by 
        rw [mem_erase, mem_support_iff] <;>
          splitIfs <;> [exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩, exact and_iff_right h]⟩

@[simp]
theorem support_erase {a : α} {f : α →₀ M} : (f.erase a).Support = f.support.erase a :=
  rfl

@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 :=
  if_pos rfl

@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' :=
  if_neg h

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 :=
  by 
    ext s 
    byCases' hs : s = a
    ·
      rw [hs, erase_same]
      rfl
    ·
      rw [erase_ne hs]
      exact single_eq_of_ne (Ne.symm hs)

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b :=
  by 
    ext s 
    byCases' hs : s = a
    ·
      rw [hs, erase_same, single_eq_of_ne h.symm]
    ·
      rw [erase_ne hs]

@[simp]
theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 :=
  by 
    rw [←support_eq_empty, support_erase, support_zero, erase_empty]

end Erase

/-!
### Declarations about `sum` and `prod`

In most of this section, the domain `β` is assumed to be an `add_monoid`.
-/


section SumProd

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[toAdditive "`sum f g` is the sum of `g a (f a)` over the support of `f`. "]
def Prod [HasZero M] [CommMonoidₓ N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏a in f.support, g a (f a)

variable [HasZero M] [HasZero M'] [CommMonoidₓ N]

@[toAdditive]
theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.support ⊆ s) (g : α → M → N)
  (h : ∀ i _ : i ∈ s, g i 0 = 1) : f.prod g = ∏x in s, g x (f x) :=
  Finset.prod_subset hs$ fun x hxs hx => h x hxs ▸ congr_argₓ (g x)$ not_mem_support_iff.1 hx

@[toAdditive]
theorem prod_fintype [Fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) : f.prod g = ∏i, g i (f i) :=
  f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[simp, toAdditive]
theorem prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) : (single a b).Prod h = h a b :=
  calc (single a b).Prod h = ∏x in {a}, h x (single a b x) :=
    prod_of_support_subset _ support_single_subset h$ fun x hx => (mem_singleton.1 hx).symm ▸ h_zero 
    _ = h a b :=
    by 
      simp 
    

@[toAdditive]
theorem prod_map_range_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N} (h0 : ∀ a, h a 0 = 1) :
  (map_range f hf g).Prod h = g.prod fun a b => h a (f b) :=
  Finset.prod_subset support_map_range$
    fun _ _ H =>
      by 
        rw [not_mem_support_iff.1 H, h0]

@[simp, toAdditive]
theorem prod_zero_index {h : α → M → N} : (0 : α →₀ M).Prod h = 1 :=
  rfl

@[toAdditive]
theorem prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
  (f.prod fun x v => g.prod fun x' v' => h x v x' v') = g.prod fun x' v' => f.prod fun x v => h x v x' v' :=
  Finset.prod_comm

@[simp, toAdditive]
theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
  (f.prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 :=
  by 
    dsimp [Finsupp.prod]
    rw [f.support.prod_ite_eq]

@[simp]
theorem sum_ite_self_eq [DecidableEq α] {N : Type _} [AddCommMonoidₓ N] (f : α →₀ N) (a : α) :
  (f.sum fun x v => ite (a = x) v 0) = f a :=
  by 
    convert f.sum_ite_eq a fun x => id 
    simp [ite_eq_right_iff.2 Eq.symm]

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[simp, toAdditive "A restatement of `sum_ite_eq` with the equality test reversed."]
theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
  (f.prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 :=
  by 
    dsimp [Finsupp.prod]
    rw [f.support.prod_ite_eq']

@[simp]
theorem sum_ite_self_eq' [DecidableEq α] {N : Type _} [AddCommMonoidₓ N] (f : α →₀ N) (a : α) :
  (f.sum fun x v => ite (x = a) v 0) = f a :=
  by 
    convert f.sum_ite_eq' a fun x => id 
    simp [ite_eq_right_iff.2 Eq.symm]

@[simp]
theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) : (f.prod fun a b => g a ^ b) = ∏a, g a ^ f a :=
  f.prod_fintype _$ fun a => pow_zeroₓ _

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `on_finset` is the same as multiplying it over the original
`finset`. -/
@[to_additive #[expr "If `g` maps a second argument of 0 to 0, summing it over the\nresult of `on_finset` is the same as summing it over the original\n`finset`."]]
theorem on_finset_prod
{s : finset α}
{f : α → M}
{g : α → M → N}
(hf : ∀ a, «expr ≠ »(f a, 0) → «expr ∈ »(a, s))
(hg : ∀ a, «expr = »(g a 0, 1)) : «expr = »((on_finset s f hf).prod g, «expr∏ in , »((a), s, g a (f a))) :=
«expr $ »(finset.prod_subset support_on_finset_subset, by simp [] [] [] ["[", "*", "]"] [] [] { contextual := tt })

@[toAdditive]
theorem _root_.submonoid.finsupp_prod_mem (S : Submonoid N) (f : α →₀ M) (g : α → M → N)
  (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.prod g ∈ S :=
  S.prod_mem$ fun i hi => h _ (Finsupp.mem_support_iff.mp hi)

end SumProd

/-!
### Additive monoid structure on `α →₀ M`
-/


section AddZeroClass

variable [AddZeroClass M]

instance : Add (α →₀ M) :=
  ⟨zip_with (·+·) (add_zeroₓ 0)⟩

@[simp]
theorem coe_add (f g : α →₀ M) : «expr⇑ » (f+g) = f+g :=
  rfl

theorem add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁+g₂) a = g₁ a+g₂ a :=
  rfl

theorem support_add [DecidableEq α] {g₁ g₂ : α →₀ M} : (g₁+g₂).Support ⊆ g₁.support ∪ g₂.support :=
  support_zip_with

theorem support_add_eq [DecidableEq α] {g₁ g₂ : α →₀ M} (h : Disjoint g₁.support g₂.support) :
  (g₁+g₂).Support = g₁.support ∪ g₂.support :=
  le_antisymmₓ support_zip_with$
    fun a ha =>
      (Finset.mem_union.1 ha).elim
        (fun ha =>
          have  : a ∉ g₂.support := disjoint_left.1 h ha 
          by 
            simp only [mem_support_iff, not_not] at * <;> simpa only [add_apply, this, add_zeroₓ])
        fun ha =>
          have  : a ∉ g₁.support := disjoint_right.1 h ha 
          by 
            simp only [mem_support_iff, not_not] at * <;> simpa only [add_apply, this, zero_addₓ]

@[simp]
theorem single_add {a : α} {b₁ b₂ : M} : single a (b₁+b₂) = single a b₁+single a b₂ :=
  ext$
    fun a' =>
      by 
        byCases' h : a = a'
        ·
          rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same]
        ·
          rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_addₓ]

instance : AddZeroClass (α →₀ M) :=
  { zero := 0, add := ·+·, zero_add := fun ⟨s, f, hf⟩ => ext$ fun a => zero_addₓ _,
    add_zero := fun ⟨s, f, hf⟩ => ext$ fun a => add_zeroₓ _ }

/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` for the stronger version as a linear map.
-/
@[simps]
def single_add_hom (a : α) : M →+ α →₀ M :=
  ⟨single a, single_zero, fun _ _ => single_add⟩

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` for the stronger version as a linear map. -/
@[simps apply]
def apply_add_hom (a : α) : (α →₀ M) →+ M :=
  ⟨fun g => g a, zero_apply, fun _ _ => add_apply _ _ _⟩

theorem update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) : f.update a b = single a b+f.erase a :=
  by 
    ext j 
    rcases eq_or_ne a j with (rfl | h)
    ·
      simp 
    ·
      simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]

theorem update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) : f.update a b = f.erase a+single a b :=
  by 
    ext j 
    rcases eq_or_ne a j with (rfl | h)
    ·
      simp 
    ·
      simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]

theorem single_add_erase (a : α) (f : α →₀ M) : (single a (f a)+f.erase a) = f :=
  by 
    rw [←update_eq_single_add_erase, update_self]

theorem erase_add_single (a : α) (f : α →₀ M) : (f.erase a+single a (f a)) = f :=
  by 
    rw [←update_eq_erase_add_single, update_self]

@[simp]
theorem erase_add (a : α) (f f' : α →₀ M) : erase a (f+f') = erase a f+erase a f' :=
  by 
    ext s 
    byCases' hs : s = a
    ·
      rw [hs, add_apply, erase_same, erase_same, erase_same, add_zeroₓ]
    rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]

/-- `finsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def erase_add_hom (a : α) : (α →₀ M) →+ α →₀ M :=
  { toFun := erase a, map_zero' := erase_zero a, map_add' := erase_add a }

@[elab_as_eliminator]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
  (ha : ∀ a b f : α →₀ M, a ∉ f.support → b ≠ 0 → p f → p (single a b+f)) : p f :=
  suffices ∀ s f : α →₀ M, f.support = s → p f from this _ _ rfl 
  fun s =>
    (Finset.induction_on s
        fun f hf =>
          by 
            rwa [support_eq_empty.1 hf])$
      fun a s has ih f hf =>
        suffices p (single a (f a)+f.erase a)by 
          rwa [single_add_erase] at this 
        by 
          apply ha
          ·
            rw [support_erase, mem_erase]
            exact fun H => H.1 rfl
          ·
            rw [←mem_support_iff, hf]
            exact mem_insert_self _ _
          ·
            apply ih _ _ 
            rw [support_erase, hf, Finset.erase_insert has]

theorem induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
  (ha : ∀ a b f : α →₀ M, a ∉ f.support → b ≠ 0 → p f → p (f+single a b)) : p f :=
  suffices ∀ s f : α →₀ M, f.support = s → p f from this _ _ rfl 
  fun s =>
    (Finset.induction_on s
        fun f hf =>
          by 
            rwa [support_eq_empty.1 hf])$
      fun a s has ih f hf =>
        suffices p (f.erase a+single a (f a))by 
          rwa [erase_add_single] at this 
        by 
          apply ha
          ·
            rw [support_erase, mem_erase]
            exact fun H => H.1 rfl
          ·
            rw [←mem_support_iff, hf]
            exact mem_insert_self _ _
          ·
            apply ih _ _ 
            rw [support_erase, hf, Finset.erase_insert has]

theorem induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0) (hadd : ∀ f g : α →₀ M, p f → p g → p (f+g))
  (hsingle : ∀ a b, p (single a b)) : p f :=
  induction₂ f h0 fun a b f _ _ w => hadd _ _ w (hsingle _ _)

@[simp]
theorem add_closure_Union_range_single : AddSubmonoid.closure (⋃a : α, Set.Range (single a : M → α →₀ M)) = ⊤ :=
  top_unique$
    fun x hx =>
      Finsupp.induction x (AddSubmonoid.zero_mem _)$
        fun a b f ha hb hf =>
          AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure$ Set.mem_Union.2 ⟨a, Set.mem_range_self _⟩) hf

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal. -/
theorem add_hom_ext [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄ (H : ∀ x y, f (single x y) = g (single x y)) : f = g :=
  by 
    refine' AddMonoidHom.eq_of_eq_on_mdense add_closure_Union_range_single fun f hf => _ 
    simp only [Set.mem_Union, Set.mem_range] at hf 
    rcases hf with ⟨x, y, rfl⟩
    apply H

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext]
theorem add_hom_ext' [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄
  (H : ∀ x, f.comp (single_add_hom x) = g.comp (single_add_hom x)) : f = g :=
  add_hom_ext$ fun x => AddMonoidHom.congr_fun (H x)

theorem mul_hom_ext [MulOneClass N] ⦃f g : Multiplicative (α →₀ M) →* N⦄
  (H : ∀ x y, f (Multiplicative.ofAdd$ single x y) = g (Multiplicative.ofAdd$ single x y)) : f = g :=
  MonoidHom.ext$ AddMonoidHom.congr_fun$ @add_hom_ext α M (Additive N) _ _ f.to_additive'' g.to_additive'' H

@[ext]
theorem mul_hom_ext' [MulOneClass N] {f g : Multiplicative (α →₀ M) →* N}
  (H : ∀ x, f.comp (single_add_hom x).toMultiplicative = g.comp (single_add_hom x).toMultiplicative) : f = g :=
  mul_hom_ext$ fun x => MonoidHom.congr_fun (H x)

theorem map_range_add [AddZeroClass N] {f : M → N} {hf : f 0 = 0} (hf' : ∀ x y, f (x+y) = f x+f y) (v₁ v₂ : α →₀ M) :
  map_range f hf (v₁+v₂) = map_range f hf v₁+map_range f hf v₂ :=
  ext$
    fun a =>
      by 
        simp only [hf', add_apply, map_range_apply]

/-- Bundle `emb_domain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps]
def emb_domain.add_monoid_hom (f : α ↪ β) : (α →₀ M) →+ β →₀ M :=
  { toFun := fun v => emb_domain f v,
    map_zero' :=
      by 
        simp ,
    map_add' :=
      fun v w =>
        by 
          ext b 
          byCases' h : b ∈ Set.Range f
          ·
            rcases h with ⟨a, rfl⟩
            simp 
          ·
            simp [emb_domain_notin_range, h] }

@[simp]
theorem emb_domain_add (f : α ↪ β) (v w : α →₀ M) : emb_domain f (v+w) = emb_domain f v+emb_domain f w :=
  (emb_domain.add_monoid_hom f).map_add v w

end AddZeroClass

section AddMonoidₓ

variable [AddMonoidₓ M]

instance : AddMonoidₓ (α →₀ M) :=
  { Finsupp.addZeroClass with zero := 0, add := ·+·,
    add_assoc := fun ⟨s, f, hf⟩ ⟨t, g, hg⟩ ⟨u, h, hh⟩ => ext$ fun a => add_assocₓ _ _ _,
    nsmul := fun n v => v.map_range ((· • ·) n) (nsmul_zero _),
    nsmul_zero' :=
      fun v =>
        by 
          ext i 
          simp ,
    nsmul_succ' :=
      fun n v =>
        by 
          ext i 
          simp [Nat.succ_eq_one_add, add_nsmul] }

end AddMonoidₓ

end Finsupp

@[toAdditive]
theorem MulEquiv.map_finsupp_prod [HasZero M] [CommMonoidₓ N] [CommMonoidₓ P] (h : N ≃* P) (f : α →₀ M)
  (g : α → M → N) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  h.map_prod _ _

@[toAdditive]
theorem MonoidHom.map_finsupp_prod [HasZero M] [CommMonoidₓ N] [CommMonoidₓ P] (h : N →* P) (f : α →₀ M)
  (g : α → M → N) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  h.map_prod _ _

theorem RingHom.map_finsupp_sum [HasZero M] [Semiringₓ R] [Semiringₓ S] (h : R →+* S) (f : α →₀ M) (g : α → M → R) :
  h (f.sum g) = f.sum fun a b => h (g a b) :=
  h.map_sum _ _

theorem RingHom.map_finsupp_prod [HasZero M] [CommSemiringₓ R] [CommSemiringₓ S] (h : R →+* S) (f : α →₀ M)
  (g : α → M → R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  h.map_prod _ _

@[toAdditive]
theorem MonoidHom.coe_finsupp_prod [HasZero β] [Monoidₓ N] [CommMonoidₓ P] (f : α →₀ β) (g : α → β → N →* P) :
  «expr⇑ » (f.prod g) = f.prod fun i fi => g i fi :=
  MonoidHom.coe_prod _ _

@[simp, toAdditive]
theorem MonoidHom.finsupp_prod_apply [HasZero β] [Monoidₓ N] [CommMonoidₓ P] (f : α →₀ β) (g : α → β → N →* P) (x : N) :
  f.prod g x = f.prod fun i fi => g i fi x :=
  MonoidHom.finset_prod_apply _ _ _

namespace Finsupp

instance [AddCommMonoidₓ M] : AddCommMonoidₓ (α →₀ M) :=
  { Finsupp.addMonoid with add_comm := fun ⟨s, f, _⟩ ⟨t, g, _⟩ => ext$ fun a => add_commₓ _ _ }

instance [AddGroupₓ G] : Sub (α →₀ G) :=
  ⟨zip_with Sub.sub (sub_zero _)⟩

instance [AddGroupₓ G] : AddGroupₓ (α →₀ G) :=
  { Finsupp.addMonoid with neg := map_range Neg.neg neg_zero, sub := Sub.sub,
    sub_eq_add_neg := fun x y => ext fun i => sub_eq_add_neg _ _,
    add_left_neg := fun ⟨s, f, _⟩ => ext$ fun x => add_left_negₓ _,
    zsmul := fun n v => v.map_range ((· • ·) n) (zsmul_zero _),
    zsmul_zero' :=
      fun v =>
        by 
          ext i 
          simp ,
    zsmul_succ' :=
      fun n v =>
        by 
          ext i 
          simp [Nat.succ_eq_one_add, add_zsmul],
    zsmul_neg' :=
      fun n v =>
        by 
          ext i 
          simp only [Nat.succ_eq_add_one, map_range_apply, zsmul_neg_succ_of_nat, Int.coe_nat_succ, neg_inj, add_zsmul,
            add_nsmul, one_zsmul, coe_nat_zsmul, one_nsmul] }

instance [AddCommGroupₓ G] : AddCommGroupₓ (α →₀ G) :=
  { Finsupp.addGroup with add_comm := add_commₓ }

theorem single_multiset_sum [AddCommMonoidₓ M] (s : Multiset M) (a : α) : single a s.sum = (s.map (single a)).Sum :=
  Multiset.induction_on s single_zero$
    fun a s ih =>
      by 
        rw [Multiset.sum_cons, single_add, ih, Multiset.map_cons, Multiset.sum_cons]

theorem single_finset_sum [AddCommMonoidₓ M] (s : Finset ι) (f : ι → M) (a : α) :
  single a (∑b in s, f b) = ∑b in s, single a (f b) :=
  by 
    trans 
    apply single_multiset_sum 
    rw [Multiset.map_map]
    rfl

theorem single_sum [HasZero M] [AddCommMonoidₓ N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
  single a (s.sum f) = s.sum fun d c => single a (f d c) :=
  single_finset_sum _ _ _

@[toAdditive]
theorem prod_neg_index [AddGroupₓ G] [CommMonoidₓ M] {g : α →₀ G} {h : α → G → M} (h0 : ∀ a, h a 0 = 1) :
  (-g).Prod h = g.prod fun a b => h a (-b) :=
  prod_map_range_index h0

@[simp]
theorem coe_neg [AddGroupₓ G] (g : α →₀ G) : «expr⇑ » (-g) = -g :=
  rfl

theorem neg_apply [AddGroupₓ G] (g : α →₀ G) (a : α) : (-g) a = -g a :=
  rfl

@[simp]
theorem coe_sub [AddGroupₓ G] (g₁ g₂ : α →₀ G) : «expr⇑ » (g₁ - g₂) = g₁ - g₂ :=
  rfl

theorem sub_apply [AddGroupₓ G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a :=
  rfl

@[simp]
theorem support_neg [AddGroupₓ G] {f : α →₀ G} : support (-f) = support f :=
  Finset.Subset.antisymm support_map_range
    (calc support f = support (- -f) := congr_argₓ support (neg_negₓ _).symm 
      _ ⊆ support (-f) := support_map_range
      )

theorem erase_eq_sub_single [AddGroupₓ G] (f : α →₀ G) (a : α) : f.erase a = f - single a (f a) :=
  by 
    ext a' 
    rcases eq_or_ne a a' with (rfl | h)
    ·
      simp 
    ·
      simp [erase_ne h.symm, single_eq_of_ne h]

theorem update_eq_sub_add_single [AddGroupₓ G] (f : α →₀ G) (a : α) (b : G) :
  f.update a b = (f - single a (f a))+single a b :=
  by 
    rw [update_eq_erase_add_single, erase_eq_sub_single]

@[simp]
theorem sum_apply [HasZero M] [AddCommMonoidₓ N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
  (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂ :=
  (apply_add_hom a₂ : (β →₀ N) →+ _).map_sum _ _

theorem support_sum [DecidableEq β] [HasZero M] [AddCommMonoidₓ N] {f : α →₀ M} {g : α → M → β →₀ N} :
  (f.sum g).Support ⊆ f.support.bUnion fun a => (g a (f a)).Support :=
  have  : ∀ c, (f.sum fun a b => g a b c) ≠ 0 → ∃ a, f a ≠ 0 ∧ ¬(g a (f a)) c = 0 :=
    fun a₁ h =>
      let ⟨a, ha, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      ⟨a, mem_support_iff.mp ha, Ne⟩
  by 
    simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_bUnion, sum_apply, exists_prop]

@[simp]
theorem sum_zero [HasZero M] [AddCommMonoidₓ N] {f : α →₀ M} : (f.sum fun a b => (0 : N)) = 0 :=
  Finset.sum_const_zero

@[simp, toAdditive]
theorem prod_mul [HasZero M] [CommMonoidₓ N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
  (f.prod fun a b => h₁ a b*h₂ a b) = f.prod h₁*f.prod h₂ :=
  Finset.prod_mul_distrib

@[simp, toAdditive]
theorem prod_inv [HasZero M] [CommGroupₓ G] {f : α →₀ M} {h : α → M → G} : (f.prod fun a b => h a b⁻¹) = f.prod h⁻¹ :=
  (MonoidHom.id G⁻¹.map_prod _ _).symm

@[simp]
theorem sum_sub [HasZero M] [AddCommGroupₓ G] {f : α →₀ M} {h₁ h₂ : α → M → G} :
  (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
  Finset.sum_sub_distrib

@[toAdditive]
theorem prod_add_index [AddCommMonoidₓ M] [CommMonoidₓ N] {f g : α →₀ M} {h : α → M → N} (h_zero : ∀ a, h a 0 = 1)
  (h_add : ∀ a b₁ b₂, h a (b₁+b₂) = h a b₁*h a b₂) : (f+g).Prod h = f.prod h*g.prod h :=
  have hf : f.prod h = ∏a in f.support ∪ g.support, h a (f a) :=
    f.prod_of_support_subset (subset_union_left _ _) _$ fun a ha => h_zero a 
  have hg : g.prod h = ∏a in f.support ∪ g.support, h a (g a) :=
    g.prod_of_support_subset (subset_union_right _ _) _$ fun a ha => h_zero a 
  have hfg : (f+g).Prod h = ∏a in f.support ∪ g.support, h a ((f+g) a) :=
    (f+g).prod_of_support_subset support_add _$ fun a ha => h_zero a 
  by 
    simp only [add_apply, prod_mul_distrib]

@[simp]
theorem sum_add_index' [AddCommMonoidₓ M] [AddCommMonoidₓ N] {f g : α →₀ M} (h : α → M →+ N) :
  ((f+g).Sum fun x => h x) = (f.sum fun x => h x)+g.sum fun x => h x :=
  sum_add_index (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]
theorem prod_add_index' [AddCommMonoidₓ M] [CommMonoidₓ N] {f g : α →₀ M} (h : α → Multiplicative M →* N) :
  ((f+g).Prod fun a b => h a (Multiplicative.ofAdd b)) =
    (f.prod fun a b => h a (Multiplicative.ofAdd b))*g.prod fun a b => h a (Multiplicative.ofAdd b) :=
  prod_add_index (fun a => (h a).map_one) fun a => (h a).map_mul

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def lift_add_hom [AddCommMonoidₓ M] [AddCommMonoidₓ N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) :=
  { toFun :=
      fun F =>
        { toFun := fun f => f.sum fun x => F x, map_zero' := Finset.sum_empty,
          map_add' := fun _ _ => sum_add_index (fun x => (F x).map_zero) fun x => (F x).map_add },
    invFun := fun F x => F.comp$ single_add_hom x,
    left_inv :=
      fun F =>
        by 
          ext 
          simp ,
    right_inv :=
      fun F =>
        by 
          ext 
          simp ,
    map_add' :=
      fun F G =>
        by 
          ext 
          simp  }

@[simp]
theorem lift_add_hom_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : α → M →+ N) (f : α →₀ M) :
  lift_add_hom F f = f.sum fun x => F x :=
  rfl

@[simp]
theorem lift_add_hom_symm_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : (α →₀ M) →+ N) (x : α) :
  lift_add_hom.symm F x = F.comp (single_add_hom x) :=
  rfl

theorem lift_add_hom_symm_apply_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : (α →₀ M) →+ N) (x : α) (y : M) :
  lift_add_hom.symm F x y = F (single x y) :=
  rfl

@[simp]
theorem lift_add_hom_single_add_hom [AddCommMonoidₓ M] :
  lift_add_hom (single_add_hom : α → M →+ α →₀ M) = AddMonoidHom.id _ :=
  lift_add_hom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

@[simp]
theorem sum_single [AddCommMonoidₓ M] (f : α →₀ M) : f.sum single = f :=
  AddMonoidHom.congr_fun lift_add_hom_single_add_hom f

@[simp]
theorem lift_add_hom_apply_single [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : α → M →+ N) (a : α) (b : M) :
  lift_add_hom f (single a b) = f a b :=
  sum_single_index (f a).map_zero

@[simp]
theorem lift_add_hom_comp_single [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : α → M →+ N) (a : α) :
  (lift_add_hom f).comp (single_add_hom a) = f a :=
  AddMonoidHom.ext$ fun b => lift_add_hom_apply_single f a b

theorem comp_lift_add_hom [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P] (g : N →+ P) (f : α → M →+ N) :
  g.comp (lift_add_hom f) = lift_add_hom fun a => g.comp (f a) :=
  lift_add_hom.symm_apply_eq.1$
    funext$
      fun a =>
        by 
          rw [lift_add_hom_symm_apply, AddMonoidHom.comp_assoc, lift_add_hom_comp_single]

theorem sum_sub_index [AddCommGroupₓ β] [AddCommGroupₓ γ] {f g : α →₀ β} {h : α → β → γ}
  (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).Sum h = f.sum h - g.sum h :=
  (lift_add_hom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[toAdditive]
theorem prod_emb_domain [HasZero M] [CommMonoidₓ N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
  (v.emb_domain f).Prod g = v.prod fun a b => g (f a) b :=
  by 
    rw [Prod, Prod, support_emb_domain, Finset.prod_map]
    simpRw [emb_domain_apply]

@[toAdditive]
theorem prod_finset_sum_index [AddCommMonoidₓ M] [CommMonoidₓ N] {s : Finset ι} {g : ι → α →₀ M} {h : α → M → N}
  (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁+b₂) = h a b₁*h a b₂) :
  (∏i in s, (g i).Prod h) = (∑i in s, g i).Prod h :=
  Finset.induction_on s rfl$
    fun a s has ih =>
      by 
        rw [prod_insert has, ih, sum_insert has, prod_add_index h_zero h_add]

@[toAdditive]
theorem prod_sum_index [AddCommMonoidₓ M] [AddCommMonoidₓ N] [CommMonoidₓ P] {f : α →₀ M} {g : α → M → β →₀ N}
  {h : β → N → P} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁+b₂) = h a b₁*h a b₂) :
  (f.sum g).Prod h = f.prod fun a b => (g a b).Prod h :=
  (prod_finset_sum_index h_zero h_add).symm

theorem multiset_sum_sum_index [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : Multiset (α →₀ M)) (h : α → M → N)
  (h₀ : ∀ a, h a 0 = 0) (h₁ : ∀ a : α b₁ b₂ : M, h a (b₁+b₂) = h a b₁+h a b₂) :
  f.sum.sum h = (f.map$ fun g : α →₀ M => g.sum h).Sum :=
  Multiset.induction_on f rfl$
    fun a s ih =>
      by 
        rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_index h₀ h₁, ih]

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem support_sum_eq_bUnion
{α : Type*}
{ι : Type*}
{M : Type*}
[add_comm_monoid M]
{g : ι → «expr →₀ »(α, M)}
(s : finset ι)
(h : ∀
 i₁
 i₂, «expr ≠ »(i₁, i₂) → disjoint (g i₁).support (g i₂).support) : «expr = »(«expr∑ in , »((i), s, g i).support, s.bUnion (λ
  i, (g i).support)) :=
begin
  apply [expr finset.induction_on s],
  { simp [] [] [] [] [] [] },
  { intros [ident i, ident s, ident hi],
    simp [] [] ["only"] ["[", expr hi, ",", expr sum_insert, ",", expr not_false_iff, ",", expr bUnion_insert, "]"] [] [],
    intro [ident hs],
    rw ["[", expr finsupp.support_add_eq, ",", expr hs, "]"] [],
    rw ["[", expr hs, "]"] [],
    intros [ident x, ident hx],
    simp [] [] ["only"] ["[", expr mem_bUnion, ",", expr exists_prop, ",", expr inf_eq_inter, ",", expr ne.def, ",", expr mem_inter, "]"] [] ["at", ident hx],
    obtain ["⟨", ident hxi, ",", ident j, ",", ident hj, ",", ident hxj, "⟩", ":=", expr hx],
    have [ident hn] [":", expr «expr ≠ »(i, j)] [":=", expr λ H, hi «expr ▸ »(H.symm, hj)],
    apply [expr h _ _ hn],
    simp [] [] [] ["[", expr hxi, ",", expr hxj, "]"] [] [] }
end

theorem multiset_map_sum [HasZero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
  Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m :=
  (Multiset.mapAddMonoidHom m).map_sum _ f.support

theorem multiset_sum_sum [HasZero M] [AddCommMonoidₓ N] {f : α →₀ M} {h : α → M → Multiset N} :
  Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) :=
  (Multiset.sumAddMonoidHom : Multiset N →+ N).map_sum _ f.support

section MapRange

section Equiv

variable [HasZero M] [HasZero N] [HasZero P]

/-- `finsupp.map_range` as an equiv. -/
@[simps apply]
def map_range.equiv (f : M ≃ N) (hf : f 0 = 0) (hf' : f.symm 0 = 0) : (α →₀ M) ≃ (α →₀ N) :=
  { toFun := (map_range f hf : (α →₀ M) → α →₀ N), invFun := (map_range f.symm hf' : (α →₀ N) → α →₀ M),
    left_inv :=
      fun x =>
        by 
          rw [←map_range_comp _ _ _ _] <;> simpRw [Equiv.symm_comp_self]
          ·
            exact map_range_id _
          ·
            rfl,
    right_inv :=
      fun x =>
        by 
          rw [←map_range_comp _ _ _ _] <;> simpRw [Equiv.self_comp_symm]
          ·
            exact map_range_id _
          ·
            rfl }

@[simp]
theorem map_range.equiv_refl : map_range.equiv (Equiv.refl M) rfl rfl = Equiv.refl (α →₀ M) :=
  Equiv.ext map_range_id

theorem map_range.equiv_trans (f : M ≃ N) (hf : f 0 = 0) hf' (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) hf₂' :
  (map_range.equiv (f.trans f₂)
      (by 
        rw [Equiv.trans_apply, hf, hf₂])
      (by 
        rw [Equiv.symm_trans_apply, hf₂', hf']) :
    (α →₀ _) ≃ _) =
    (map_range.equiv f hf hf').trans (map_range.equiv f₂ hf₂ hf₂') :=
  Equiv.ext$ map_range_comp _ _ _ _ _

@[simp]
theorem map_range.equiv_symm (f : M ≃ N) hf hf' :
  ((map_range.equiv f hf hf').symm : (α →₀ _) ≃ _) = map_range.equiv f.symm hf' hf :=
  Equiv.ext$ fun x => rfl

end Equiv

section ZeroHom

variable [HasZero M] [HasZero N] [HasZero P]

/-- Composition with a fixed zero-preserving homomorphism is itself an zero-preserving homomorphism
on functions. -/
@[simps]
def map_range.zero_hom (f : ZeroHom M N) : ZeroHom (α →₀ M) (α →₀ N) :=
  { toFun := (map_range f f.map_zero : (α →₀ M) → α →₀ N), map_zero' := map_range_zero }

@[simp]
theorem map_range.zero_hom_id : map_range.zero_hom (ZeroHom.id M) = ZeroHom.id (α →₀ M) :=
  ZeroHom.ext map_range_id

theorem map_range.zero_hom_comp (f : ZeroHom N P) (f₂ : ZeroHom M N) :
  (map_range.zero_hom (f.comp f₂) : ZeroHom (α →₀ _) _) = (map_range.zero_hom f).comp (map_range.zero_hom f₂) :=
  ZeroHom.ext$ map_range_comp _ _ _ _ _

end ZeroHom

section AddMonoidHom

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P]

/--
Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
def map_range.add_monoid_hom (f : M →+ N) : (α →₀ M) →+ α →₀ N :=
  { toFun := (map_range f f.map_zero : (α →₀ M) → α →₀ N), map_zero' := map_range_zero,
    map_add' := fun a b => map_range_add f.map_add _ _ }

@[simp]
theorem map_range.add_monoid_hom_id : map_range.add_monoid_hom (AddMonoidHom.id M) = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext map_range_id

theorem map_range.add_monoid_hom_comp (f : N →+ P) (f₂ : M →+ N) :
  (map_range.add_monoid_hom (f.comp f₂) : (α →₀ _) →+ _) =
    (map_range.add_monoid_hom f).comp (map_range.add_monoid_hom f₂) :=
  AddMonoidHom.ext$ map_range_comp _ _ _ _ _

@[simp]
theorem map_range.add_monoid_hom_to_zero_hom (f : M →+ N) :
  (map_range.add_monoid_hom f).toZeroHom = (map_range.zero_hom f.to_zero_hom : ZeroHom (α →₀ _) _) :=
  ZeroHom.ext$ fun _ => rfl

theorem map_range_multiset_sum (f : M →+ N) (m : Multiset (α →₀ M)) :
  map_range f f.map_zero m.sum = (m.map$ fun x => map_range f f.map_zero x).Sum :=
  (map_range.add_monoid_hom f : (α →₀ _) →+ _).map_multiset_sum _

theorem map_range_finset_sum (f : M →+ N) (s : Finset ι) (g : ι → α →₀ M) :
  map_range f f.map_zero (∑x in s, g x) = ∑x in s, map_range f f.map_zero (g x) :=
  (map_range.add_monoid_hom f : (α →₀ _) →+ _).map_sum _ _

/-- `finsupp.map_range.add_monoid_hom` as an equiv. -/
@[simps apply]
def map_range.add_equiv (f : M ≃+ N) : (α →₀ M) ≃+ (α →₀ N) :=
  { map_range.add_monoid_hom f.to_add_monoid_hom with toFun := (map_range f f.map_zero : (α →₀ M) → α →₀ N),
    invFun := (map_range f.symm f.symm.map_zero : (α →₀ N) → α →₀ M),
    left_inv :=
      fun x =>
        by 
          rw [←map_range_comp _ _ _ _] <;> simpRw [AddEquiv.symm_comp_self]
          ·
            exact map_range_id _
          ·
            rfl,
    right_inv :=
      fun x =>
        by 
          rw [←map_range_comp _ _ _ _] <;> simpRw [AddEquiv.self_comp_symm]
          ·
            exact map_range_id _
          ·
            rfl }

@[simp]
theorem map_range.add_equiv_refl : map_range.add_equiv (AddEquiv.refl M) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext map_range_id

theorem map_range.add_equiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
  (map_range.add_equiv (f.trans f₂) : (α →₀ _) ≃+ _) = (map_range.add_equiv f).trans (map_range.add_equiv f₂) :=
  AddEquiv.ext$ map_range_comp _ _ _ _ _

@[simp]
theorem map_range.add_equiv_symm (f : M ≃+ N) :
  ((map_range.add_equiv f).symm : (α →₀ _) ≃+ _) = map_range.add_equiv f.symm :=
  AddEquiv.ext$ fun x => rfl

@[simp]
theorem map_range.add_equiv_to_add_monoid_hom (f : M ≃+ N) :
  (map_range.add_equiv f : (α →₀ _) ≃+ _).toAddMonoidHom =
    (map_range.add_monoid_hom f.to_add_monoid_hom : (α →₀ _) →+ _) :=
  AddMonoidHom.ext$ fun _ => rfl

@[simp]
theorem map_range.add_equiv_to_equiv (f : M ≃+ N) :
  (map_range.add_equiv f).toEquiv = (map_range.equiv f.to_equiv f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
  Equiv.ext$ fun _ => rfl

end AddMonoidHom

end MapRange

/-! ### Declarations about `map_domain` -/


section MapDomain

variable [AddCommMonoidₓ M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def map_domain (f : α → β) (v : α →₀ M) : β →₀ M :=
  v.sum$ fun a => single (f a)

theorem map_domain_apply {f : α → β} (hf : Function.Injective f) (x : α →₀ M) (a : α) : map_domain f x (f a) = x a :=
  by 
    rw [map_domain, sum_apply, Sum, Finset.sum_eq_single a, single_eq_same]
    ·
      intro b _ hba 
      exact single_eq_of_ne (hf.ne hba)
    ·
      intro h 
      rw [not_mem_support_iff.1 h, single_zero, zero_apply]

theorem map_domain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ Set.Range f) : map_domain f x a = 0 :=
  by 
    rw [map_domain, sum_apply, Sum]
    exact Finset.sum_eq_zero fun a' h' => single_eq_of_ne$ fun eq => h$ Eq ▸ Set.mem_range_self _

@[simp]
theorem map_domain_id : map_domain id v = v :=
  sum_single _

theorem map_domain_comp {f : α → β} {g : β → γ} : map_domain (g ∘ f) v = map_domain g (map_domain f v) :=
  by 
    refine' ((sum_sum_index _ _).trans _).symm
    ·
      intros 
      exact single_zero
    ·
      intros 
      exact single_add 
    refine' sum_congr rfl fun _ _ => sum_single_index _
    ·
      exact single_zero

@[simp]
theorem map_domain_single {f : α → β} {a : α} {b : M} : map_domain f (single a b) = single (f a) b :=
  sum_single_index single_zero

@[simp]
theorem map_domain_zero {f : α → β} : map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
  sum_zero_index

theorem map_domain_congr {f g : α → β} (h : ∀ x _ : x ∈ v.support, f x = g x) : v.map_domain f = v.map_domain g :=
  Finset.sum_congr rfl$
    fun _ H =>
      by 
        simp only [h _ H]

theorem map_domain_add {f : α → β} : map_domain f (v₁+v₂) = map_domain f v₁+map_domain f v₂ :=
  sum_add_index (fun _ => single_zero) fun _ _ _ => single_add

@[simp]
theorem map_domain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) : map_domain f x a = x (f.symm a) :=
  by 
    convLHS => rw [←f.apply_symm_apply a]
    exact map_domain_apply f.injective _ _

/-- `finsupp.map_domain` is an `add_monoid_hom`. -/
@[simps]
def map_domain.add_monoid_hom (f : α → β) : (α →₀ M) →+ β →₀ M :=
  { toFun := map_domain f, map_zero' := map_domain_zero, map_add' := fun _ _ => map_domain_add }

@[simp]
theorem map_domain.add_monoid_hom_id : map_domain.add_monoid_hom id = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext$ fun _ => map_domain_id

theorem map_domain.add_monoid_hom_comp (f : β → γ) (g : α → β) :
  (map_domain.add_monoid_hom (f ∘ g) : (α →₀ M) →+ γ →₀ M) =
    (map_domain.add_monoid_hom f).comp (map_domain.add_monoid_hom g) :=
  AddMonoidHom.ext$ fun _ => map_domain_comp

theorem map_domain_finset_sum {f : α → β} {s : Finset ι} {v : ι → α →₀ M} :
  map_domain f (∑i in s, v i) = ∑i in s, map_domain f (v i) :=
  (map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_sum _ _

theorem map_domain_sum [HasZero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
  map_domain f (s.sum v) = s.sum fun a b => map_domain f (v a b) :=
  (map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_finsupp_sum _ _

theorem map_domain_support [DecidableEq β] {f : α → β} {s : α →₀ M} : (s.map_domain f).Support ⊆ s.support.image f :=
  Finset.Subset.trans support_sum$
    Finset.Subset.trans (Finset.bUnion_mono$ fun a ha => support_single_subset)$
      by 
        rw [Finset.bUnion_singleton] <;> exact subset.refl _

@[toAdditive]
theorem prod_map_domain_index [CommMonoidₓ N] {f : α → β} {s : α →₀ M} {h : β → M → N} (h_zero : ∀ b, h b 0 = 1)
  (h_add : ∀ b m₁ m₂, h b (m₁+m₂) = h b m₁*h b m₂) : (map_domain f s).Prod h = s.prod fun a m => h (f a) m :=
  (prod_sum_index h_zero h_add).trans$ prod_congr rfl$ fun _ _ => prod_single_index (h_zero _)

/--
A version of `sum_map_domain_index` that takes a bundled `add_monoid_hom`,
rather than separate linearity hypotheses.
-/
@[simp]
theorem sum_map_domain_index_add_monoid_hom [AddCommMonoidₓ N] {f : α → β} {s : α →₀ M} (h : β → M →+ N) :
  ((map_domain f s).Sum fun b m => h b m) = s.sum fun a m => h (f a) m :=
  @sum_map_domain_index _ _ _ _ _ _ _ _ (fun b m => h b m) (fun b => (h b).map_zero) fun b m₁ m₂ => (h b).map_add _ _

theorem emb_domain_eq_map_domain (f : α ↪ β) (v : α →₀ M) : emb_domain f v = map_domain f v :=
  by 
    ext a 
    byCases' a ∈ Set.Range f
    ·
      rcases h with ⟨a, rfl⟩
      rw [map_domain_apply f.injective, emb_domain_apply]
    ·
      rw [map_domain_notin_range, emb_domain_notin_range] <;> assumption

@[toAdditive]
theorem prod_map_domain_index_inj [CommMonoidₓ N] {f : α → β} {s : α →₀ M} {h : β → M → N} (hf : Function.Injective f) :
  (s.map_domain f).Prod h = s.prod fun a b => h (f a) b :=
  by 
    rw [←Function.Embedding.coe_fn_mk f hf, ←emb_domain_eq_map_domain, prod_emb_domain]

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_domain_injective
{f : α → β}
(hf : function.injective f) : function.injective (map_domain f : «expr →₀ »(α, M) → «expr →₀ »(β, M)) :=
begin
  assume [binders (v₁ v₂ eq)],
  ext [] [ident a] [],
  have [] [":", expr «expr = »(map_domain f v₁ (f a), map_domain f v₂ (f a))] [],
  { rw [expr eq] [] },
  rwa ["[", expr map_domain_apply hf, ",", expr map_domain_apply hf, "]"] ["at", ident this]
end

theorem map_domain.add_monoid_hom_comp_map_range [AddCommMonoidₓ N] (f : α → β) (g : M →+ N) :
  (map_domain.add_monoid_hom f).comp (map_range.add_monoid_hom g) =
    (map_range.add_monoid_hom g).comp (map_domain.add_monoid_hom f) :=
  by 
    ext 
    simp 

/-- When `g` preserves addition, `map_range` and `map_domain` commute. -/
theorem map_domain_map_range [AddCommMonoidₓ N] (f : α → β) (v : α →₀ M) (g : M → N) (h0 : g 0 = 0)
  (hadd : ∀ x y, g (x+y) = g x+g y) : map_domain f (map_range g h0 v) = map_range g h0 (map_domain f v) :=
  let g' : M →+ N := { toFun := g, map_zero' := h0, map_add' := hadd }
  AddMonoidHom.congr_fun (map_domain.add_monoid_hom_comp_map_range f g') v

end MapDomain

/-! ### Declarations about `comap_domain` -/


section ComapDomain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
def comap_domain [HasZero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' «expr↑ » l.support)) : α →₀ M :=
  { Support := l.support.preimage f hf, toFun := fun a => l (f a),
    mem_support_to_fun :=
      by 
        intro a 
        simp only [finset.mem_def.symm, Finset.mem_preimage]
        exact l.mem_support_to_fun (f a) }

@[simp]
theorem comap_domain_apply [HasZero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' «expr↑ » l.support)) (a : α) :
  comap_domain f l hf a = l (f a) :=
  rfl

theorem sum_comap_domain [HasZero M] [AddCommMonoidₓ N] (f : α → β) (l : β →₀ M) (g : β → M → N)
  (hf : Set.BijOn f (f ⁻¹' «expr↑ » l.support) («expr↑ » l.support)) :
  (comap_domain f l hf.inj_on).Sum (g ∘ f) = l.sum g :=
  by 
    simp only [Sum, comap_domain_apply, · ∘ ·]
    simp [comap_domain, Finset.sum_preimage_of_bij f _ _ fun x => g x (l x)]

theorem eq_zero_of_comap_domain_eq_zero [AddCommMonoidₓ M] (f : α → β) (l : β →₀ M)
  (hf : Set.BijOn f (f ⁻¹' «expr↑ » l.support) («expr↑ » l.support)) : comap_domain f l hf.inj_on = 0 → l = 0 :=
  by 
    rw [←support_eq_empty, ←support_eq_empty, comap_domain]
    simp only [Finset.ext_iff, Finset.not_mem_empty, iff_falseₓ, mem_preimage]
    intro h a ha 
    cases' hf.2.2 ha with b hb 
    exact h b (hb.2.symm ▸ ha)

theorem map_domain_comap_domain [AddCommMonoidₓ M] (f : α → β) (l : β →₀ M) (hf : Function.Injective f)
  (hl : «expr↑ » l.support ⊆ Set.Range f) : map_domain f (comap_domain f l (hf.inj_on _)) = l :=
  by 
    ext a 
    byCases' h_cases : a ∈ Set.Range f
    ·
      rcases Set.mem_range.1 h_cases with ⟨b, hb⟩
      rw [hb.symm, map_domain_apply hf, comap_domain_apply]
    ·
      rw [map_domain_notin_range _ _ h_cases]
      byContra h_contr 
      apply h_cases (hl$ Finset.mem_coe.2$ mem_support_iff.2$ fun h => h_contr h.symm)

end ComapDomain

section Option

/-- Restrict a finitely supported function on `option α` to a finitely supported function on `α`. -/
def some [HasZero M] (f : Option α →₀ M) : α →₀ M :=
  f.comap_domain Option.some
    fun _ =>
      by 
        simp 

@[simp]
theorem some_apply [HasZero M] (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
theorem some_zero [HasZero M] : (0 : Option α →₀ M).some = 0 :=
  by 
    ext 
    simp 

@[simp]
theorem some_add [AddCommMonoidₓ M] (f g : Option α →₀ M) : (f+g).some = f.some+g.some :=
  by 
    ext 
    simp 

@[simp]
theorem some_single_none [HasZero M] (m : M) : (single none m : Option α →₀ M).some = 0 :=
  by 
    ext 
    simp 

@[simp]
theorem some_single_some [HasZero M] (a : α) (m : M) : (single (Option.some a) m : Option α →₀ M).some = single a m :=
  by 
    ext b 
    simp [single_apply]

@[toAdditive]
theorem prod_option_index [AddCommMonoidₓ M] [CommMonoidₓ N] (f : Option α →₀ M) (b : Option α → M → N)
  (h_zero : ∀ o, b o 0 = 1) (h_add : ∀ o m₁ m₂, b o (m₁+m₂) = b o m₁*b o m₂) :
  f.prod b = b none (f none)*f.some.prod fun a => b (Option.some a) :=
  by 
    apply induction_linear f
    ·
      simp [h_zero]
    ·
      intro f₁ f₂ h₁ h₂ 
      rw [Finsupp.prod_add_index, h₁, h₂, some_add, Finsupp.prod_add_index]
      simp only [h_add, Pi.add_apply, Finsupp.coe_add]
      rw [mul_mul_mul_commₓ]
      all_goals 
        simp [h_zero, h_add]
    ·
      rintro (_ | a) m <;> simp [h_zero, h_add]

theorem sum_option_index_smul [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (f : Option α →₀ R) (b : Option α → M) :
  (f.sum fun o r => r • b o) = (f none • b none)+f.some.sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

end Option

/-! ### Declarations about `equiv_congr_left` -/


section EquivCongrLeft

variable [HasZero M]

/-- Given `f : α ≃ β`, we can map `l : α →₀ M` to  `equiv_map_domain f l : β →₀ M` (computably)
by mapping the support forwards and the function backwards. -/
def equiv_map_domain (f : α ≃ β) (l : α →₀ M) : β →₀ M :=
  { Support := l.support.map f.to_embedding, toFun := fun a => l (f.symm a),
    mem_support_to_fun :=
      fun a =>
        by 
          simp only [Finset.mem_map_equiv, mem_support_to_fun] <;> rfl }

@[simp]
theorem equiv_map_domain_apply (f : α ≃ β) (l : α →₀ M) (b : β) : equiv_map_domain f l b = l (f.symm b) :=
  rfl

theorem equiv_map_domain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) : equiv_map_domain f.symm l a = l (f a) :=
  rfl

@[simp]
theorem equiv_map_domain_refl (l : α →₀ M) : equiv_map_domain (Equiv.refl _) l = l :=
  by 
    ext x <;> rfl

theorem equiv_map_domain_refl' : equiv_map_domain (Equiv.refl _) = @id (α →₀ M) :=
  by 
    ext x <;> rfl

theorem equiv_map_domain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
  equiv_map_domain (f.trans g) l = equiv_map_domain g (equiv_map_domain f l) :=
  by 
    ext x <;> rfl

theorem equiv_map_domain_trans' (f : α ≃ β) (g : β ≃ γ) :
  @equiv_map_domain _ _ M _ (f.trans g) = equiv_map_domain g ∘ equiv_map_domain f :=
  by 
    ext x <;> rfl

@[simp]
theorem equiv_map_domain_single (f : α ≃ β) (a : α) (b : M) : equiv_map_domain f (single a b) = single (f a) b :=
  by 
    ext x <;> simp only [single_apply, Equiv.apply_eq_iff_eq_symm_apply, equiv_map_domain_apply] <;> congr

@[simp]
theorem equiv_map_domain_zero {f : α ≃ β} : equiv_map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
  by 
    ext x <;> simp only [equiv_map_domain_apply, coe_zero, Pi.zero_apply]

theorem equiv_map_domain_eq_map_domain {M} [AddCommMonoidₓ M] (f : α ≃ β) (l : α →₀ M) :
  equiv_map_domain f l = map_domain f l :=
  by 
    ext x <;> simp [map_domain_equiv_apply]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `equiv.Pi_congr_left`. -/
def equiv_congr_left (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) :=
  by 
    refine' ⟨equiv_map_domain f, equiv_map_domain f.symm, fun f => _, fun f => _⟩ <;>
      ext x <;> simp only [equiv_map_domain_apply, Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

@[simp]
theorem equiv_congr_left_apply (f : α ≃ β) (l : α →₀ M) : equiv_congr_left f l = equiv_map_domain f l :=
  rfl

@[simp]
theorem equiv_congr_left_symm (f : α ≃ β) : (@equiv_congr_left _ _ M _ f).symm = equiv_congr_left f.symm :=
  rfl

end EquivCongrLeft

/-! ### Declarations about `filter` -/


section Filter

section HasZero

variable [HasZero M] (p : α → Prop) (f : α →₀ M)

/-- `filter p f` is the function which is `f a` if `p a` is true and 0 otherwise. -/
def filter (p : α → Prop) (f : α →₀ M) : α →₀ M :=
  { toFun := fun a => if p a then f a else 0, Support := f.support.filter fun a => p a,
    mem_support_to_fun :=
      fun a =>
        by 
          splitIfs <;>
            ·
              simp only [h, mem_filter, mem_support_iff]
              tauto }

theorem filter_apply (a : α) [D : Decidable (p a)] : f.filter p a = if p a then f a else 0 :=
  by 
    rw [Subsingleton.elimₓ D] <;> rfl

theorem filter_eq_indicator : «expr⇑ » (f.filter p) = Set.indicator { x | p x } f :=
  rfl

@[simp]
theorem filter_apply_pos {a : α} (h : p a) : f.filter p a = f a :=
  if_pos h

@[simp]
theorem filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0 :=
  if_neg h

@[simp]
theorem support_filter [D : DecidablePred p] : (f.filter p).Support = f.support.filter p :=
  by 
    rw [Subsingleton.elimₓ D] <;> rfl

theorem filter_zero : (0 : α →₀ M).filter p = 0 :=
  by 
    rw [←support_eq_empty, support_filter, support_zero, Finset.filter_empty]

@[simp]
theorem filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
  coe_fn_injective$
    by 
      simp [filter_eq_indicator, Set.subset_def, mem_support_single, h]

@[simp]
theorem filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 0 :=
  ext$
    by 
      simp [filter_eq_indicator, single_apply_eq_zero, @Imp.swap (p _), h]

end HasZero

theorem filter_pos_add_filter_neg [AddZeroClass M] (f : α →₀ M) (p : α → Prop) :
  (f.filter p+f.filter fun a => ¬p a) = f :=
  coe_fn_injective$ Set.indicator_self_add_compl { x | p x } f

end Filter

/-! ### Declarations about `frange` -/


section Frange

variable [HasZero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : Finset M :=
  Finset.image f f.support

theorem mem_frange {f : α →₀ M} {y : M} : y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y :=
  Finset.mem_image.trans
    ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩,
      fun ⟨hy, x, hx⟩ => ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_frange {f : α →₀ M} : (0 : M) ∉ f.frange :=
  fun H => (mem_frange.1 H).1 rfl

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} :=
  fun r hr =>
    let ⟨t, ht1, ht2⟩ := mem_frange.1 hr 
    ht2 ▸
      by 
        rw [single_apply] at ht2⊢ <;> splitIfs  at ht2⊢ <;> [exact Finset.mem_singleton_self _, cc]

end Frange

/-! ### Declarations about `subtype_domain` -/


section SubtypeDomain

section Zero

variable [HasZero M] {p : α → Prop}

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain (p : α → Prop) (f : α →₀ M) : Subtype p →₀ M :=
  ⟨f.support.subtype p, f ∘ coeₓ,
    fun a =>
      by 
        simp only [mem_subtype, mem_support_iff]⟩

@[simp]
theorem support_subtype_domain [D : DecidablePred p] {f : α →₀ M} :
  (subtype_domain p f).Support = f.support.subtype p :=
  by 
    rw [Subsingleton.elimₓ D] <;> rfl

@[simp]
theorem subtype_domain_apply {a : Subtype p} {v : α →₀ M} : (subtype_domain p v) a = v a.val :=
  rfl

@[simp]
theorem subtype_domain_zero : subtype_domain p (0 : α →₀ M) = 0 :=
  rfl

theorem subtype_domain_eq_zero_iff' {f : α →₀ M} : f.subtype_domain p = 0 ↔ ∀ x, p x → f x = 0 :=
  by 
    simpRw [←support_eq_empty, support_subtype_domain, subtype_eq_empty, not_mem_support_iff]

theorem subtype_domain_eq_zero_iff {f : α →₀ M} (hf : ∀ x _ : x ∈ f.support, p x) : f.subtype_domain p = 0 ↔ f = 0 :=
  subtype_domain_eq_zero_iff'.trans
    ⟨fun H => ext$ fun x => if hx : p x then H x hx else not_mem_support_iff.1$ mt (hf x) hx,
      fun H x _ =>
        by 
          simp [H]⟩

@[toAdditive]
theorem prod_subtype_domain_index [CommMonoidₓ N] {v : α →₀ M} {h : α → M → N} (hp : ∀ x _ : x ∈ v.support, p x) :
  ((v.subtype_domain p).Prod fun a b => h a b) = v.prod h :=
  prod_bij (fun p _ => p.val) (fun _ => mem_subtype.1) (fun _ _ => rfl) (fun _ _ _ _ => Subtype.eq)
    fun b hb => ⟨⟨b, hp b hb⟩, mem_subtype.2 hb, rfl⟩

end Zero

section AddZeroClass

variable [AddZeroClass M] {p : α → Prop} {v v' : α →₀ M}

@[simp]
theorem subtype_domain_add {v v' : α →₀ M} : (v+v').subtypeDomain p = v.subtype_domain p+v'.subtype_domain p :=
  ext$ fun _ => rfl

/-- `subtype_domain` but as an `add_monoid_hom`. -/
def subtype_domain_add_monoid_hom : (α →₀ M) →+ Subtype p →₀ M :=
  { toFun := subtype_domain p, map_zero' := subtype_domain_zero, map_add' := fun _ _ => subtype_domain_add }

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filter_add_hom (p : α → Prop) : (α →₀ M) →+ α →₀ M :=
  { toFun := filter p, map_zero' := filter_zero p,
    map_add' := fun f g => coe_fn_injective$ Set.indicator_add { x | p x } f g }

@[simp]
theorem filter_add {v v' : α →₀ M} : (v+v').filter p = v.filter p+v'.filter p :=
  (filter_add_hom p).map_add v v'

end AddZeroClass

section CommMonoidₓ

variable [AddCommMonoidₓ M] {p : α → Prop}

theorem subtype_domain_sum {s : Finset ι} {h : ι → α →₀ M} :
  (∑c in s, h c).subtypeDomain p = ∑c in s, (h c).subtypeDomain p :=
  (subtype_domain_add_monoid_hom : _ →+ Subtype p →₀ M).map_sum _ s

theorem subtype_domain_finsupp_sum [HasZero N] {s : β →₀ N} {h : β → N → α →₀ M} :
  (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtype_domain_sum

theorem filter_sum (s : Finset ι) (f : ι → α →₀ M) : (∑a in s, f a).filter p = ∑a in s, filter p (f a) :=
  (filter_add_hom p : (α →₀ M) →+ _).map_sum f s

theorem filter_eq_sum (p : α → Prop) [D : DecidablePred p] (f : α →₀ M) :
  f.filter p = ∑i in f.support.filter p, single i (f i) :=
  (f.filter p).sum_single.symm.trans$
    Finset.sum_congr
        (by 
          rw [Subsingleton.elimₓ D] <;> rfl)$
      fun x hx =>
        by 
          rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end CommMonoidₓ

section Groupₓ

variable [AddGroupₓ G] {p : α → Prop} {v v' : α →₀ G}

@[simp]
theorem subtype_domain_neg : (-v).subtypeDomain p = -v.subtype_domain p :=
  ext$ fun _ => rfl

@[simp]
theorem subtype_domain_sub : (v - v').subtypeDomain p = v.subtype_domain p - v'.subtype_domain p :=
  ext$ fun _ => rfl

@[simp]
theorem single_neg {a : α} {b : G} : single a (-b) = -single a b :=
  (single_add_hom a : G →+ _).map_neg b

@[simp]
theorem single_sub {a : α} {b₁ b₂ : G} : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (single_add_hom a : G →+ _).map_sub b₁ b₂

@[simp]
theorem erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
  (erase_add_hom a : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (erase_add_hom a : (_ →₀ G) →+ _).map_sub f₁ f₂

@[simp]
theorem filter_neg (p : α → Prop) (f : α →₀ G) : filter p (-f) = -filter p f :=
  (filter_add_hom p : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem filter_sub (p : α → Prop) (f₁ f₂ : α →₀ G) : filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
  (filter_add_hom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end Groupₓ

end SubtypeDomain

/-! ### Declarations relating `finsupp` to `multiset` -/


section Multiset

/-- Given `f : α →₀ ℕ`, `f.to_multiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `add_equiv`. -/
def to_multiset : (α →₀ ℕ) ≃+ Multiset α :=
  { toFun := fun f => f.sum fun a n => n • {a},
    invFun :=
      fun s =>
        ⟨s.to_finset, fun a => s.count a,
          fun a =>
            by 
              simp ⟩,
    left_inv :=
      fun f =>
        ext$
          fun a =>
            by 
              simp only [Sum, Multiset.count_sum', Multiset.count_singleton, mul_boole, coe_mk, Multiset.mem_to_finset,
                iff_selfₓ, not_not, mem_support_iff, ite_eq_left_iff, Ne.def, Multiset.count_eq_zero,
                Multiset.count_nsmul, Finset.sum_ite_eq, ite_not]
              exact Eq.symm,
    right_inv :=
      fun s =>
        by 
          simp only [Sum, coe_mk, Multiset.to_finset_sum_count_nsmul_eq],
    map_add' := fun f g => sum_add_index (fun a => zero_nsmul _) fun a => add_nsmul _ }

theorem to_multiset_zero : (0 : α →₀ ℕ).toMultiset = 0 :=
  rfl

theorem to_multiset_add (m n : α →₀ ℕ) : (m+n).toMultiset = m.to_multiset+n.to_multiset :=
  to_multiset.map_add m n

theorem to_multiset_apply (f : α →₀ ℕ) : f.to_multiset = f.sum fun a n => n • {a} :=
  rfl

@[simp]
theorem to_multiset_symm_apply (s : Multiset α) (x : α) : Finsupp.toMultiset.symm s x = s.count x :=
  rfl

@[simp]
theorem to_multiset_single (a : α) (n : ℕ) : to_multiset (single a n) = n • {a} :=
  by 
    rw [to_multiset_apply, sum_single_index] <;> apply zero_nsmul

theorem to_multiset_sum {ι : Type _} {f : ι → α →₀ ℕ} (s : Finset ι) :
  Finsupp.toMultiset (∑i in s, f i) = ∑i in s, Finsupp.toMultiset (f i) :=
  AddEquiv.map_sum _ _ _

theorem to_multiset_sum_single {ι : Type _} (s : Finset ι) (n : ℕ) :
  Finsupp.toMultiset (∑i in s, single i n) = n • s.val :=
  by 
    simpRw [to_multiset_sum, Finsupp.to_multiset_single, sum_nsmul, sum_multiset_singleton]

theorem card_to_multiset (f : α →₀ ℕ) : f.to_multiset.card = f.sum fun a => id :=
  by 
    simp [to_multiset_apply, AddMonoidHom.map_finsupp_sum, Function.id_def]

theorem to_multiset_map (f : α →₀ ℕ) (g : α → β) : f.to_multiset.map g = (f.map_domain g).toMultiset :=
  by 
    refine' f.induction _ _
    ·
      rw [to_multiset_zero, Multiset.map_zero, map_domain_zero, to_multiset_zero]
    ·
      intro a n f _ _ ih 
      rw [to_multiset_add, Multiset.map_add, ih, map_domain_add, map_domain_single, to_multiset_single, to_multiset_add,
        to_multiset_single, ←Multiset.coe_map_add_monoid_hom, (Multiset.mapAddMonoidHom g).map_nsmul]
      rfl

@[simp]
theorem prod_to_multiset [CommMonoidₓ M] (f : M →₀ ℕ) : f.to_multiset.prod = f.prod fun a n => a ^ n :=
  by 
    refine' f.induction _ _
    ·
      rw [to_multiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
    ·
      intro a n f _ _ ih 
      rw [to_multiset_add, Multiset.prod_add, ih, to_multiset_single, Finsupp.prod_add_index, Finsupp.prod_single_index,
        Multiset.prod_nsmul, Multiset.prod_singleton]
      ·
        exact pow_zeroₓ a
      ·
        exact pow_zeroₓ
      ·
        exact pow_addₓ

@[simp]
theorem to_finset_to_multiset [DecidableEq α] (f : α →₀ ℕ) : f.to_multiset.to_finset = f.support :=
  by 
    refine' f.induction _ _
    ·
      rw [to_multiset_zero, Multiset.to_finset_zero, support_zero]
    ·
      intro a n f ha hn ih 
      rw [to_multiset_add, Multiset.to_finset_add, ih, to_multiset_single, support_add_eq, support_single_ne_zero hn,
        Multiset.to_finset_nsmul _ _ hn, Multiset.to_finset_singleton]
      refine' Disjoint.mono_left support_single_subset _ 
      rwa [Finset.disjoint_singleton_left]

@[simp]
theorem count_to_multiset [DecidableEq α] (f : α →₀ ℕ) (a : α) : f.to_multiset.count a = f a :=
  calc f.to_multiset.count a = f.sum fun x n => (n • {x} : Multiset α).count a :=
    (Multiset.countAddMonoidHom a).map_sum _ f.support 
    _ = f.sum fun x n => n*({x} : Multiset α).count a :=
    by 
      simp only [Multiset.count_nsmul]
    _ = f a*({a} : Multiset α).count a :=
    sum_eq_single _
      (fun a' _ H =>
        by 
          simp only [Multiset.count_singleton, if_false, H.symm, mul_zero])
      fun H =>
        by 
          simp only [not_mem_support_iff.1 H, zero_mul]
    _ = f a :=
    by 
      rw [Multiset.count_singleton_self, mul_oneₓ]
    

theorem mem_support_multiset_sum [AddCommMonoidₓ M] {s : Multiset (α →₀ M)} (a : α) :
  a ∈ s.sum.support → ∃ (f : _)(_ : f ∈ s), a ∈ (f : α →₀ M).Support :=
  Multiset.induction_on s False.elim
    (by 
      intro f s ih ha 
      byCases' a ∈ f.support
      ·
        exact ⟨f, Multiset.mem_cons_self _ _, h⟩
      ·
        simp only [Multiset.sum_cons, mem_support_iff, add_apply, not_mem_support_iff.1 h, zero_addₓ] at ha 
        rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩
        exact ⟨f', Multiset.mem_cons_of_mem h₀, h₁⟩)

theorem mem_support_finset_sum [AddCommMonoidₓ M] {s : Finset ι} {h : ι → α →₀ M} (a : α)
  (ha : a ∈ (∑c in s, h c).Support) : ∃ (c : _)(_ : c ∈ s), a ∈ (h c).Support :=
  let ⟨f, hf, hfa⟩ := mem_support_multiset_sum a ha 
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

@[simp]
theorem mem_to_multiset (f : α →₀ ℕ) (i : α) : i ∈ f.to_multiset ↔ i ∈ f.support :=
  by 
    rw [←Multiset.count_ne_zero, Finsupp.count_to_multiset, Finsupp.mem_support_iff]

end Multiset

/-! ### Declarations about `curry` and `uncurry` -/


section CurryUncurry

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : α × β →₀ M) : α →₀ β →₀ M :=
  f.sum$ fun p c => single p.1 (single p.2 c)

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem curry_apply (f : «expr →₀ »(«expr × »(α, β), M)) (x : α) (y : β) : «expr = »(f.curry x y, f (x, y)) :=
begin
  have [] [":", expr ∀
   b : «expr × »(α, β), «expr = »(single b.fst (single b.snd (f b)) x y, if «expr = »(b, (x, y)) then f b else 0)] [],
  { rintros ["⟨", ident b₁, ",", ident b₂, "⟩"],
    simp [] [] [] ["[", expr single_apply, ",", expr ite_apply, ",", expr prod.ext_iff, ",", expr ite_and, "]"] [] [],
    split_ifs [] []; simp [] [] [] ["[", expr single_apply, ",", "*", "]"] [] [] },
  rw ["[", expr finsupp.curry, ",", expr sum_apply, ",", expr sum_apply, ",", expr finsupp.sum, ",", expr finset.sum_eq_single, ",", expr this, ",", expr if_pos rfl, "]"] [],
  { intros [ident b, ident hb, ident b_ne],
    rw ["[", expr this b, ",", expr if_neg b_ne, "]"] [] },
  { intros [ident hxy],
    rw ["[", expr this (x, y), ",", expr if_pos rfl, ",", expr not_mem_support_iff.mp hxy, "]"] [] }
end

theorem sum_curry_index (f : α × β →₀ M) (g : α → β → M → N) (hg₀ : ∀ a b, g a b 0 = 0)
  (hg₁ : ∀ a b c₀ c₁, g a b (c₀+c₁) = g a b c₀+g a b c₁) :
  (f.curry.sum fun a f => f.sum (g a)) = f.sum fun p c => g p.1 p.2 c :=
  by 
    rw [Finsupp.curry]
    trans
    ·
      exact
        sum_sum_index (fun a => sum_zero_index)
          fun a b₀ b₁ => sum_add_index (fun a => hg₀ _ _) fun c d₀ d₁ => hg₁ _ _ _ _ 
    congr 
    funext p c 
    trans
    ·
      exact sum_single_index sum_zero_index 
    exact sum_single_index (hg₀ _ _)

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ β →₀ M) : α × β →₀ M :=
  f.sum$ fun a g => g.sum$ fun b c => single (a, b) c

/-- `finsupp_prod_equiv` defines the `equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsupp_prod_equiv : (α × β →₀ M) ≃ (α →₀ β →₀ M) :=
  by 
    refine' ⟨Finsupp.curry, Finsupp.uncurry, fun f => _, fun f => _⟩ <;>
      simp only [Finsupp.curry, Finsupp.uncurry, sum_sum_index, sum_zero_index, sum_add_index, sum_single_index,
        single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, Prod.mk.eta,
        (single_sum _ _ _).symm, sum_single]

theorem filter_curry (f : α × β →₀ M) (p : α → Prop) : (f.filter fun a : α × β => p a.1).curry = f.curry.filter p :=
  by 
    rw [Finsupp.curry, Finsupp.curry, Finsupp.sum, Finsupp.sum, filter_sum, support_filter, sum_filter]
    refine' Finset.sum_congr rfl _ 
    rintro ⟨a₁, a₂⟩ ha 
    dsimp only 
    splitIfs
    ·
      rw [filter_apply_pos, filter_single_of_pos] <;> exact h
    ·
      rwa [filter_single_of_neg]

theorem support_curry [DecidableEq α] (f : α × β →₀ M) : f.curry.support ⊆ f.support.image Prod.fst :=
  by 
    rw [←Finset.bUnion_singleton]
    refine' Finset.Subset.trans support_sum _ 
    refine' Finset.bUnion_mono fun a _ => support_single_subset

end CurryUncurry

section Sum

/-- `finsupp.sum_elim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
def sum_elim {α β γ : Type _} [HasZero γ] (f : α →₀ γ) (g : β →₀ γ) : Sum α β →₀ γ :=
  on_finset (f.support.map ⟨_, Sum.inl_injective⟩ ∪ g.support.map ⟨_, Sum.inr_injective⟩) (Sum.elim f g)
    fun ab h =>
      by 
        cases' ab with a b <;> simp only [Sum.elim_inl, Sum.elim_inr] at h <;> simpa

@[simp]
theorem coe_sum_elim {α β γ : Type _} [HasZero γ] (f : α →₀ γ) (g : β →₀ γ) : «expr⇑ » (sum_elim f g) = Sum.elim f g :=
  rfl

theorem sum_elim_apply {α β γ : Type _} [HasZero γ] (f : α →₀ γ) (g : β →₀ γ) (x : Sum α β) :
  sum_elim f g x = Sum.elim f g x :=
  rfl

theorem sum_elim_inl {α β γ : Type _} [HasZero γ] (f : α →₀ γ) (g : β →₀ γ) (x : α) : sum_elim f g (Sum.inl x) = f x :=
  rfl

theorem sum_elim_inr {α β γ : Type _} [HasZero γ] (f : α →₀ γ) (g : β →₀ γ) (x : β) : sum_elim f g (Sum.inr x) = g x :=
  rfl

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symmApply]
def sum_finsupp_equiv_prod_finsupp {α β γ : Type _} [HasZero γ] : (Sum α β →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) :=
  { toFun :=
      fun f => ⟨f.comap_domain Sum.inl (Sum.inl_injective.InjOn _), f.comap_domain Sum.inr (Sum.inr_injective.InjOn _)⟩,
    invFun := fun fg => sum_elim fg.1 fg.2,
    left_inv :=
      fun f =>
        by 
          ext ab 
          cases' ab with a b <;> simp ,
    right_inv :=
      fun fg =>
        by 
          ext <;> simp  }

theorem fst_sum_finsupp_equiv_prod_finsupp {α β γ : Type _} [HasZero γ] (f : Sum α β →₀ γ) (x : α) :
  (sum_finsupp_equiv_prod_finsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sum_finsupp_equiv_prod_finsupp {α β γ : Type _} [HasZero γ] (f : Sum α β →₀ γ) (y : β) :
  (sum_finsupp_equiv_prod_finsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sum_finsupp_equiv_prod_finsupp_symm_inl {α β γ : Type _} [HasZero γ] (fg : (α →₀ γ) × (β →₀ γ)) (x : α) :
  (sum_finsupp_equiv_prod_finsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sum_finsupp_equiv_prod_finsupp_symm_inr {α β γ : Type _} [HasZero γ] (fg : (α →₀ γ) × (β →₀ γ)) (y : β) :
  (sum_finsupp_equiv_prod_finsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

variable [AddMonoidₓ M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symmApply]
def sum_finsupp_add_equiv_prod_finsupp {α β : Type _} : (Sum α β →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
  { sum_finsupp_equiv_prod_finsupp with
    map_add' :=
      by 
        intros 
        ext <;>
          simp only [Equiv.to_fun_as_coe, Prod.fst_add, Prod.snd_add, add_apply, snd_sum_finsupp_equiv_prod_finsupp,
            fst_sum_finsupp_equiv_prod_finsupp] }

theorem fst_sum_finsupp_add_equiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (x : α) :
  (sum_finsupp_add_equiv_prod_finsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sum_finsupp_add_equiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (y : β) :
  (sum_finsupp_add_equiv_prod_finsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sum_finsupp_add_equiv_prod_finsupp_symm_inl {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
  (sum_finsupp_add_equiv_prod_finsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sum_finsupp_add_equiv_prod_finsupp_symm_inr {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
  (sum_finsupp_add_equiv_prod_finsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section 

variable [Groupₓ G] [MulAction G α] [AddCommMonoidₓ M]

/--
Scalar multiplication by a group element g,
given by precomposition with the action of g⁻¹ on the domain.
-/
def comap_has_scalar : HasScalar G (α →₀ M) :=
  { smul :=
      fun g f =>
        f.comap_domain (fun a => g⁻¹ • a)
          fun a a' m m' h =>
            by 
              simpa [←mul_smul] using congr_argₓ (fun a => g • a) h }

attribute [local instance] comap_has_scalar

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is multiplicative in g.
-/
def comap_mul_action : MulAction G (α →₀ M) :=
  { one_smul :=
      fun f =>
        by 
          ext 
          dsimp [· • ·]
          simp ,
    mul_smul :=
      fun g g' f =>
        by 
          ext 
          dsimp [· • ·]
          simp [mul_smul] }

attribute [local instance] comap_mul_action

/--
Scalar multiplication by a group element,
given by precomposition with the action of g⁻¹ on the domain,
is additive in the second argument.
-/
def comap_distrib_mul_action : DistribMulAction G (α →₀ M) :=
  { smul_zero :=
      fun g =>
        by 
          ext 
          dsimp [· • ·]
          simp ,
    smul_add :=
      fun g f f' =>
        by 
          ext 
          dsimp [· • ·]
          simp  }

/--
Scalar multiplication by a group element on finitely supported functions on a group,
given by precomposition with the action of g⁻¹. -/
def comap_distrib_mul_action_self : DistribMulAction G (G →₀ M) :=
  @Finsupp.comapDistribMulAction G M G _ (Monoidₓ.toMulAction G) _

@[simp]
theorem comap_smul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  by 
    ext a' 
    dsimp [· • ·]
    byCases' h : g • a = a'
    ·
      subst h 
      simp [←mul_smul]
    ·
      simp [single_eq_of_ne h]
      rw [single_eq_of_ne]
      rintro rfl 
      simpa [←mul_smul] using h

@[simp]
theorem comap_smul_apply (g : G) (f : α →₀ M) (a : α) : (g • f) a = f (g⁻¹ • a) :=
  rfl

end 

section 

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : HasScalar R (α →₀ M) :=
  ⟨fun a v => v.map_range ((· • ·) a) (smul_zero _)⟩

/-!
Throughout this section, some `monoid` and `semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/


@[simp]
theorem coe_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (b : R) (v : α →₀ M) :
  «expr⇑ » (b • v) = b • v :=
  rfl

theorem smul_apply {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (b : R) (v : α →₀ M) (a : α) :
  (b • v) a = b • v a :=
  rfl

theorem _root_.is_smul_regular.finsupp {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {k : R}
  (hk : IsSmulRegular M k) : IsSmulRegular (α →₀ M) k :=
  fun _ _ h => ext$ fun i => hk (congr_funₓ h i)

instance [Monoidₓ R] [Nonempty α] [AddMonoidₓ M] [DistribMulAction R M] [HasFaithfulScalar R M] :
  HasFaithfulScalar R (α →₀ M) :=
  { eq_of_smul_eq_smul :=
      fun r₁ r₂ h =>
        let ⟨a⟩ := ‹Nonempty α›
        eq_of_smul_eq_smul$
          fun m : M =>
            by 
              simpa using congr_funₓ (h (single a m)) a }

variable (α M)

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R (α →₀ M) :=
  { smul := · • ·, smul_add := fun a x y => ext$ fun _ => smul_add _ _ _,
    one_smul := fun x => ext$ fun _ => one_smul _ _, mul_smul := fun r s x => ext$ fun _ => mul_smul _ _ _,
    smul_zero := fun x => ext$ fun _ => smul_zero _ }

instance [Monoidₓ R] [Monoidₓ S] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction S M] [HasScalar R S]
  [IsScalarTower R S M] : IsScalarTower R S (α →₀ M) :=
  { smul_assoc := fun r s a => ext$ fun _ => smul_assoc _ _ _ }

instance [Monoidₓ R] [Monoidₓ S] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction S M] [SmulCommClass R S M] :
  SmulCommClass R S (α →₀ M) :=
  { smul_comm := fun r s a => ext$ fun _ => smul_comm _ _ _ }

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module R (α →₀ M) :=
  { Finsupp.distribMulAction α M with smul := · • ·, zero_smul := fun x => ext$ fun _ => zero_smul _ _,
    add_smul := fun a x y => ext$ fun _ => add_smul _ _ _ }

variable {α M} {R}

theorem support_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {b : R} {g : α →₀ M} :
  (b • g).Support ⊆ g.support :=
  fun a =>
    by 
      simp only [smul_apply, mem_support_iff, Ne.def]
      exact mt fun h => h.symm ▸ smul_zero _

section 

variable {p : α → Prop}

@[simp]
theorem filter_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {b : R} {v : α →₀ M} :
  (b • v).filter p = b • v.filter p :=
  coe_fn_injective$ Set.indicator_smul { x | p x } b v

end 

theorem map_domain_smul {_ : Monoidₓ R} [AddCommMonoidₓ M] [DistribMulAction R M] {f : α → β} (b : R) (v : α →₀ M) :
  map_domain f (b • v) = b • map_domain f v :=
  by 
    change map_domain f (map_range _ _ _) = map_range _ _ _ 
    apply Finsupp.induction v
    ·
      simp only [map_domain_zero, map_range_zero]
    intro a b v' hv₁ hv₂ IH 
    rw [map_range_add, map_domain_add, IH, map_domain_add, map_range_add, map_range_single, map_domain_single,
        map_domain_single, map_range_single] <;>
      apply smul_add

@[simp]
theorem smul_single {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (c : R) (a : α) (b : M) :
  c • Finsupp.single a b = Finsupp.single a (c • b) :=
  map_range_single

@[simp]
theorem smul_single' {_ : Semiringₓ R} (c : R) (a : α) (b : R) : c • Finsupp.single a b = Finsupp.single a (c*b) :=
  smul_single _ _ _

-- error in Data.Finsupp.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_range_smul
{_ : monoid R}
[add_monoid M]
[distrib_mul_action R M]
[add_monoid N]
[distrib_mul_action R N]
{f : M → N}
{hf : «expr = »(f 0, 0)}
(c : R)
(v : «expr →₀ »(α, M))
(hsmul : ∀
 x, «expr = »(f «expr • »(c, x), «expr • »(c, f x))) : «expr = »(map_range f hf «expr • »(c, v), «expr • »(c, map_range f hf v)) :=
begin
  erw ["<-", expr map_range_comp] [],
  have [] [":", expr «expr = »(«expr ∘ »(f, ((«expr • »)) c), «expr ∘ »(((«expr • »)) c, f))] [":=", expr funext hsmul],
  simp_rw [expr this] [],
  apply [expr map_range_comp],
  rw ["[", expr function.comp_apply, ",", expr smul_zero, ",", expr hf, "]"] []
end

theorem smul_single_one [Semiringₓ R] (a : α) (b : R) : b • single a 1 = single a b :=
  by 
    rw [smul_single, smul_eq_mul, mul_oneₓ]

end 

theorem sum_smul_index [Semiringₓ R] [AddCommMonoidₓ M] {g : α →₀ R} {b : R} {h : α → R → M} (h0 : ∀ i, h i 0 = 0) :
  (b • g).Sum h = g.sum fun i a => h i (b*a) :=
  Finsupp.sum_map_range_index h0

theorem sum_smul_index' [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] [AddCommMonoidₓ N] {g : α →₀ M} {b : R}
  {h : α → M → N} (h0 : ∀ i, h i 0 = 0) : (b • g).Sum h = g.sum fun i c => h i (b • c) :=
  Finsupp.sum_map_range_index h0

/-- A version of `finsupp.sum_smul_index'` for bundled additive maps. -/
theorem sum_smul_index_add_monoid_hom [Monoidₓ R] [AddMonoidₓ M] [AddCommMonoidₓ N] [DistribMulAction R M] {g : α →₀ M}
  {b : R} {h : α → M →+ N} : ((b • g).Sum fun a => h a) = g.sum fun i c => h i (b • c) :=
  sum_map_range_index fun i => (h i).map_zero

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] {ι : Type _} [NoZeroSmulDivisors R M] :
  NoZeroSmulDivisors R (ι →₀ M) :=
  ⟨fun c f h =>
      or_iff_not_imp_left.mpr fun hc => Finsupp.ext fun i => (smul_eq_zero.mp (Finsupp.ext_iff.mp h i)).resolve_left hc⟩

section DistribMulActionHom

variable [Semiringₓ R]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [DistribMulAction R M] [DistribMulAction R N]

/-- `finsupp.single` as a `distrib_mul_action_hom`.

See also `finsupp.lsingle` for the version as a linear map. -/
def distrib_mul_action_hom.single (a : α) : M →+[R] α →₀ M :=
  { single_add_hom a with
    map_smul' :=
      fun k m =>
        by 
          simp only [AddMonoidHom.to_fun_eq_coe, single_add_hom_apply, smul_single] }

theorem distrib_mul_action_hom_ext {f g : (α →₀ M) →+[R] N} (h : ∀ a : α m : M, f (single a m) = g (single a m)) :
  f = g :=
  DistribMulActionHom.to_add_monoid_hom_injective$ add_hom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem distrib_mul_action_hom_ext' {f g : (α →₀ M) →+[R] N}
  (h : ∀ a : α, f.comp (distrib_mul_action_hom.single a) = g.comp (distrib_mul_action_hom.single a)) : f = g :=
  distrib_mul_action_hom_ext$ fun a => DistribMulActionHom.congr_fun (h a)

end DistribMulActionHom

section 

variable [HasZero R]

/-- The `finsupp` version of `pi.unique`. -/
instance unique_of_right [Subsingleton R] : Unique (α →₀ R) :=
  { Finsupp.inhabited with uniq := fun l => ext$ fun i => Subsingleton.elimₓ _ _ }

/-- The `finsupp` version of `pi.unique_of_is_empty`. -/
instance unique_of_left [IsEmpty α] : Unique (α →₀ R) :=
  { Finsupp.inhabited with uniq := fun l => ext isEmptyElim }

end 

/-- Given an `add_comm_monoid M` and `s : set α`, `restrict_support_equiv s M` is the `equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
def restrict_support_equiv (s : Set α) (M : Type _) [AddCommMonoidₓ M] :
  { f : α →₀ M // «expr↑ » f.support ⊆ s } ≃ (s →₀ M) :=
  by 
    refine' ⟨fun f => subtype_domain (fun x => x ∈ s) f.1, fun f => ⟨f.map_domain Subtype.val, _⟩, _, _⟩
    ·
      refine' Set.Subset.trans (Finset.coe_subset.2 map_domain_support) _ 
      rw [Finset.coe_image, Set.image_subset_iff]
      exact fun x hx => x.2
    ·
      rintro ⟨f, hf⟩
      apply Subtype.eq 
      ext a 
      dsimp only 
      refine' Classical.by_cases (fun h : a ∈ Set.Range (Subtype.val : s → α) => _) fun h => _
      ·
        rcases h with ⟨x, rfl⟩
        rw [map_domain_apply Subtype.val_injective, subtype_domain_apply]
      ·
        convert map_domain_notin_range _ _ h 
        rw [←not_mem_support_iff]
        refine' mt _ h 
        exact fun ha => ⟨⟨a, hf ha⟩, rfl⟩
    ·
      intro f 
      ext ⟨a, ha⟩
      dsimp only 
      rw [subtype_domain_apply, map_domain_apply Subtype.val_injective]

/-- Given `add_comm_monoid M` and `e : α ≃ β`, `dom_congr e` is the corresponding `equiv` between
`α →₀ M` and `β →₀ M`.

This is `finsupp.equiv_congr_left` as an `add_equiv`. -/
@[simps apply]
protected def dom_congr [AddCommMonoidₓ M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) :=
  { toFun := equiv_map_domain e, invFun := equiv_map_domain e.symm,
    left_inv :=
      fun v =>
        by 
          simp only [←equiv_map_domain_trans, Equiv.self_trans_symm]
          exact equiv_map_domain_refl _,
    right_inv :=
      by 
        intro v 
        simp only [←equiv_map_domain_trans, Equiv.symm_trans_self]
        exact equiv_map_domain_refl _,
    map_add' :=
      fun a b =>
        by 
          simp only [equiv_map_domain_eq_map_domain] <;> exact map_domain_add }

@[simp]
theorem dom_congr_refl [AddCommMonoidₓ M] : Finsupp.domCongr (Equiv.refl α) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext$ fun _ => equiv_map_domain_refl _

@[simp]
theorem dom_congr_symm [AddCommMonoidₓ M] (e : α ≃ β) :
  (Finsupp.domCongr e).symm = (Finsupp.domCongr e.symm : (β →₀ M) ≃+ (α →₀ M)) :=
  AddEquiv.ext$ fun _ => rfl

@[simp]
theorem dom_congr_trans [AddCommMonoidₓ M] (e : α ≃ β) (f : β ≃ γ) :
  (Finsupp.domCongr e).trans (Finsupp.domCongr f) = (Finsupp.domCongr (e.trans f) : (α →₀ M) ≃+ _) :=
  AddEquiv.ext$ fun _ => (equiv_map_domain_trans _ _ _).symm

end Finsupp

namespace Finsupp

/-! ### Declarations about sigma types -/


section Sigma

variable {αs : ι → Type _} [HasZero M] (l : (Σi, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `finsupp` version of `sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
  l.comap_domain (Sigma.mk i) fun x1 x2 _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

theorem split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ :=
  by 
    dunfold split 
    rw [comap_domain_apply]

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def split_support : Finset ι :=
  l.support.image Sigma.fst

theorem mem_split_support_iff_nonzero (i : ι) : i ∈ split_support l ↔ split l i ≠ 0 :=
  by 
    rw [split_support, mem_image, Ne.def, ←support_eq_empty, ←Ne.def, ←Finset.nonempty_iff_ne_empty, split,
      comap_domain, Finset.Nonempty]
    simp only [exists_prop, Finset.mem_preimage, exists_and_distrib_right, exists_eq_right, mem_support_iff,
      Sigma.exists, Ne.def]

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def split_comp [HasZero N] (g : ∀ i, (αs i →₀ M) → N) (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N :=
  { Support := split_support l, toFun := fun i => g i (split l i),
    mem_support_to_fun :=
      by 
        intro i 
        rw [mem_split_support_iff_nonzero, not_iff_not, hg] }

theorem sigma_support : l.support = l.split_support.sigma fun i => (l.split i).Support :=
  by 
    simp only [Finset.ext_iff, split_support, split, comap_domain, mem_image, mem_preimage, Sigma.forall, mem_sigma] <;>
      tauto

theorem sigma_sum [AddCommMonoidₓ N] (f : (Σi : ι, αs i) → M → N) :
  l.sum f = ∑i in split_support l, (split l i).Sum fun a : αs i b => f ⟨i, a⟩ b :=
  by 
    simp only [Sum, sigma_support, sum_sigma, split_apply]

variable {η : Type _} [Fintype η] {ιs : η → Type _} [HasZero α]

/-- On a `fintype η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `finsupp` version of `equiv.Pi_curry`. -/
noncomputable def sigma_finsupp_equiv_pi_finsupp : ((Σj, ιs j) →₀ α) ≃ ∀ j, ιs j →₀ α :=
  { toFun := split,
    invFun :=
      fun f =>
        on_finset (Finset.univ.Sigma fun j => (f j).Support) (fun ji => f ji.1 ji.2)
          fun g hg => Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩,
    left_inv :=
      fun f =>
        by 
          ext 
          simp [split],
    right_inv :=
      fun f =>
        by 
          ext 
          simp [split] }

@[simp]
theorem sigma_finsupp_equiv_pi_finsupp_apply (f : (Σj, ιs j) →₀ α) j i :
  sigma_finsupp_equiv_pi_finsupp f j i = f ⟨j, i⟩ :=
  rfl

/-- On a `fintype η`, `finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `add_equiv` version of `finsupp.sigma_finsupp_equiv_pi_finsupp`.
-/
noncomputable def sigma_finsupp_add_equiv_pi_finsupp {α : Type _} {ιs : η → Type _} [AddMonoidₓ α] :
  ((Σj, ιs j) →₀ α) ≃+ ∀ j, ιs j →₀ α :=
  { sigma_finsupp_equiv_pi_finsupp with
    map_add' :=
      fun f g =>
        by 
          ext 
          simp  }

@[simp]
theorem sigma_finsupp_add_equiv_pi_finsupp_apply {α : Type _} {ιs : η → Type _} [AddMonoidₓ α] (f : (Σj, ιs j) →₀ α) j
  i : sigma_finsupp_add_equiv_pi_finsupp f j i = f ⟨j, i⟩ :=
  rfl

end Sigma

end Finsupp

/-! ### Declarations relating `multiset` to `finsupp` -/


namespace Multiset

/-- Given a multiset `s`, `s.to_finsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
def to_finsupp : Multiset α ≃+ (α →₀ ℕ) :=
  Finsupp.toMultiset.symm

@[simp]
theorem to_finsupp_support [D : DecidableEq α] (s : Multiset α) : s.to_finsupp.support = s.to_finset :=
  by 
    rw [Subsingleton.elimₓ D] <;> rfl

@[simp]
theorem to_finsupp_apply [D : DecidableEq α] (s : Multiset α) (a : α) : to_finsupp s a = s.count a :=
  by 
    rw [Subsingleton.elimₓ D] <;> rfl

theorem to_finsupp_zero : to_finsupp (0 : Multiset α) = 0 :=
  AddEquiv.map_zero _

theorem to_finsupp_add (s t : Multiset α) : to_finsupp (s+t) = to_finsupp s+to_finsupp t :=
  to_finsupp.map_add s t

@[simp]
theorem to_finsupp_singleton (a : α) : to_finsupp ({a} : Multiset α) = Finsupp.single a 1 :=
  Finsupp.toMultiset.symm_apply_eq.2$
    by 
      simp 

@[simp]
theorem to_finsupp_to_multiset (s : Multiset α) : s.to_finsupp.to_multiset = s :=
  Finsupp.toMultiset.apply_symm_apply s

theorem to_finsupp_eq_iff {s : Multiset α} {f : α →₀ ℕ} : s.to_finsupp = f ↔ s = f.to_multiset :=
  Finsupp.toMultiset.symm_apply_eq

end Multiset

@[simp]
theorem Finsupp.to_multiset_to_finsupp (f : α →₀ ℕ) : f.to_multiset.to_finsupp = f :=
  Finsupp.toMultiset.symm_apply_apply f

/-! ### Declarations about order(ed) instances on `finsupp` -/


namespace Finsupp

instance [Preorderₓ M] [HasZero M] : Preorderₓ (α →₀ M) :=
  { le := fun f g => ∀ s, f s ≤ g s, le_refl := fun f s => le_reflₓ _,
    le_trans := fun f g h Hfg Hgh s => le_transₓ (Hfg s) (Hgh s) }

instance [PartialOrderₓ M] [HasZero M] : PartialOrderₓ (α →₀ M) :=
  { Finsupp.preorder with le_antisymm := fun f g hfg hgf => ext$ fun s => le_antisymmₓ (hfg s) (hgf s) }

instance [OrderedAddCommMonoid M] : OrderedAddCommMonoid (α →₀ M) :=
  { Finsupp.addCommMonoid, Finsupp.partialOrder with add_le_add_left := fun a b h c s => add_le_add_left (h s) (c s) }

instance [OrderedCancelAddCommMonoid M] : OrderedCancelAddCommMonoid (α →₀ M) :=
  { Finsupp.addCommMonoid, Finsupp.partialOrder with add_le_add_left := fun a b h c s => add_le_add_left (h s) (c s),
    le_of_add_le_add_left := fun a b c h s => le_of_add_le_add_left (h s),
    add_left_cancel := fun a b c h => ext$ fun s => add_left_cancelₓ (ext_iff.1 h s) }

instance [OrderedAddCommMonoid M] [ContravariantClass M M (·+·) (· ≤ ·)] :
  ContravariantClass (α →₀ M) (α →₀ M) (·+·) (· ≤ ·) :=
  ⟨fun f g h H x => le_of_add_le_add_left$ H x⟩

theorem le_def [Preorderₓ M] [HasZero M] {f g : α →₀ M} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl

theorem le_iff' [CanonicallyOrderedAddMonoid M] (f g : α →₀ M) {t : Finset α} (hf : f.support ⊆ t) :
  f ≤ g ↔ ∀ s _ : s ∈ t, f s ≤ g s :=
  ⟨fun h s hs => h s,
    fun h s => if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

theorem le_iff [CanonicallyOrderedAddMonoid M] (f g : α →₀ M) : f ≤ g ↔ ∀ s _ : s ∈ f.support, f s ≤ g s :=
  le_iff' f g (subset.refl _)

instance decidable_le [CanonicallyOrderedAddMonoid M] [DecidableRel (@LE.le M _)] : DecidableRel (@LE.le (α →₀ M) _) :=
  fun f g => decidableOfIff _ (le_iff f g).symm

@[simp]
theorem single_le_iff [CanonicallyOrderedAddMonoid M] {i : α} {x : M} {f : α →₀ M} : single i x ≤ f ↔ x ≤ f i :=
  (le_iff' _ _ support_single_subset).trans$
    by 
      simp 

@[simp]
theorem add_eq_zero_iff [CanonicallyOrderedAddMonoid M] (f g : α →₀ M) : (f+g) = 0 ↔ f = 0 ∧ g = 0 :=
  by 
    simp [ext_iff, forall_and_distrib]

/-- `finsupp.to_multiset` as an order isomorphism. -/
def order_iso_multiset : (α →₀ ℕ) ≃o Multiset α :=
  { toEquiv := to_multiset.toEquiv,
    map_rel_iff' :=
      fun f g =>
        by 
          simp [Multiset.le_iff_count, le_def] }

@[simp]
theorem coe_order_iso_multiset : «expr⇑ » (@order_iso_multiset α) = to_multiset :=
  rfl

@[simp]
theorem coe_order_iso_multiset_symm : «expr⇑ » (@order_iso_multiset α).symm = Multiset.toFinsupp :=
  rfl

theorem to_multiset_strict_mono : StrictMono (@to_multiset α) :=
  order_iso_multiset.StrictMono

theorem sum_id_lt_of_lt (m n : α →₀ ℕ) (h : m < n) : (m.sum fun _ => id) < n.sum fun _ => id :=
  by 
    rw [←card_to_multiset, ←card_to_multiset]
    apply Multiset.card_lt_of_lt 
    exact to_multiset_strict_mono h

variable (α)

/-- The order on `σ →₀ ℕ` is well-founded.-/
theorem lt_wf : WellFounded (@LT.lt (α →₀ ℕ) _) :=
  Subrelation.wfₓ sum_id_lt_of_lt$ InvImage.wfₓ _ Nat.lt_wf

variable {α}

/-! Declarations about subtraction on `finsupp` with codomain a `canonically_ordered_add_monoid`.

Some of these lemmas are used to develop the partial derivative on `mv_polynomial`. -/


section NatSub

section CanonicallyOrderedMonoid

instance [CanonicallyOrderedAddMonoid M] : OrderBot (α →₀ M) :=
  { bot := 0,
    bot_le :=
      by 
        simp [Finsupp.le_def] }

variable [CanonicallyOrderedAddMonoid M] [Sub M] [HasOrderedSub M]

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : Sub (α →₀ M) :=
  ⟨zip_with (fun m n => m - n) (tsub_self 0)⟩

@[simp]
theorem coe_tsub (g₁ g₂ : α →₀ M) : «expr⇑ » (g₁ - g₂) = g₁ - g₂ :=
  rfl

theorem tsub_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a :=
  rfl

instance : CanonicallyOrderedAddMonoid (α →₀ M) :=
  { Finsupp.orderBot,
    (by 
      infer_instance :
    OrderedAddCommMonoid (α →₀ M)) with
    le_iff_exists_add :=
      by 
        intro f g 
        split 
        ·
          intro H 
          use g - f 
          ext x 
          symm 
          exact add_tsub_cancel_of_le (H x)
        ·
          rintro ⟨g, rfl⟩ x 
          exact self_le_add_right (f x) (g x) }

instance : HasOrderedSub (α →₀ M) :=
  ⟨fun n m k => forall_congrₓ$ fun x => tsub_le_iff_right⟩

@[simp]
theorem single_tsub {a : α} {n₁ n₂ : M} : single a (n₁ - n₂) = single a n₁ - single a n₂ :=
  by 
    ext f 
    byCases' h : a = f
    ·
      rw [h, tsub_apply, single_eq_same, single_eq_same, single_eq_same]
    rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

end CanonicallyOrderedMonoid

/-! Some lemmas specifically about `ℕ`. -/


theorem sub_single_one_add {a : α} {u u' : α →₀ ℕ} (h : u a ≠ 0) : ((u - single a 1)+u') = (u+u') - single a 1 :=
  tsub_add_eq_add_tsub$ single_le_iff.mpr$ Nat.one_le_iff_ne_zero.mpr h

theorem add_sub_single_one {a : α} {u u' : α →₀ ℕ} (h : u' a ≠ 0) : (u+u' - single a 1) = (u+u') - single a 1 :=
  (add_tsub_assoc_of_le (single_le_iff.mpr$ Nat.one_le_iff_ne_zero.mpr h) _).symm

end NatSub

end Finsupp

namespace Multiset

theorem to_finsuppstrict_mono : StrictMono (@to_finsupp α) :=
  Finsupp.orderIsoMultiset.symm.StrictMono

end Multiset

