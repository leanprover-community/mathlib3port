import Mathbin.Data.Set.Lattice
import Mathbin.Logic.Relation

/-!
# Relations holding pairwise

This file defines pairwise relations and pairwise disjoint indexed sets.

## Main declarations

* `pairwise`: `pairwise r` states that `r i j` for all `i ≠ j`.
* `set.pairwise`: `s.pairwise r` states that `r i j` for all `i ≠ j` with `i, j ∈ s`.
* `set.pairwise_disjoint`: `s.pairwise_disjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `disjoint`.
-/


open Set

variable {α ι ι' : Type _} {r p q : α → α → Prop}

section Pairwise

variable {f : ι → α} {s t u : Set α} {a b : α}

/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
def Pairwise (r : α → α → Prop) :=
  ∀ i j, i ≠ j → r i j

theorem Pairwise.mono (hr : Pairwise r) (h : ∀ ⦃i j⦄, r i j → p i j) : Pairwise p := fun i j hij => h $ hr i j hij

theorem pairwise_on_bool (hr : Symmetric r) {a b : α} : Pairwise (r on fun c => cond c a b) ↔ r a b := by
  simpa [Pairwise, Function.onFun] using @hr a b

theorem pairwise_disjoint_on_bool [SemilatticeInf α] [OrderBot α] {a b : α} :
    Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b :=
  pairwise_on_bool Disjoint.symm

theorem Symmetric.pairwise_on [LinearOrderₓ ι] (hr : Symmetric r) (f : ι → α) :
    Pairwise (r on f) ↔ ∀ m n, m < n → r (f m) (f n) :=
  ⟨fun h m n hmn => h m n hmn.ne, fun h m n hmn => by
    obtain hmn' | hmn' := hmn.lt_or_lt
    · exact h _ _ hmn'
      
    · exact hr (h _ _ hmn')
      ⟩

theorem pairwise_disjoint_on [SemilatticeInf α] [OrderBot α] [LinearOrderₓ ι] (f : ι → α) :
    Pairwise (Disjoint on f) ↔ ∀ m n, m < n → Disjoint (f m) (f n) :=
  Symmetric.pairwise_on Disjoint.symm f

namespace Set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
protected def Pairwise (s : Set α) (r : α → α → Prop) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y

theorem pairwise_of_forall (s : Set α) (r : α → α → Prop) (h : ∀ a b, r a b) : s.pairwise r := fun a _ b _ _ => h a b

theorem pairwise.imp_on (h : s.pairwise r) (hrp : s.pairwise fun ⦃a b : α⦄ => r a b → p a b) : s.pairwise p :=
  fun a ha b hb hab => hrp ha hb hab $ h ha hb hab

theorem pairwise.imp (h : s.pairwise r) (hpq : ∀ ⦃a b : α⦄, r a b → p a b) : s.pairwise p :=
  h.imp_on $ pairwise_of_forall s _ hpq

theorem Pairwise.mono (h : t ⊆ s) (hs : s.pairwise r) : t.pairwise r := fun x xt y yt => hs (h xt) (h yt)

theorem pairwise.mono' (H : r ≤ p) (hr : s.pairwise r) : s.pairwise p :=
  hr.imp H

theorem pairwise_top (s : Set α) : s.pairwise ⊤ :=
  pairwise_of_forall s _ fun a b => trivialₓ

protected theorem subsingleton.pairwise (h : s.subsingleton) (r : α → α → Prop) : s.pairwise r := fun x hx y hy hne =>
  (hne (h hx hy)).elim

@[simp]
theorem pairwise_empty (r : α → α → Prop) : (∅ : Set α).Pairwise r :=
  subsingleton_empty.Pairwise r

@[simp]
theorem pairwise_singleton (a : α) (r : α → α → Prop) : Set.Pairwise {a} r :=
  subsingleton_singleton.Pairwise r

theorem nonempty.pairwise_iff_exists_forall [IsEquiv α r] {s : Set ι} (hs : s.nonempty) :
    s.pairwise (r on f) ↔ ∃ z, ∀, ∀ x ∈ s, ∀, r (f x) z := by
  fconstructor
  · rcases hs with ⟨y, hy⟩
    refine' fun H => ⟨f y, fun x hx => _⟩
    rcases eq_or_ne x y with (rfl | hne)
    · apply IsRefl.refl
      
    · exact H hx hy hne
      
    
  · rintro ⟨z, hz⟩ x hx y hy hne
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (IsSymm.symm _ _ $ hz _ hy)
    

/-- For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.pairwise_eq_iff_exists_eq` for a version that assumes `[nonempty ι]` instead of
`set.nonempty s`. -/
theorem nonempty.pairwise_eq_iff_exists_eq {s : Set α} (hs : s.nonempty) {f : α → ι} :
    (s.pairwise fun x y => f x = f y) ↔ ∃ z, ∀, ∀ x ∈ s, ∀, f x = z :=
  hs.pairwise_iff_exists_forall

theorem pairwise_iff_exists_forall [Nonempty ι] (s : Set α) (f : α → ι) {r : ι → ι → Prop} [IsEquiv ι r] :
    s.pairwise (r on f) ↔ ∃ z, ∀, ∀ x ∈ s, ∀, r (f x) z := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
    
  · exact hne.pairwise_iff_exists_forall
    

/-- A function `f : α → ι` with nonempty codomain takes pairwise equal values on a set `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.nonempty.pairwise_eq_iff_exists_eq` for a version that assumes `set.nonempty s` instead of
`[nonempty ι]`. -/
theorem pairwise_eq_iff_exists_eq [Nonempty ι] (s : Set α) (f : α → ι) :
    (s.pairwise fun x y => f x = f y) ↔ ∃ z, ∀, ∀ x ∈ s, ∀, f x = z :=
  pairwise_iff_exists_forall s f

theorem pairwise_union :
    (s ∪ t).Pairwise r ↔ s.pairwise r ∧ t.pairwise r ∧ ∀, ∀ a ∈ s, ∀, ∀ b ∈ t, ∀, a ≠ b → r a b ∧ r b a := by
  simp only [Set.Pairwise, mem_union_eq, or_imp_distrib, forall_and_distrib]
  exact
    ⟨fun H => ⟨H.1.1, H.2.2, H.2.1, fun x hx y hy hne => H.1.2 y hy x hx hne.symm⟩, fun H =>
      ⟨⟨H.1, fun x hx y hy hne => H.2.2.2 y hy x hx hne.symm⟩, H.2.2.1, H.2.1⟩⟩

theorem pairwise_union_of_symmetric (hr : Symmetric r) :
    (s ∪ t).Pairwise r ↔ s.pairwise r ∧ t.pairwise r ∧ ∀, ∀ a ∈ s, ∀, ∀ b ∈ t, ∀, a ≠ b → r a b :=
  pairwise_union.trans $ by
    simp only [hr.iff, and_selfₓ]

theorem pairwise_insert : (insert a s).Pairwise r ↔ s.pairwise r ∧ ∀, ∀ b ∈ s, ∀, a ≠ b → r a b ∧ r b a := by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_andₓ, mem_singleton_iff, forall_eq]

theorem pairwise_insert_of_symmetric (hr : Symmetric r) :
    (insert a s).Pairwise r ↔ s.pairwise r ∧ ∀, ∀ b ∈ s, ∀, a ≠ b → r a b := by
  simp only [pairwise_insert, hr.iff a, and_selfₓ]

theorem pairwise_pair : Set.Pairwise {a, b} r ↔ a ≠ b → r a b ∧ r b a := by
  simp [pairwise_insert]

theorem pairwise_pair_of_symmetric (hr : Symmetric r) : Set.Pairwise {a, b} r ↔ a ≠ b → r a b := by
  simp [pairwise_insert_of_symmetric hr]

theorem pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise r := by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]

theorem pairwise.on_injective (hs : s.pairwise r) (hf : Function.Injective f) (hfs : ∀ x, f x ∈ s) :
    Pairwise (r on f) := fun i j hij => hs (hfs i) (hfs j) (hf.ne hij)

theorem inj_on.pairwise_image {s : Set ι} (h : s.inj_on f) : (f '' s).Pairwise r ↔ s.pairwise (r on f) := by
  simp (config := { contextual := true })[h.eq_iff, Set.Pairwise]

theorem pairwise_Union {f : ι → Set α} (h : Directed (· ⊆ ·) f) : (⋃ n, f n).Pairwise r ↔ ∀ n, (f n).Pairwise r := by
  constructor
  · intro H n
    exact Pairwise.mono (subset_Union _ _) H
    
  · intro H i hi j hj hij
    rcases mem_Union.1 hi with ⟨m, hm⟩
    rcases mem_Union.1 hj with ⟨n, hn⟩
    rcases h m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij
    

theorem pairwise_sUnion {r : α → α → Prop} {s : Set (Set α)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀s).Pairwise r ↔ ∀, ∀ a ∈ s, ∀, Set.Pairwise a r := by
  rw [sUnion_eq_Union, pairwise_Union h.directed_coe, SetCoe.forall]
  rfl

end Set

theorem Pairwise.set_pairwise (h : Pairwise r) (s : Set α) : s.pairwise r := fun x hx y hy => h x y

end Pairwise

theorem pairwise_subtype_iff_pairwise_set {α : Type _} (s : Set α) (r : α → α → Prop) :
    (Pairwise fun x : s y : s => r x y) ↔ s.pairwise r := by
  constructor
  · intro h x hx y hy hxy
    exact
      h ⟨x, hx⟩ ⟨y, hy⟩
        (by
          simpa only [Subtype.mk_eq_mk, Ne.def])
    
  · rintro h ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk, Ne.def] at hxy
    exact h hx hy hxy
    

alias pairwise_subtype_iff_pairwise_set ↔ Pairwise.set_of_subtype Set.Pairwise.subtype

namespace Set

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {s t : Set ι} {f g : ι → α}

/-- A set is `pairwise_disjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint. -/
def pairwise_disjoint (s : Set ι) (f : ι → α) : Prop :=
  s.pairwise (Disjoint on f)

theorem pairwise_disjoint.subset (ht : t.pairwise_disjoint f) (h : s ⊆ t) : s.pairwise_disjoint f :=
  Pairwise.mono h ht

theorem pairwise_disjoint.mono_on (hs : s.pairwise_disjoint f) (h : ∀ ⦃i⦄, i ∈ s → g i ≤ f i) : s.pairwise_disjoint g :=
  fun a ha b hb hab => (hs ha hb hab).mono (h ha) (h hb)

theorem pairwise_disjoint.mono (hs : s.pairwise_disjoint f) (h : g ≤ f) : s.pairwise_disjoint g :=
  hs.mono_on fun i _ => h i

@[simp]
theorem pairwise_disjoint_empty : (∅ : Set ι).PairwiseDisjoint f :=
  pairwise_empty _

@[simp]
theorem pairwise_disjoint_singleton (i : ι) (f : ι → α) : pairwise_disjoint {i} f :=
  pairwise_singleton i _

theorem pairwise_disjoint_insert {i : ι} :
    (insert i s).PairwiseDisjoint f ↔ s.pairwise_disjoint f ∧ ∀, ∀ j ∈ s, ∀, i ≠ j → Disjoint (f i) (f j) :=
  Set.pairwise_insert_of_symmetric $ symmetric_disjoint.comap f

theorem pairwise_disjoint.insert (hs : s.pairwise_disjoint f) {i : ι}
    (h : ∀, ∀ j ∈ s, ∀, i ≠ j → Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  Set.pairwise_disjoint_insert.2 ⟨hs, h⟩

theorem pairwise_disjoint.image_of_le (hs : s.pairwise_disjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
    (g '' s).PairwiseDisjoint f := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb $ ne_of_apply_ne _ h).mono (hg a) (hg b)

theorem inj_on.pairwise_disjoint_image {g : ι' → ι} {s : Set ι'} (h : s.inj_on g) :
    (g '' s).PairwiseDisjoint f ↔ s.pairwise_disjoint (f ∘ g) :=
  h.pairwise_image

theorem pairwise_disjoint.range (g : s → ι) (hg : ∀ i : s, f (g i) ≤ f i) (ht : s.pairwise_disjoint f) :
    (range g).PairwiseDisjoint f := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact (ht x.2 y.2 $ fun h => hxy $ congr_argₓ g $ Subtype.ext h).mono (hg x) (hg y)

theorem pairwise_disjoint_union :
    (s ∪ t).PairwiseDisjoint f ↔
      s.pairwise_disjoint f ∧ t.pairwise_disjoint f ∧ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j) :=
  pairwise_union_of_symmetric $ symmetric_disjoint.comap f

theorem pairwise_disjoint.union (hs : s.pairwise_disjoint f) (ht : t.pairwise_disjoint f)
    (h : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j)) : (s ∪ t).PairwiseDisjoint f :=
  pairwise_disjoint_union.2 ⟨hs, ht, h⟩

theorem pairwise_disjoint_Union {g : ι' → Set ι} (h : Directed (· ⊆ ·) g) :
    (⋃ n, g n).PairwiseDisjoint f ↔ ∀ ⦃n⦄, (g n).PairwiseDisjoint f :=
  pairwise_Union h

theorem pairwise_disjoint_sUnion {s : Set (Set ι)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀s).PairwiseDisjoint f ↔ ∀ ⦃a⦄, a ∈ s → Set.PairwiseDisjoint a f :=
  pairwise_sUnion h

theorem pairwise_disjoint.elim (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : ¬Disjoint (f i) (f j)) : i = j :=
  of_not_not $ fun hij => h $ hs hi hj hij

theorem pairwise_disjoint.elim' (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (h : f i⊓f j ≠ ⊥) :
    i = j :=
  hs.elim hi hj $ fun hij => h hij.eq_bot

end SemilatticeInfBot

section CompleteLattice

variable [CompleteLattice α]

/-- Bind operation for `set.pairwise_disjoint`. If you want to only consider finsets of indices, you
can use `set.pairwise_disjoint.bUnion_finset`. -/
theorem pairwise_disjoint.bUnion {s : Set ι'} {g : ι' → Set ι} {f : ι → α}
    (hs : s.pairwise_disjoint fun i' : ι' => ⨆ i ∈ g i', f i) (hg : ∀, ∀ i ∈ s, ∀, (g i).PairwiseDisjoint f) :
    (⋃ i ∈ s, g i).PairwiseDisjoint f := by
  rintro a ha b hb hab
  simp_rw [Set.mem_Union]  at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd.subst ha) hb hab
    
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (le_bsupr a ha) (le_bsupr b hb)
    

end CompleteLattice

/-! ### Pairwise disjoint set of sets -/


theorem pairwise_disjoint_range_singleton : (Set.Range (singleton : ι → Set ι)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)

theorem pairwise_disjoint_fiber (f : ι → α) (s : Set α) : s.pairwise_disjoint fun a => f ⁻¹' {a} :=
  fun a _ b _ h i ⟨hia, hib⟩ => h $ (Eq.symm hia).trans hib

theorem pairwise_disjoint.elim_set {s : Set ι} {f : ι → Set α} (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s)
    (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj $ not_disjoint_iff.2 ⟨a, hai, haj⟩

theorem bUnion_diff_bUnion_eq {s t : Set ι} {f : ι → Set α} (h : (s ∪ t).PairwiseDisjoint f) :
    ((⋃ i ∈ s, f i) \ ⋃ i ∈ t, f i) = ⋃ i ∈ s \ t, f i := by
  refine'
    (bUnion_diff_bUnion_subset f s t).antisymm (bUnion_subset $ fun i hi a ha => (mem_diff _).2 ⟨mem_bUnion hi.1 ha, _⟩)
  rw [mem_bUnion_iff]
  rintro ⟨j, hj, haj⟩
  exact h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm ⟨ha, haj⟩

/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def bUnion_eq_sigma_of_disjoint {s : Set ι} {f : ι → Set α} (h : s.pairwise (Disjoint on f)) :
    (⋃ i ∈ s, f i) ≃ Σ i : s, f i :=
  (Equivₓ.setCongr (bUnion_eq_Union _ _)).trans $
    Union_eq_sigma_of_disjoint $ fun ⟨i, hi⟩ ⟨j, hj⟩ ne => h hi hj $ fun eq => Ne $ Subtype.eq Eq

end Set

theorem pairwise_disjoint_fiber (f : ι → α) : Pairwise (Disjoint on fun a : α => f ⁻¹' {a}) :=
  Set.pairwise_univ.1 $ Set.pairwise_disjoint_fiber f univ

