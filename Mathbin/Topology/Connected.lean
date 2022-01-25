import Mathbin.Topology.SubsetProperties

/-!
# Connected subsets of topological spaces

In this file we define connected subsets of a topological spaces and various other properties and
classes related to connectivity.

## Main definitions

We define the following properties for sets in a topological space:

* `is_connected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
* `connected_component` is the connected component of an element in the space.
* `is_totally_disconnected`: all of its connected components are singletons.
* `is_totally_separated`: any two points can be separated by two disjoint opens that cover the set.

For each of these definitions, we also have a class stating that the whole space
satisfies that property:
`connected_space`, `totally_disconnected_space`, `totally_separated_space`.

## On the definition of connected sets/spaces

In informal mathematics, connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `is_preconnected`.
In other words, the only difference is whether the empty space counts as connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/


open Set Function TopologicalSpace

open_locale Classical TopologicalSpace

universe u v

variable {α : Type u} {β : Type v} {ι : Type _} {π : ι → Type _} [TopologicalSpace α] {s t u v : Set α}

section Preconnected

/-- A preconnected set is one where there is no non-trivial open partition. -/
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty

/-- A connected set is one that is nonempty and where there is no non-trivial open partition. -/
def IsConnected (s : Set α) : Prop :=
  s.nonempty ∧ IsPreconnected s

theorem IsConnected.nonempty {s : Set α} (h : IsConnected s) : s.nonempty :=
  h.1

theorem IsConnected.is_preconnected {s : Set α} (h : IsConnected s) : IsPreconnected s :=
  h.2

theorem IsPreirreducible.is_preconnected {s : Set α} (H : IsPreirreducible s) : IsPreconnected s := fun _ _ hu hv _ =>
  H _ _ hu hv

theorem IsIrreducible.is_connected {s : Set α} (H : IsIrreducible s) : IsConnected s :=
  ⟨H.nonempty, H.is_preirreducible.is_preconnected⟩

theorem is_preconnected_empty : IsPreconnected (∅ : Set α) :=
  is_preirreducible_empty.IsPreconnected

theorem is_connected_singleton {x} : IsConnected ({x} : Set α) :=
  is_irreducible_singleton.IsConnected

theorem is_preconnected_singleton {x} : IsPreconnected ({x} : Set α) :=
  is_connected_singleton.IsPreconnected

theorem Set.Subsingleton.is_preconnected {s : Set α} (hs : s.subsingleton) : IsPreconnected s :=
  hs.induction_on is_preconnected_empty fun x => is_preconnected_singleton

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall {s : Set α} (x : α)
    (H : ∀, ∀ y ∈ s, ∀, ∃ (t : _)(_ : t ⊆ s), x ∈ t ∧ y ∈ t ∧ IsPreconnected t) : IsPreconnected s := by
  rintro u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩
  have xs : x ∈ s := by
    rcases H y ys with ⟨t, ts, xt, yt, ht⟩
    exact ts xt
  wlog xu : x ∈ u := hs xs using u v y z, v u z y
  rcases H y ys with ⟨t, ts, xt, yt, ht⟩
  have := ht u v hu hv (subset.trans ts hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩
  exact this.imp fun z hz => ⟨ts hz.1, hz.2⟩

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (x y «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall_pair {s : Set α}
    (H : ∀ x y _ : x ∈ s _ : y ∈ s, ∃ (t : _)(_ : t ⊆ s), x ∈ t ∧ y ∈ t ∧ IsPreconnected t) : IsPreconnected s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  exacts[is_preconnected_empty, is_preconnected_of_forall x $ fun y => H x hx y]

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
theorem is_preconnected_sUnion (x : α) (c : Set (Set α)) (H1 : ∀, ∀ s ∈ c, ∀, x ∈ s)
    (H2 : ∀, ∀ s ∈ c, ∀, IsPreconnected s) : IsPreconnected (⋃₀c) := by
  apply is_preconnected_of_forall x
  rintro y ⟨s, sc, ys⟩
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩

theorem is_preconnected_Union {ι : Sort _} {s : ι → Set α} (h₁ : (⋂ i, s i).Nonempty) (h₂ : ∀ i, IsPreconnected (s i)) :
    IsPreconnected (⋃ i, s i) :=
  Exists.elim h₁ $ fun f hf => is_preconnected_sUnion f _ hf (forall_range_iff.2 h₂)

theorem IsPreconnected.union (x : α) {s t : Set α} (H1 : x ∈ s) (H2 : x ∈ t) (H3 : IsPreconnected s)
    (H4 : IsPreconnected t) : IsPreconnected (s ∪ t) :=
  sUnion_pair s t ▸
    is_preconnected_sUnion x {s, t}
      (by
        rintro r (rfl | rfl | h) <;> assumption)
      (by
        rintro r (rfl | rfl | h) <;> assumption)

theorem IsConnected.union {s t : Set α} (H : (s ∩ t).Nonempty) (Hs : IsConnected s) (Ht : IsConnected t) :
    IsConnected (s ∪ t) := by
  rcases H with ⟨x, hx⟩
  refine' ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, _⟩
  exact
    IsPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx) Hs.is_preconnected Ht.is_preconnected

/-- Theorem of bark and tree :
if a set is within a (pre)connected set and its closure,
then it is (pre)connected as well. -/
theorem IsPreconnected.subset_closure {s : Set α} {t : Set α} (H : IsPreconnected s) (Kst : s ⊆ t)
    (Ktcs : t ⊆ Closure s) : IsPreconnected t := fun u v hu hv htuv ⟨y, hyt, hyu⟩ ⟨z, hzt, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv (subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, Kst hrs, hruv⟩

theorem IsConnected.subset_closure {s : Set α} {t : Set α} (H : IsConnected s) (Kst : s ⊆ t) (Ktcs : t ⊆ Closure s) :
    IsConnected t :=
  let hsne := H.left
  let ht := Kst
  let htne := nonempty.mono ht hsne
  ⟨nonempty.mono Kst H.left, IsPreconnected.subset_closure H.right Kst Ktcs⟩

/-- The closure of a (pre)connected set is (pre)connected as well. -/
theorem IsPreconnected.closure {s : Set α} (H : IsPreconnected s) : IsPreconnected (Closure s) :=
  IsPreconnected.subset_closure H subset_closure $ subset.refl $ Closure s

theorem IsConnected.closure {s : Set α} (H : IsConnected s) : IsConnected (Closure s) :=
  IsConnected.subset_closure H subset_closure $ subset.refl $ Closure s

/-- The image of a (pre)connected set is (pre)connected as well. -/
theorem IsPreconnected.image [TopologicalSpace β] {s : Set α} (H : IsPreconnected s) (f : α → β)
    (hf : ContinuousOn f s) : IsPreconnected (f '' s) := by
  rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
  rcases continuous_on_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuous_on_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  replace huv : s ⊆ u' ∪ v'
  · rw [image_subset_iff, preimage_union] at huv
    replace huv := subset_inter huv (subset.refl _)
    rw [inter_distrib_right, u'_eq, v'_eq, ← inter_distrib_right] at huv
    exact (subset_inter_iff.1 huv).1
    
  obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).Nonempty := by
    refine' H u' v' hu' hv' huv ⟨x, _⟩ ⟨y, _⟩ <;> rw [inter_comm]
    exacts[u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
  rw [← inter_self s, inter_assoc, inter_left_comm s u', ← inter_assoc, inter_comm s, inter_comm s, ← u'_eq, ← v'_eq] at
    hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩

theorem IsConnected.image [TopologicalSpace β] {s : Set α} (H : IsConnected s) (f : α → β) (hf : ContinuousOn f s) :
    IsConnected (f '' s) :=
  ⟨nonempty_image_iff.mpr H.nonempty, H.is_preconnected.image f hf⟩

theorem is_preconnected_closed_iff {s : Set α} :
    IsPreconnected s ↔
      ∀ t t', IsClosed t → IsClosed t' → s ⊆ t ∪ t' → (s ∩ t).Nonempty → (s ∩ t').Nonempty → (s ∩ (t ∩ t')).Nonempty :=
  ⟨by
    rintro h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩
    by_contra h'
    rw [← ne_empty_iff_nonempty, Ne.def, not_not, ← subset_compl_iff_disjoint, compl_inter] at h'
    have xt' : x ∉ t' := (h' xs).elim (absurd xt) id
    have yt : y ∉ t := (h' ys).elim id (absurd yt')
    have :=
      ne_empty_iff_nonempty.2
        (h (tᶜ) (t'ᶜ) (is_open_compl_iff.2 ht) (is_open_compl_iff.2 ht') h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩)
    rw [Ne.def, ← compl_union, ← subset_compl_iff_disjoint, compl_compl] at this
    contradiction, by
    rintro h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩
    by_contra h'
    rw [← ne_empty_iff_nonempty, Ne.def, not_not, ← subset_compl_iff_disjoint, compl_inter] at h'
    have xv : x ∉ v := (h' xs).elim (absurd xu) id
    have yu : y ∉ u := (h' ys).elim id (absurd yv)
    have :=
      ne_empty_iff_nonempty.2
        (h (uᶜ) (vᶜ) (is_closed_compl_iff.2 hu) (is_closed_compl_iff.2 hv) h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩)
    rw [Ne.def, ← compl_union, ← subset_compl_iff_disjoint, compl_compl] at this
    contradiction⟩

theorem Inducing.is_preconnected_image [TopologicalSpace β] {s : Set α} {f : α → β} (hf : Inducing f) :
    IsPreconnected (f '' s) ↔ IsPreconnected s := by
  refine' ⟨fun h => _, fun h => h.image _ hf.continuous.continuous_on⟩
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  rcases hf.is_open_iff.1 hu' with ⟨u, hu, rfl⟩
  rcases hf.is_open_iff.1 hv' with ⟨v, hv, rfl⟩
  replace huv : f '' s ⊆ u ∪ v
  · rwa [image_subset_iff]
    
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩ with
    ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩
  exact ⟨z, hzs, hzuv⟩

theorem IsPreconnected.preimage_of_open_map [TopologicalSpace β] {s : Set β} (hs : IsPreconnected s) {f : α → β}
    (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ Set.Range f) : IsPreconnected (f ⁻¹' s) :=
  fun u v hu hv hsuv hsu hsv => by
  obtain ⟨b, hbs, hbu, hbv⟩ := hs (f '' u) (f '' v) (hf u hu) (hf v hv) _ _ _
  obtain ⟨a, rfl⟩ := hsf hbs
  rw [hinj.mem_set_image] at hbu hbv
  exact ⟨a, hbs, hbu, hbv⟩
  · have := Set.image_subset f hsuv
    rwa [Set.image_preimage_eq_of_subset hsf, Set.image_union] at this
    
  · obtain ⟨x, hx1, hx2⟩ := hsu
    exact ⟨f x, hx1, x, hx2, rfl⟩
    
  · obtain ⟨y, hy1, hy2⟩ := hsv
    exact ⟨f y, hy1, y, hy2, rfl⟩
    

theorem IsPreconnected.preimage_of_closed_map [TopologicalSpace β] {s : Set β} (hs : IsPreconnected s) {f : α → β}
    (hinj : Function.Injective f) (hf : IsClosedMap f) (hsf : s ⊆ Set.Range f) : IsPreconnected (f ⁻¹' s) :=
  is_preconnected_closed_iff.2 $ fun u v hu hv hsuv hsu hsv => by
    obtain ⟨b, hbs, hbu, hbv⟩ := is_preconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) _ _ _
    obtain ⟨a, rfl⟩ := hsf hbs
    rw [hinj.mem_set_image] at hbu hbv
    exact ⟨a, hbs, hbu, hbv⟩
    · have := Set.image_subset f hsuv
      rwa [Set.image_preimage_eq_of_subset hsf, Set.image_union] at this
      
    · obtain ⟨x, hx1, hx2⟩ := hsu
      exact ⟨f x, hx1, x, hx2, rfl⟩
      
    · obtain ⟨y, hy1, hy2⟩ := hsv
      exact ⟨f y, hy1, y, hy2, rfl⟩
      

theorem IsConnected.preimage_of_open_map [TopologicalSpace β] {s : Set β} (hs : IsConnected s) {f : α → β}
    (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ Set.Range f) : IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.is_preconnected.preimage_of_open_map hinj hf hsf⟩

theorem IsConnected.preimage_of_closed_map [TopologicalSpace β] {s : Set β} (hs : IsConnected s) {f : α → β}
    (hinj : Function.Injective f) (hf : IsClosedMap f) (hsf : s ⊆ Set.Range f) : IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.is_preconnected.preimage_of_closed_map hinj hf hsf⟩

theorem IsPreconnected.subset_or_subset (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v)
    (hs : IsPreconnected s) : s ⊆ u ∨ s ⊆ v := by
  specialize hs u v hu hv hsuv
  obtain hsu | hsu := (s ∩ u).eq_empty_or_nonempty
  · exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
    
  · replace hs := mt (hs hsu)
    simp_rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff_inter_eq_empty.1 huv]
       at hs
    exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)
    

theorem IsPreconnected.subset_left_of_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hsuv : s ⊆ u ∪ v) (hsu : (s ∩ u).Nonempty) (hs : IsPreconnected s) : s ⊆ u :=
  Disjoint.subset_left_of_subset_union hsuv
    (by
      by_contra hsv
      rw [Set.not_disjoint_iff_nonempty_inter] at hsv
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv
      exact Set.disjoint_iff.1 huv hx)

theorem IsPreconnected.subset_right_of_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hsuv : s ⊆ u ∪ v) (hsv : (s ∩ v).Nonempty) (hs : IsPreconnected s) : s ⊆ v :=
  hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv

theorem IsPreconnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ×ˢ t) := by
  apply is_preconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  refine' ⟨Prod.mk a₁ '' t ∪ flip Prod.mk b₂ '' s, _, Or.inl ⟨b₁, hb₁, rfl⟩, Or.inr ⟨a₂, ha₂, rfl⟩, _⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    exacts[⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
    
  · exact
      (ht.image _ (Continuous.Prod.mk _).ContinuousOn).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩ ⟨a₁, ha₁, rfl⟩
        (hs.image _ (continuous_id.prod_mk continuous_const).ContinuousOn)
    

theorem IsConnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConnected s) (ht : IsConnected t) :
    IsConnected (s ×ˢ t) :=
  ⟨hs.1.Prod ht.1, hs.2.Prod ht.2⟩

theorem is_preconnected_univ_pi [∀ i, TopologicalSpace (π i)] {s : ∀ i, Set (π i)} (hs : ∀ i, IsPreconnected (s i)) :
    IsPreconnected (pi univ s) := by
  rintro u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩
  induction' I using Finset.induction_on with i I hi ihI
  · refine' ⟨g, hgs, ⟨_, hgv⟩⟩
    simpa using hI
    
  · rw [Finset.piecewise_insert] at hI
    have := I.piecewise_mem_set_pi hfs hgs
    refine' (hsuv this).elim ihI fun h => _
    set S := update (I.piecewise f g) i '' s i
    have hsub : S ⊆ pi univ s := by
      refine' image_subset_iff.2 fun z hz => _
      rwa [update_preimage_univ_pi]
      exact fun j hj => this j trivialₓ
    have hconn : IsPreconnected S := (hs i).Image _ (continuous_const.update i continuous_id).ContinuousOn
    have hSu : (S ∩ u).Nonempty := ⟨_, mem_image_of_mem _ (hfs _ trivialₓ), hI⟩
    have hSv : (S ∩ v).Nonempty := ⟨_, ⟨_, this _ trivialₓ, update_eq_self _ _⟩, h⟩
    refine' (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono _
    exact inter_subset_inter_left _ hsub
    

@[simp]
theorem is_connected_univ_pi [∀ i, TopologicalSpace (π i)] {s : ∀ i, Set (π i)} :
    IsConnected (pi univ s) ↔ ∀ i, IsConnected (s i) := by
  simp only [IsConnected, ← univ_pi_nonempty_iff, forall_and_distrib, And.congr_right_iff]
  refine' fun hne => ⟨fun hc i => _, is_preconnected_univ_pi⟩
  rw [← eval_image_univ_pi hne]
  exact hc.image _ (continuous_apply _).ContinuousOn

theorem Sigma.is_connected_iff [∀ i, TopologicalSpace (π i)] {s : Set (Σ i, π i)} :
    IsConnected s ↔ ∃ i t, IsConnected t ∧ s = Sigma.mk i '' t := by
  refine' ⟨fun hs => _, _⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s ⊆ Set.Range (Sigma.mk i) := by
      have h : Set.Range (Sigma.mk i) = Sigma.fst ⁻¹' {i} := by
        ext
        simp
      rw [h]
      exact
        IsPreconnected.subset_left_of_subset_union (is_open_sigma_fst_preimage _)
          (is_open_sigma_fst_preimage { x | x ≠ i }) (Set.disjoint_iff.2 $ fun x hx => hx.2 hx.1)
          (fun y hy => by
            simp [Classical.em])
          ⟨⟨i, x⟩, hx, rfl⟩ hs.2
    exact
      ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_open_map sigma_mk_injective is_open_map_sigma_mk this,
        (Set.image_preimage_eq_of_subset this).symm⟩
    
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigma_mk.continuous_on
    

theorem Sigma.is_preconnected_iff [hι : Nonempty ι] [∀ i, TopologicalSpace (π i)] {s : Set (Σ i, π i)} :
    IsPreconnected s ↔ ∃ i t, IsPreconnected t ∧ s = Sigma.mk i '' t := by
  refine' ⟨fun hs => _, _⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, is_preconnected_empty, (Set.image_empty _).symm⟩
      
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.is_connected_iff.1 ⟨h, hs⟩
      refine' ⟨a, t, ht.is_preconnected, rfl⟩
      
    
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigma_mk.continuous_on
    

theorem Sum.is_connected_iff [TopologicalSpace β] {s : Set (Sum α β)} :
    IsConnected s ↔ (∃ t, IsConnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsConnected t ∧ s = Sum.inr '' t := by
  refine' ⟨fun hs => _, _⟩
  · let u : Set (Sum α β) := Set.Range Sum.inl
    let v : Set (Sum α β) := Set.Range Sum.inr
    have hu : IsOpen u := is_open_range_inl
    obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h :=
        IsPreconnected.subset_left_of_subset_union is_open_range_inl is_open_range_inr
          set.is_compl_range_inl_range_inr.disjoint
          (show s ⊆ Set.Range Sum.inl ∪ Set.Range Sum.inr by
            simp )
          ⟨Sum.inl x, hx, x, rfl⟩ hs.2
      refine' Or.inl ⟨Sum.inl ⁻¹' s, _, _⟩
      · exact hs.preimage_of_open_map Sum.inl_injective open_embedding_inl.is_open_map h
        
      · exact (Set.image_preimage_eq_of_subset h).symm
        
      
    · have h :=
        IsPreconnected.subset_right_of_subset_union is_open_range_inl is_open_range_inr
          set.is_compl_range_inl_range_inr.disjoint
          (show s ⊆ Set.Range Sum.inl ∪ Set.Range Sum.inr by
            simp )
          ⟨Sum.inr x, hx, x, rfl⟩ hs.2
      refine' Or.inr ⟨Sum.inr ⁻¹' s, _, _⟩
      · exact hs.preimage_of_open_map Sum.inr_injective open_embedding_inr.is_open_map h
        
      · exact (Set.image_preimage_eq_of_subset h).symm
        
      
    
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuous_on
      
    · exact ht.image _ continuous_inr.continuous_on
      
    

theorem Sum.is_preconnected_iff [TopologicalSpace β] {s : Set (Sum α β)} :
    IsPreconnected s ↔ (∃ t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsPreconnected t ∧ s = Sum.inr '' t := by
  refine' ⟨fun hs => _, _⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, is_preconnected_empty, (Set.image_empty _).symm⟩
      
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.is_connected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.is_preconnected, rfl⟩
      
    · exact Or.inr ⟨t, ht.is_preconnected, rfl⟩
      
    
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuous_on
      
    · exact ht.image _ continuous_inr.continuous_on
      
    

/-- The connected component of a point is the maximal connected set
that contains this point. -/
def ConnectedComponent (x : α) : Set α :=
  ⋃₀{ s : Set α | IsPreconnected s ∧ x ∈ s }

/-- The connected component of a point inside a set. -/
def ConnectedComponentIn (F : Set α) (x : F) : Set α :=
  coe '' ConnectedComponent x

theorem mem_connected_component {x : α} : x ∈ ConnectedComponent x :=
  mem_sUnion_of_mem (mem_singleton x) ⟨is_connected_singleton.IsPreconnected, mem_singleton x⟩

theorem is_preconnected_connected_component {x : α} : IsPreconnected (ConnectedComponent x) :=
  is_preconnected_sUnion x _ (fun _ => And.right) fun _ => And.left

theorem is_connected_connected_component {x : α} : IsConnected (ConnectedComponent x) :=
  ⟨⟨x, mem_connected_component⟩, is_preconnected_connected_component⟩

theorem IsPreconnected.subset_connected_component {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x ∈ s) :
    s ⊆ ConnectedComponent x := fun z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩

theorem IsConnected.subset_connected_component {x : α} {s : Set α} (H1 : IsConnected s) (H2 : x ∈ s) :
    s ⊆ ConnectedComponent x :=
  H1.2.subset_connected_component H2

theorem connected_component_eq {x y : α} (h : y ∈ ConnectedComponent x) : ConnectedComponent x = ConnectedComponent y :=
  eq_of_subset_of_subset (is_connected_connected_component.subset_connected_component h)
    (is_connected_connected_component.subset_connected_component
      (Set.mem_of_mem_of_subset mem_connected_component
        (is_connected_connected_component.subset_connected_component h)))

theorem connected_component_disjoint {x y : α} (h : ConnectedComponent x ≠ ConnectedComponent y) :
    Disjoint (ConnectedComponent x) (ConnectedComponent y) :=
  Set.disjoint_left.2 fun a h1 h2 => h ((connected_component_eq h1).trans (connected_component_eq h2).symm)

theorem is_closed_connected_component {x : α} : IsClosed (ConnectedComponent x) :=
  closure_eq_iff_is_closed.1 $
    subset.antisymm
      (is_connected_connected_component.closure.subset_connected_component (subset_closure mem_connected_component))
      subset_closure

theorem Continuous.image_connected_component_subset [TopologicalSpace β] {f : α → β} (h : Continuous f) (a : α) :
    f '' ConnectedComponent a ⊆ ConnectedComponent (f a) :=
  (is_connected_connected_component.Image f h.continuous_on).subset_connected_component
    ((mem_image f (ConnectedComponent a) (f a)).2 ⟨a, mem_connected_component, rfl⟩)

theorem Continuous.maps_to_connected_component [TopologicalSpace β] {f : α → β} (h : Continuous f) (a : α) :
    maps_to f (ConnectedComponent a) (ConnectedComponent (f a)) :=
  maps_to'.2 $ h.image_connected_component_subset a

theorem irreducible_component_subset_connected_component {x : α} : IrreducibleComponent x ⊆ ConnectedComponent x :=
  is_irreducible_irreducible_component.IsConnected.subset_connected_component mem_irreducible_component

/-- A preconnected space is one where there is no non-trivial open partition. -/
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  is_preconnected_univ : IsPreconnected (univ : Set α)

export PreconnectedSpace (is_preconnected_univ)

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
class ConnectedSpace (α : Type u) [TopologicalSpace α] extends PreconnectedSpace α : Prop where
  to_nonempty : Nonempty α

attribute [instance] ConnectedSpace.to_nonempty

theorem is_preconnected_range [TopologicalSpace β] [PreconnectedSpace α] {f : α → β} (h : Continuous f) :
    IsPreconnected (range f) :=
  @image_univ _ _ f ▸ is_preconnected_univ.Image _ h.continuous_on

theorem is_connected_range [TopologicalSpace β] [ConnectedSpace α] {f : α → β} (h : Continuous f) :
    IsConnected (range f) :=
  ⟨range_nonempty f, is_preconnected_range h⟩

theorem DenseRange.preconnected_space [TopologicalSpace β] [PreconnectedSpace α] {f : α → β} (hf : DenseRange f)
    (hc : Continuous f) : PreconnectedSpace β :=
  ⟨hf.closure_eq ▸ (is_preconnected_range hc).closure⟩

theorem connected_space_iff_connected_component : ConnectedSpace α ↔ ∃ x : α, ConnectedComponent x = univ := by
  constructor
  · rintro ⟨h, ⟨x⟩⟩
    exact ⟨x, eq_univ_of_univ_subset $ is_preconnected_univ.subset_connected_component (mem_univ x)⟩
    
  · rintro ⟨x, h⟩
    have : PreconnectedSpace α :=
      ⟨by
        rw [← h]
        exact is_preconnected_connected_component⟩
    exact ⟨⟨x⟩⟩
    

theorem preconnected_space_iff_connected_component : PreconnectedSpace α ↔ ∀ x : α, ConnectedComponent x = univ := by
  constructor
  · intro h x
    exact eq_univ_of_univ_subset $ is_preconnected_univ.subset_connected_component (mem_univ x)
    
  · intro h
    cases' is_empty_or_nonempty α with hα hα
    · exact
        ⟨by
          rw [univ_eq_empty_iff.mpr hα]
          exact is_preconnected_empty⟩
      
    · exact
        ⟨by
          rw [← h (Classical.choice hα)]
          exact is_preconnected_connected_component⟩
      
    

@[simp]
theorem PreconnectedSpace.connected_component_eq_univ {X : Type _} [TopologicalSpace X] [h : PreconnectedSpace X]
    (x : X) : ConnectedComponent x = univ :=
  preconnected_space_iff_connected_component.mp h x

instance [TopologicalSpace β] [PreconnectedSpace α] [PreconnectedSpace β] : PreconnectedSpace (α × β) :=
  ⟨by
    rw [← univ_prod_univ]
    exact is_preconnected_univ.prod is_preconnected_univ⟩

instance [TopologicalSpace β] [ConnectedSpace α] [ConnectedSpace β] : ConnectedSpace (α × β) :=
  ⟨Prod.nonempty⟩

instance [∀ i, TopologicalSpace (π i)] [∀ i, PreconnectedSpace (π i)] : PreconnectedSpace (∀ i, π i) :=
  ⟨by
    rw [← pi_univ univ]
    exact is_preconnected_univ_pi fun i => is_preconnected_univ⟩

instance [∀ i, TopologicalSpace (π i)] [∀ i, ConnectedSpace (π i)] : ConnectedSpace (∀ i, π i) :=
  ⟨Classical.nonempty_piₓ.2 $ fun i => by
      infer_instance⟩

instance (priority := 100) PreirreducibleSpace.preconnected_space (α : Type u) [TopologicalSpace α]
    [PreirreducibleSpace α] : PreconnectedSpace α :=
  ⟨(PreirreducibleSpace.is_preirreducible_univ α).IsPreconnected⟩

instance (priority := 100) IrreducibleSpace.connected_space (α : Type u) [TopologicalSpace α] [IrreducibleSpace α] :
    ConnectedSpace α where
  to_nonempty := IrreducibleSpace.to_nonempty α

theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s ∪ t = univ → s.nonempty → t.nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.is_preconnected_univ α _ _ s t

theorem is_clopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
    Classical.by_contradiction $ fun h =>
      have h1 : s ≠ ∅ ∧ sᶜ ≠ ∅ :=
        ⟨mt Or.inl h,
          mt
            (fun h2 =>
              Or.inr $
                (by
                  rw [← compl_compl s, h2, compl_empty] : s = univ))
            h⟩
      let ⟨_, h2, h3⟩ :=
        nonempty_inter hs.1 hs.2.is_open_compl (union_compl_self s) (ne_empty_iff_nonempty.1 h1.1)
          (ne_empty_iff_nonempty.1 h1.2)
      h3 h2,
    by
    rintro (rfl | rfl) <;> [exact is_clopen_empty, exact is_clopen_univ]⟩

theorem eq_univ_of_nonempty_clopen [PreconnectedSpace α] {s : Set α} (h : s.nonempty) (h' : IsClopen s) : s = univ := by
  rw [is_clopen_iff] at h'
  exact h'.resolve_left h.ne_empty

theorem Subtype.preconnected_space {s : Set α} (h : IsPreconnected s) : PreconnectedSpace s :=
  { is_preconnected_univ := by
      rwa [← embedding_subtype_coe.to_inducing.is_preconnected_image, image_univ, Subtype.range_coe] }

theorem Subtype.connected_space {s : Set α} (h : IsConnected s) : ConnectedSpace s :=
  { to_preconnected_space := Subtype.preconnected_space h.is_preconnected, to_nonempty := h.nonempty.to_subtype }

theorem is_preconnected_iff_preconnected_space {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s :=
  ⟨Subtype.preconnected_space, by
    intro
    simpa using is_preconnected_univ.image (coe : s → α) continuous_subtype_coe.continuous_on⟩

theorem is_connected_iff_connected_space {s : Set α} : IsConnected s ↔ ConnectedSpace s :=
  ⟨Subtype.connected_space, fun h => ⟨nonempty_subtype.mp h.2, is_preconnected_iff_preconnected_space.mpr h.1⟩⟩

/-- A set `s` is preconnected if and only if
for every cover by two open sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint {s : Set α} :
    IsPreconnected s ↔ ∀ u v : Set α hu : IsOpen u hv : IsOpen v hs : s ⊆ u ∪ v huv : s ∩ (u ∩ v) = ∅, s ⊆ u ∨ s ⊆ v :=
  by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    rw [ne_empty_iff_nonempty]
    simp [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
    
  · intro u v hu hv hs hsu hsv
    rw [← ne_empty_iff_nonempty]
    intro H
    specialize h u v hu hv hs H
    contrapose H
    apply ne_empty_iff_nonempty.mpr
    cases h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
      
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩
      
    

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
theorem is_connected_iff_sUnion_disjoint_open {s : Set α} :
    IsConnected s ↔
      ∀ U : Finset (Set α) H : ∀ u v : Set α, u ∈ U → v ∈ U → (s ∩ (u ∩ v)).Nonempty → u = v hU :
        ∀, ∀ u ∈ U, ∀, IsOpen u hs : s ⊆ ⋃₀↑U, ∃ u ∈ U, s ⊆ u :=
  by
  rw [IsConnected, is_preconnected_iff_subset_of_disjoint]
  constructor <;> intro h
  · intro U
    apply Finset.induction_on U
    · rcases h.left with ⟨⟩
      suffices s ⊆ ∅ → False by
        simpa
      intro
      solve_by_elim
      
    · intro u U hu IH hs hU H
      rw [Finset.coe_insert, sUnion_insert] at H
      cases' h.2 u (⋃₀↑U) _ _ H _ with hsu hsU
      · exact ⟨u, Finset.mem_insert_self _ _, hsu⟩
        
      · rcases IH _ _ hsU with ⟨v, hvU, hsv⟩
        · exact ⟨v, Finset.mem_insert_of_mem hvU, hsv⟩
          
        · intros
          apply hs <;> solve_by_elim [Finset.mem_insert_of_mem]
          
        · intros
          solve_by_elim [Finset.mem_insert_of_mem]
          
        
      · solve_by_elim [Finset.mem_insert_self]
        
      · apply is_open_sUnion
        intros
        solve_by_elim [Finset.mem_insert_of_mem]
        
      · apply eq_empty_of_subset_empty
        rintro x ⟨hxs, hxu, hxU⟩
        rw [mem_sUnion] at hxU
        rcases hxU with ⟨v, hvU, hxv⟩
        rcases hs u v (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hvU) _ with rfl
        · contradiction
          
        · exact ⟨x, hxs, hxu, hxv⟩
          
        
      
    
  · constructor
    · rw [← ne_empty_iff_nonempty]
      by_contra hs
      subst hs
      simpa using h ∅ _ _ _ <;> simp
      
    intro u v hu hv hs hsuv
    rcases h {u, v} _ _ _ with ⟨t, ht, ht'⟩
    · rw [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with (rfl | rfl) <;> tauto
      
    · intro t₁ t₂ ht₁ ht₂ hst
      rw [← ne_empty_iff_nonempty] at hst
      rw [Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
      rcases ht₁ with (rfl | rfl) <;> rcases ht₂ with (rfl | rfl)
      all_goals
        first |
          rfl|
          contradiction|
          skip
      rw [inter_comm t₁] at hst
      contradiction
      
    · intro t
      rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl) <;> assumption
      
    · simpa using hs
      
    

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem IsPreconnected.subset_clopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) (hne : (s ∩ t).Nonempty) :
    s ⊆ t := by
  by_contra h
  have : (s ∩ tᶜ).Nonempty := inter_compl_nonempty_iff.2 h
  obtain ⟨x, -, hx, hx'⟩ : (s ∩ (t ∩ tᶜ)).Nonempty
  exact hs t (tᶜ) ht.is_open ht.compl.is_open (fun x hx => em _) hne this
  exact hx' hx

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem disjoint_or_subset_of_clopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) : Disjoint s t ∨ s ⊆ t :=
  (disjoint_or_nonempty_inter s t).imp_right $ hs.subset_clopen ht

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint_closed :
    IsPreconnected s ↔
      ∀ u v : Set α hu : IsClosed u hv : IsClosed v hs : s ⊆ u ∪ v huv : s ∩ (u ∩ v) = ∅, s ⊆ u ∨ s ⊆ v :=
  by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [is_preconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    rw [ne_empty_iff_nonempty]
    simp [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
    
  · rw [is_preconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    rw [← ne_empty_iff_nonempty]
    intro H
    specialize h u v hu hv hs H
    contrapose H
    apply ne_empty_iff_nonempty.mpr
    cases h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
      
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩
      
    

/-- A closed set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) :
    IsPreconnected s ↔ ∀ u v : Set α hu : IsClosed u hv : IsClosed v hss : s ⊆ u ∪ v huv : u ∩ v = ∅, s ⊆ u ∨ s ⊆ v :=
  by
  constructor
  · intro h u v hu hv hss huv
    apply is_preconnected_iff_subset_of_disjoint_closed.1 h u v hu hv hss
    rw [huv]
    exact inter_empty s
    
  intro H
  rw [is_preconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hss huv
  have H1 := H (u ∩ s) (v ∩ s)
  rw [subset_inter_iff, subset_inter_iff] at H1
  simp only [subset.refl, and_trueₓ] at H1
  apply H1 (IsClosed.inter hu hs) (IsClosed.inter hv hs)
  · rw [← inter_distrib_right]
    apply subset_inter_iff.2
    exact ⟨hss, subset.refl s⟩
    
  · rw [inter_comm v s, inter_assoc, ← inter_assoc s, inter_self s, inter_comm, inter_assoc, inter_comm v u, huv]
    

theorem IsClopen.connected_component_subset {x} (hs : IsClopen s) (hx : x ∈ s) : ConnectedComponent x ⊆ s :=
  is_preconnected_connected_component.subset_clopen hs ⟨x, mem_connected_component, hx⟩

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
theorem connected_component_subset_Inter_clopen {x : α} :
    ConnectedComponent x ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  subset_Inter $ fun Z => Z.2.1.connected_component_subset Z.2.2

/-- A clopen set is the union of its connected components. -/
theorem IsClopen.bUnion_connected_component_eq {Z : Set α} (h : IsClopen Z) : (⋃ x ∈ Z, ConnectedComponent x) = Z :=
  subset.antisymm (Union₂_subset $ fun x => h.connected_component_subset) $ fun x hx =>
    mem_Union₂_of_mem hx mem_connected_component

/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
theorem preimage_connected_component_connected [TopologicalSpace β] {f : α → β}
    (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t})) (hcl : ∀ T : Set β, IsClosed T ↔ IsClosed (f ⁻¹' T)) (t : β) :
    IsConnected (f ⁻¹' ConnectedComponent t) := by
  have hf : surjective f := surjective.of_comp fun t : β => (connected_fibers t).1
  constructor
  · cases' hf t with s hs
    use s
    rw [mem_preimage, hs]
    exact mem_connected_component
    
  have hT : IsClosed (f ⁻¹' ConnectedComponent t) := (hcl (ConnectedComponent t)).1 is_closed_connected_component
  rw [is_preconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  let T₁ := { t' ∈ ConnectedComponent t | f ⁻¹' {t'} ⊆ u }
  let T₂ := { t' ∈ ConnectedComponent t | f ⁻¹' {t'} ⊆ v }
  have fiber_decomp : ∀, ∀ t' ∈ ConnectedComponent t, ∀, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v := by
    intro t' ht'
    apply is_preconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact subset.trans (hf.preimage_subset_preimage_iff.2 (singleton_subset_iff.2 ht')) huv
      
    rw [uv_disj]
    exact inter_empty _
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' ConnectedComponent t ∩ u := by
    apply eq_of_subset_of_subset
    · rw [← bUnion_preimage_singleton]
      refine' Union₂_subset fun t' ht' => subset_inter _ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
      
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
      
    dsimp only
    cases fiber_decomp (f a) (mem_preimage.1 hat)
    · exact h
      
    · exfalso
      rw [← not_nonempty_iff_eq_empty] at uv_disj
      exact uv_disj (nonempty_of_mem (mem_inter hau (h rfl)))
      
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' ConnectedComponent t ∩ v := by
    apply eq_of_subset_of_subset
    · rw [← bUnion_preimage_singleton]
      refine' Union₂_subset fun t' ht' => subset_inter _ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
      
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
      
    dsimp only
    cases fiber_decomp (f a) (mem_preimage.1 hat)
    · exfalso
      rw [← not_nonempty_iff_eq_empty] at uv_disj
      exact uv_disj (nonempty_of_mem (mem_inter (h rfl) hav))
      
    · exact h
      
  have hT₁ : IsClosed T₁ := (hcl T₁).2 (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := (hcl T₂).2 (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : ConnectedComponent t ⊆ T₁ ∪ T₂ := by
    intro t' ht'
    rw [mem_union t' T₁ T₂]
    cases' fiber_decomp t' ht' with htu htv
    · left
      exact ⟨ht', htu⟩
      
    right
    exact ⟨ht', htv⟩
  have T_disjoint : T₁ ∩ T₂ = ∅ := by
    rw [← image_preimage_eq (T₁ ∩ T₂) hf]
    suffices f ⁻¹' (T₁ ∩ T₂) = ∅ by
      rw [this]
      exact image_empty _
    rw [preimage_inter, T₁_u, T₂_v]
    rw [inter_comm] at uv_disj
    conv => congr rw [inter_assoc]congr skip rw [← inter_assoc, inter_comm, ← inter_assoc, uv_disj, empty_inter]
    exact inter_empty _
  cases
    (is_preconnected_iff_subset_of_fully_disjoint_closed is_closed_connected_component).1
      is_preconnected_connected_component T₁ T₂ hT₁ hT₂ T_decomp T_disjoint
  · left
    rw [subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' ConnectedComponent t ⊆ f ⁻¹' T₁ by
      exact subset.trans (subset.trans this T₁_u.1) (inter_subset_right _ _)
    exact preimage_mono h
    
  right
  rw [subset.antisymm_iff] at T₂_v
  suffices f ⁻¹' ConnectedComponent t ⊆ f ⁻¹' T₂ by
    exact subset.trans (subset.trans this T₂_v.1) (inter_subset_right _ _)
  exact preimage_mono h

theorem QuotientMap.preimage_connected_component [TopologicalSpace β] {f : α → β} (hf : QuotientMap f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) : f ⁻¹' ConnectedComponent (f a) = ConnectedComponent a :=
  ((preimage_connected_component_connected h_fibers (fun _ => hf.is_closed_preimage.symm) _).subset_connected_component
        mem_connected_component).antisymm
    (hf.continuous.maps_to_connected_component a)

theorem QuotientMap.image_connected_component [TopologicalSpace β] {f : α → β} (hf : QuotientMap f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) : f '' ConnectedComponent a = ConnectedComponent (f a) := by
  rw [← hf.preimage_connected_component h_fibers, image_preimage_eq _ hf.surjective]

end Preconnected

section TotallyDisconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, ie either empty or a singleton.-/
def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.subsingleton

theorem is_totally_disconnected_empty : IsTotallyDisconnected (∅ : Set α) := fun _ ht _ _ x_in _ _ => (ht x_in).elim

theorem is_totally_disconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) := fun _ ht _ =>
  subsingleton.mono subsingleton_singleton ht

/-- A space is totally disconnected if all of its connected components are singletons. -/
class TotallyDisconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  is_totally_disconnected_univ : IsTotallyDisconnected (univ : Set α)

theorem IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α} (h : IsPreconnected s) : s.subsingleton :=
  TotallyDisconnectedSpace.is_totally_disconnected_univ s (subset_univ s) h

instance Pi.totally_disconnected_space {α : Type _} {β : α → Type _} [t₂ : ∀ a, TopologicalSpace (β a)]
    [∀ a, TotallyDisconnectedSpace (β a)] : TotallyDisconnectedSpace (∀ a : α, β a) :=
  ⟨fun t h1 h2 =>
    have this : ∀ a, IsPreconnected ((fun x : ∀ a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).ContinuousOn
    fun x x_in y y_in => funext $ fun a => (this a).Subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

instance Prod.totally_disconnected_space [TopologicalSpace β] [TotallyDisconnectedSpace α]
    [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β) :=
  ⟨fun t h1 h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.ContinuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.ContinuousOn
    fun x hx y hy => Prod.extₓ (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩) (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

instance [TopologicalSpace β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
    TotallyDisconnectedSpace (Sum α β) := by
  refine' ⟨fun s _ hs => _⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.is_preconnected_iff.1 hs
  · exact ht.subsingleton.image _
    
  · exact ht.subsingleton.image _
    

instance [∀ i, TopologicalSpace (π i)] [∀ i, TotallyDisconnectedSpace (π i)] : TotallyDisconnectedSpace (Σ i, π i) := by
  refine' ⟨fun s _ hs => _⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact Set.subsingleton_empty
    
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.is_connected_iff.1 ⟨h, hs⟩
    exact ht.is_preconnected.subsingleton.image _
    

/-- A space is totally disconnected iff its connected components are subsingletons. -/
theorem totally_disconnected_space_iff_connected_component_subsingleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, (ConnectedComponent x).Subsingleton := by
  constructor
  · intro h x
    apply h.1
    · exact subset_univ _
      
    exact is_preconnected_connected_component
    
  intro h
  constructor
  intro s s_sub hs
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, x_in⟩)
  · exact subsingleton_empty
    
  · exact (h x).mono (hs.subset_connected_component x_in)
    

/-- A space is totally disconnected iff its connected components are singletons. -/
theorem totally_disconnected_space_iff_connected_component_singleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, ConnectedComponent x = {x} := by
  rw [totally_disconnected_space_iff_connected_component_subsingleton]
  apply forall_congrₓ fun x => _
  rw [Set.subsingleton_iff_singleton]
  exact mem_connected_component

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp]
theorem Continuous.image_connected_component_eq_singleton {β : Type _} [TopologicalSpace β] [TotallyDisconnectedSpace β]
    {f : α → β} (h : Continuous f) (a : α) : f '' ConnectedComponent a = {f a} :=
  (Set.subsingleton_iff_singleton $ mem_image_of_mem f mem_connected_component).mp
    (is_preconnected_connected_component.Image f h.continuous_on).Subsingleton

theorem is_totally_disconnected_of_totally_disconnected_space [TotallyDisconnectedSpace α] (s : Set α) :
    IsTotallyDisconnected s := fun t hts ht => TotallyDisconnectedSpace.is_totally_disconnected_univ _ t.subset_univ ht

theorem is_totally_disconnected_of_image [TopologicalSpace β] {f : α → β} (hf : ContinuousOn f s) (hf' : injective f)
    (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s := fun t hts ht x x_in y y_in =>
  hf' $ h _ (image_subset f hts) (ht.image f $ hf.mono hts) (mem_image_of_mem f x_in) (mem_image_of_mem f y_in)

theorem Embedding.is_totally_disconnected [TopologicalSpace β] {f : α → β} (hf : Embedding f) {s : Set α}
    (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  is_totally_disconnected_of_image hf.continuous.continuous_on hf.inj h

instance Subtype.totally_disconnected_space {α : Type _} {p : α → Prop} [TopologicalSpace α]
    [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Subtype p) :=
  ⟨embedding_subtype_coe.IsTotallyDisconnected (is_totally_disconnected_of_totally_disconnected_space _)⟩

end TotallyDisconnected

section TotallySeparated

/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
def IsTotallySeparated (s : Set α) : Prop :=
  ∀, ∀ x ∈ s, ∀, ∀, ∀ y ∈ s, ∀, x ≠ y → ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ u ∩ v = ∅

theorem is_totally_separated_empty : IsTotallySeparated (∅ : Set α) := fun x => False.elim

theorem is_totally_separated_singleton {x} : IsTotallySeparated ({x} : Set α) := fun p hp q hq hpq =>
  (hpq $ (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

theorem is_totally_disconnected_of_is_totally_separated {s : Set α} (H : IsTotallySeparated s) :
    IsTotallyDisconnected s := by
  intro t hts ht x x_in y y_in
  by_contra h
  obtain
    ⟨u : Set α, v : Set α, hu : IsOpen u, hv : IsOpen v, hxu : x ∈ u, hyv : y ∈ v, hs : s ⊆ u ∪ v, huv : u ∩ v = ∅⟩ :=
    H x (hts x_in) y (hts y_in) h
  have : (t ∩ u).Nonempty → (t ∩ v).Nonempty → (t ∩ (u ∩ v)).Nonempty := ht _ _ hu hv (subset.trans hts hs)
  obtain ⟨z, hz : z ∈ t ∩ (u ∩ v)⟩ := this ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩
  simpa [huv] using hz

alias is_totally_disconnected_of_is_totally_separated ← IsTotallySeparated.is_totally_disconnected

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
class TotallySeparatedSpace (α : Type u) [TopologicalSpace α] : Prop where
  is_totally_separated_univ {} : IsTotallySeparated (univ : Set α)

instance (priority := 100) TotallySeparatedSpace.totally_disconnected_space (α : Type u) [TopologicalSpace α]
    [TotallySeparatedSpace α] : TotallyDisconnectedSpace α :=
  ⟨is_totally_disconnected_of_is_totally_separated $ TotallySeparatedSpace.is_totally_separated_univ α⟩

instance (priority := 100) TotallySeparatedSpace.of_discrete (α : Type _) [TopologicalSpace α] [DiscreteTopology α] :
    TotallySeparatedSpace α :=
  ⟨fun a _ b _ h =>
    ⟨{b}ᶜ, {b}, is_open_discrete _, is_open_discrete _, by
      simpa⟩⟩

theorem exists_clopen_of_totally_separated {α : Type _} [TopologicalSpace α] [TotallySeparatedSpace α] {x y : α}
    (hxy : x ≠ y) : ∃ (U : Set α)(hU : IsClopen U), x ∈ U ∧ y ∈ Uᶜ := by
  obtain ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ :=
    TotallySeparatedSpace.is_totally_separated_univ α x (Set.mem_univ x) y (Set.mem_univ y) hxy
  have clopen_U := is_clopen_inter_of_disjoint_cover_clopen is_clopen_univ f hU hV disj
  rw [Set.univ_inter _] at clopen_U
  rw [← Set.subset_compl_iff_disjoint, Set.subset_compl_comm] at disj
  exact ⟨U, clopen_U, Ux, disj Vy⟩

end TotallySeparated

section connectedComponentSetoid

/-- The setoid of connected components of a topological space -/
def connectedComponentSetoid (α : Type _) [TopologicalSpace α] : Setoidₓ α :=
  ⟨fun x y => ConnectedComponent x = ConnectedComponent y,
    ⟨fun x => by
      trivial, fun x y h1 => h1.symm, fun x y z h1 h2 => h1.trans h2⟩⟩

/-- The quotient of a space by its connected components -/
def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotientₓ (connectedComponentSetoid α)

instance : CoeTₓ α (ConnectedComponents α) :=
  ⟨Quotientₓ.mk'⟩

namespace ConnectedComponents

@[simp]
theorem coe_eq_coe {x y : α} : (x : ConnectedComponents α) = y ↔ ConnectedComponent x = ConnectedComponent y :=
  Quotientₓ.eq'

theorem coe_ne_coe {x y : α} : (x : ConnectedComponents α) ≠ y ↔ ConnectedComponent x ≠ ConnectedComponent y :=
  not_congr coe_eq_coe

theorem coe_eq_coe' {x y : α} : (x : ConnectedComponents α) = y ↔ x ∈ ConnectedComponent y :=
  coe_eq_coe.trans ⟨fun h => h ▸ mem_connected_component, fun h => (connected_component_eq h).symm⟩

instance [Inhabited α] : Inhabited (ConnectedComponents α) :=
  ⟨↑(default : α)⟩

instance : TopologicalSpace (ConnectedComponents α) :=
  Quotientₓ.topologicalSpace

theorem surjective_coe : surjective (coe : α → ConnectedComponents α) :=
  surjective_quot_mk _

theorem quotient_map_coe : QuotientMap (coe : α → ConnectedComponents α) :=
  quotient_map_quot_mk

@[continuity]
theorem continuous_coe : Continuous (coe : α → ConnectedComponents α) :=
  quotient_map_coe.Continuous

@[simp]
theorem range_coe : range (coe : α → ConnectedComponents α) = univ :=
  surjective_coe.range_eq

end ConnectedComponents

variable [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α → β}

theorem Continuous.image_eq_of_connected_component_eq (h : Continuous f) (a b : α)
    (hab : ConnectedComponent a = ConnectedComponent b) : f a = f b :=
  singleton_eq_singleton_iff.1 $
    h.image_connected_component_eq_singleton a ▸ h.image_connected_component_eq_singleton b ▸ hab ▸ rfl

/-- The lift to `connected_components α` of a continuous map from `α` to a totally disconnected space
-/
def Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponents α → β := fun x =>
  Quotientₓ.liftOn' x f h.image_eq_of_connected_component_eq

@[continuity]
theorem Continuous.connected_components_lift_continuous (h : Continuous f) : Continuous h.connected_components_lift :=
  continuous_quotient_lift_on' h.image_eq_of_connected_component_eq h

@[simp]
theorem Continuous.connected_components_lift_apply_coe (h : Continuous f) (x : α) :
    h.connected_components_lift x = f x :=
  rfl

@[simp]
theorem Continuous.connected_components_lift_comp_coe (h : Continuous f) : h.connected_components_lift ∘ coe = f :=
  rfl

theorem connected_components_lift_unique' {β : Sort _} {g₁ g₂ : ConnectedComponents α → β}
    (hg : g₁ ∘ (coe : α → ConnectedComponents α) = g₂ ∘ coe) : g₁ = g₂ :=
  ConnectedComponents.surjective_coe.injective_comp_right hg

theorem Continuous.connected_components_lift_unique (h : Continuous f) (g : ConnectedComponents α → β)
    (hg : g ∘ coe = f) : g = h.connected_components_lift :=
  connected_components_lift_unique' $ hg.trans h.connected_components_lift_comp_coe.symm

/-- The preimage of a singleton in `connected_components` is the connected component
of an element in the equivalence class. -/
theorem connected_components_preimage_singleton {x : α} :
    coe ⁻¹' ({x} : Set (ConnectedComponents α)) = ConnectedComponent x := by
  ext y
  simp [ConnectedComponents.coe_eq_coe']

/-- The preimage of the image of a set under the quotient map to `connected_components α`
is the union of the connected components of the elements in it. -/
theorem connected_components_preimage_image (U : Set α) :
    coe ⁻¹' (coe '' U : Set (ConnectedComponents α)) = ⋃ x ∈ U, ConnectedComponent x := by
  simp only [connected_components_preimage_singleton, preimage_Union₂, image_eq_Union]

instance ConnectedComponents.totally_disconnected_space : TotallyDisconnectedSpace (ConnectedComponents α) := by
  rw [totally_disconnected_space_iff_connected_component_singleton]
  refine' connected_components.surjective_coe.forall.2 fun x => _
  rw [← connected_components.quotient_map_coe.image_connected_component, ← connected_components_preimage_singleton,
    image_preimage_eq _ ConnectedComponents.surjective_coe]
  refine' connected_components.surjective_coe.forall.2 fun y => _
  rw [connected_components_preimage_singleton]
  exact is_connected_connected_component

/-- Functoriality of `connected_components` -/
def Continuous.connectedComponentsMap {β : Type _} [TopologicalSpace β] {f : α → β} (h : Continuous f) :
    ConnectedComponents α → ConnectedComponents β :=
  Continuous.connectedComponentsLift (continuous_quotient_mk.comp h)

theorem Continuous.connected_components_map_continuous {β : Type _} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : Continuous h.connected_components_map :=
  Continuous.connected_components_lift_continuous (continuous_quotient_mk.comp h)

end connectedComponentSetoid

