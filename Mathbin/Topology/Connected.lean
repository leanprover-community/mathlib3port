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

variable {α : Type u} {β : Type v} [TopologicalSpace α] {s t u v : Set α}

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

theorem IsPreirreducible.is_preconnected {s : Set α} (H : IsPreirreducible s) : IsPreconnected s :=
  fun _ _ hu hv _ => H _ _ hu hv

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

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall
{s : set α}
(x : α)
(H : ∀
 y «expr ∈ » s, «expr∃ , »((t «expr ⊆ » s), «expr ∧ »(«expr ∈ »(x, t), «expr ∧ »(«expr ∈ »(y, t), is_preconnected t)))) : is_preconnected s :=
begin
  rintros [ident u, ident v, ident hu, ident hv, ident hs, "⟨", ident z, ",", ident zs, ",", ident zu, "⟩", "⟨", ident y, ",", ident ys, ",", ident yv, "⟩"],
  have [ident xs] [":", expr «expr ∈ »(x, s)] [],
  by { rcases [expr H y ys, "with", "⟨", ident t, ",", ident ts, ",", ident xt, ",", ident yt, ",", ident ht, "⟩"],
    exact [expr ts xt] },
  wlog [ident xu] [":", expr «expr ∈ »(x, u)] [":=", expr hs xs] ["using", "[", ident u, ident v, ident y, ident z, ",", ident v, ident u, ident z, ident y, "]"],
  rcases [expr H y ys, "with", "⟨", ident t, ",", ident ts, ",", ident xt, ",", ident yt, ",", ident ht, "⟩"],
  have [] [] [":=", expr ht u v hu hv (subset.trans ts hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩],
  exact [expr this.imp (λ z hz, ⟨ts hz.1, hz.2⟩)]
end

/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
theorem is_preconnected_of_forall_pair {s : Set α}
  (H : ∀ x y _ : x ∈ s _ : y ∈ s, ∃ (t : _)(_ : t ⊆ s), x ∈ t ∧ y ∈ t ∧ IsPreconnected t) : IsPreconnected s :=
  by 
    rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    exacts[is_preconnected_empty, is_preconnected_of_forall x fun y => H x y hx]

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
theorem is_preconnected_sUnion (x : α) (c : Set (Set α)) (H1 : ∀ s _ : s ∈ c, x ∈ s)
  (H2 : ∀ s _ : s ∈ c, IsPreconnected s) : IsPreconnected (⋃₀c) :=
  by 
    apply is_preconnected_of_forall x 
    rintro y ⟨s, sc, ys⟩
    exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩

theorem is_preconnected_Union {ι : Sort _} {s : ι → Set α} (h₁ : (⋂i, s i).Nonempty) (h₂ : ∀ i, IsPreconnected (s i)) :
  IsPreconnected (⋃i, s i) :=
  Exists.elim h₁$ fun f hf => is_preconnected_sUnion f _ hf (forall_range_iff.2 h₂)

theorem IsPreconnected.union (x : α) {s t : Set α} (H1 : x ∈ s) (H2 : x ∈ t) (H3 : IsPreconnected s)
  (H4 : IsPreconnected t) : IsPreconnected (s ∪ t) :=
  sUnion_pair s t ▸
    is_preconnected_sUnion x {s, t}
      (by 
        rintro r (rfl | rfl | h) <;> assumption)
      (by 
        rintro r (rfl | rfl | h) <;> assumption)

theorem IsConnected.union {s t : Set α} (H : (s ∩ t).Nonempty) (Hs : IsConnected s) (Ht : IsConnected t) :
  IsConnected (s ∪ t) :=
  by 
    rcases H with ⟨x, hx⟩
    refine' ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, _⟩
    exact
      IsPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx) Hs.is_preconnected
        Ht.is_preconnected

/-- Theorem of bark and tree :
if a set is within a (pre)connected set and its closure,
then it is (pre)connected as well. -/
theorem IsPreconnected.subset_closure {s : Set α} {t : Set α} (H : IsPreconnected s) (Kst : s ⊆ t)
  (Ktcs : t ⊆ Closure s) : IsPreconnected t :=
  fun u v hu hv htuv ⟨y, hyt, hyu⟩ ⟨z, hzt, hzv⟩ =>
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
  IsPreconnected.subset_closure H subset_closure$ subset.refl$ Closure s

theorem IsConnected.closure {s : Set α} (H : IsConnected s) : IsConnected (Closure s) :=
  IsConnected.subset_closure H subset_closure$ subset.refl$ Closure s

/-- The image of a (pre)connected set is (pre)connected as well. -/
theorem IsPreconnected.image [TopologicalSpace β] {s : Set α} (H : IsPreconnected s) (f : α → β)
  (hf : ContinuousOn f s) : IsPreconnected (f '' s) :=
  by 
    rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
    rcases continuous_on_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
    rcases continuous_on_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
    replace huv : s ⊆ u' ∪ v'
    ·
      rw [image_subset_iff, preimage_union] at huv 
      replace huv := subset_inter huv (subset.refl _)
      rw [inter_distrib_right, u'_eq, v'_eq, ←inter_distrib_right] at huv 
      exact (subset_inter_iff.1 huv).1
    obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).Nonempty
    ·
      refine' H u' v' hu' hv' huv ⟨x, _⟩ ⟨y, _⟩ <;> rw [inter_comm]
      exacts[u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
    rw [←inter_self s, inter_assoc, inter_left_comm s u', ←inter_assoc, inter_comm s, inter_comm s, ←u'_eq, ←v'_eq] at
      hz 
    exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩

theorem IsConnected.image [TopologicalSpace β] {s : Set α} (H : IsConnected s) (f : α → β) (hf : ContinuousOn f s) :
  IsConnected (f '' s) :=
  ⟨nonempty_image_iff.mpr H.nonempty, H.is_preconnected.image f hf⟩

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_preconnected_closed_iff
{s : set α} : «expr ↔ »(is_preconnected s, ∀
 t
 t', is_closed t → is_closed t' → «expr ⊆ »(s, «expr ∪ »(t, t')) → «expr ∩ »(s, t).nonempty → «expr ∩ »(s, t').nonempty → «expr ∩ »(s, «expr ∩ »(t, t')).nonempty) :=
⟨begin
   rintros [ident h, ident t, ident t', ident ht, ident ht', ident htt', "⟨", ident x, ",", ident xs, ",", ident xt, "⟩", "⟨", ident y, ",", ident ys, ",", ident yt', "⟩"],
   by_contradiction [ident h'],
   rw ["[", "<-", expr ne_empty_iff_nonempty, ",", expr ne.def, ",", expr not_not, ",", "<-", expr subset_compl_iff_disjoint, ",", expr compl_inter, "]"] ["at", ident h'],
   have [ident xt'] [":", expr «expr ∉ »(x, t')] [],
   from [expr (h' xs).elim (absurd xt) id],
   have [ident yt] [":", expr «expr ∉ »(y, t)] [],
   from [expr (h' ys).elim id (absurd yt')],
   have [] [] [":=", expr ne_empty_iff_nonempty.2 (h «expr ᶜ»(t) «expr ᶜ»(t') (is_open_compl_iff.2 ht) (is_open_compl_iff.2 ht') h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩)],
   rw ["[", expr ne.def, ",", "<-", expr compl_union, ",", "<-", expr subset_compl_iff_disjoint, ",", expr compl_compl, "]"] ["at", ident this],
   contradiction
 end, begin
   rintros [ident h, ident u, ident v, ident hu, ident hv, ident huv, "⟨", ident x, ",", ident xs, ",", ident xu, "⟩", "⟨", ident y, ",", ident ys, ",", ident yv, "⟩"],
   by_contradiction [ident h'],
   rw ["[", "<-", expr ne_empty_iff_nonempty, ",", expr ne.def, ",", expr not_not, ",", "<-", expr subset_compl_iff_disjoint, ",", expr compl_inter, "]"] ["at", ident h'],
   have [ident xv] [":", expr «expr ∉ »(x, v)] [],
   from [expr (h' xs).elim (absurd xu) id],
   have [ident yu] [":", expr «expr ∉ »(y, u)] [],
   from [expr (h' ys).elim id (absurd yv)],
   have [] [] [":=", expr ne_empty_iff_nonempty.2 (h «expr ᶜ»(u) «expr ᶜ»(v) (is_closed_compl_iff.2 hu) (is_closed_compl_iff.2 hv) h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩)],
   rw ["[", expr ne.def, ",", "<-", expr compl_union, ",", "<-", expr subset_compl_iff_disjoint, ",", expr compl_compl, "]"] ["at", ident this],
   contradiction
 end⟩

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_preconnected.preimage_of_open_map
[topological_space β]
{s : set β}
(hs : is_preconnected s)
{f : α → β}
(hinj : function.injective f)
(hf : is_open_map f)
(hsf : «expr ⊆ »(s, set.range f)) : is_preconnected «expr ⁻¹' »(f, s) :=
λ u v hu hv hsuv hsu hsv, begin
  obtain ["⟨", ident b, ",", ident hbs, ",", ident hbu, ",", ident hbv, "⟩", ":=", expr hs «expr '' »(f, u) «expr '' »(f, v) (hf u hu) (hf v hv) _ _ _],
  obtain ["⟨", ident a, ",", ident rfl, "⟩", ":=", expr hsf hbs],
  rw [expr hinj.mem_set_image] ["at", ident hbu, ident hbv],
  exact [expr ⟨a, hbs, hbu, hbv⟩],
  { have [] [] [":=", expr set.image_subset f hsuv],
    rwa ["[", expr set.image_preimage_eq_of_subset hsf, ",", expr set.image_union, "]"] ["at", ident this] },
  { obtain ["⟨", ident x, ",", ident hx1, ",", ident hx2, "⟩", ":=", expr hsu],
    exact [expr ⟨f x, hx1, x, hx2, rfl⟩] },
  { obtain ["⟨", ident y, ",", ident hy1, ",", ident hy2, "⟩", ":=", expr hsv],
    exact [expr ⟨f y, hy1, y, hy2, rfl⟩] }
end

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_preconnected.preimage_of_closed_map
[topological_space β]
{s : set β}
(hs : is_preconnected s)
{f : α → β}
(hinj : function.injective f)
(hf : is_closed_map f)
(hsf : «expr ⊆ »(s, set.range f)) : is_preconnected «expr ⁻¹' »(f, s) :=
«expr $ »(is_preconnected_closed_iff.2, λ u v hu hv hsuv hsu hsv, begin
   obtain ["⟨", ident b, ",", ident hbs, ",", ident hbu, ",", ident hbv, "⟩", ":=", expr is_preconnected_closed_iff.1 hs «expr '' »(f, u) «expr '' »(f, v) (hf u hu) (hf v hv) _ _ _],
   obtain ["⟨", ident a, ",", ident rfl, "⟩", ":=", expr hsf hbs],
   rw [expr hinj.mem_set_image] ["at", ident hbu, ident hbv],
   exact [expr ⟨a, hbs, hbu, hbv⟩],
   { have [] [] [":=", expr set.image_subset f hsuv],
     rwa ["[", expr set.image_preimage_eq_of_subset hsf, ",", expr set.image_union, "]"] ["at", ident this] },
   { obtain ["⟨", ident x, ",", ident hx1, ",", ident hx2, "⟩", ":=", expr hsu],
     exact [expr ⟨f x, hx1, x, hx2, rfl⟩] },
   { obtain ["⟨", ident y, ",", ident hy1, ",", ident hy2, "⟩", ":=", expr hsv],
     exact [expr ⟨f y, hy1, y, hy2, rfl⟩] }
 end)

theorem IsConnected.preimage_of_open_map [TopologicalSpace β] {s : Set β} (hs : IsConnected s) {f : α → β}
  (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ Set.Range f) : IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.is_preconnected.preimage_of_open_map hinj hf hsf⟩

theorem IsConnected.preimage_of_closed_map [TopologicalSpace β] {s : Set β} (hs : IsConnected s) {f : α → β}
  (hinj : Function.Injective f) (hf : IsClosedMap f) (hsf : s ⊆ Set.Range f) : IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.is_preconnected.preimage_of_closed_map hinj hf hsf⟩

theorem IsPreconnected.subset_or_subset (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v)
  (hs : IsPreconnected s) : s ⊆ u ∨ s ⊆ v :=
  by 
    specialize hs u v hu hv hsuv 
    obtain hsu | hsu := (s ∩ u).eq_empty_or_nonempty
    ·
      exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
    ·
      replace hs := mt (hs hsu)
      simpRw [Set.not_nonempty_iff_eq_empty, ←Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff_inter_eq_empty.1 huv]
         at hs 
      exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)

theorem IsPreconnected.subset_left_of_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
  (hsuv : s ⊆ u ∪ v) (hsu : (s ∩ u).Nonempty) (hs : IsPreconnected s) : s ⊆ u :=
  Disjoint.subset_left_of_subset_union hsuv
    (by 
      byContra hsv 
      rw [Set.not_disjoint_iff_nonempty_inter] at hsv 
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv 
      exact Set.disjoint_iff.1 huv hx)

theorem IsPreconnected.subset_right_of_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
  (hsuv : s ⊆ u ∪ v) (hsv : (s ∩ v).Nonempty) (hs : IsPreconnected s) : s ⊆ v :=
  Disjoint.subset_right_of_subset_union hsuv
    (by 
      byContra hsu 
      rw [Set.not_disjoint_iff_nonempty_inter] at hsu 
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv 
      exact Set.disjoint_iff.1 huv hx)

theorem IsPreconnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsPreconnected s)
  (ht : IsPreconnected t) : IsPreconnected (s.prod t) :=
  by 
    apply is_preconnected_of_forall_pair 
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨ha₁, hb₁⟩ ⟨ha₂, hb₂⟩
    refine' ⟨Prod.mk a₁ '' t ∪ flip Prod.mk b₂ '' s, _, Or.inl ⟨b₁, hb₁, rfl⟩, Or.inr ⟨a₂, ha₂, rfl⟩, _⟩
    ·
      rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
      exacts[⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
    ·
      exact
        (ht.image _ (Continuous.Prod.mk _).ContinuousOn).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩ ⟨a₁, ha₁, rfl⟩
          (hs.image _ (continuous_id.prod_mk continuous_const).ContinuousOn)

theorem IsConnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConnected s) (ht : IsConnected t) :
  IsConnected (s.prod t) :=
  ⟨hs.1.Prod ht.1, hs.2.Prod ht.2⟩

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_preconnected_univ_pi
{ι : Type*}
{π : ι → Type*}
[∀ i, topological_space (π i)]
{s : ∀ i, set (π i)}
(hs : ∀ i, is_preconnected (s i)) : is_preconnected (pi univ s) :=
begin
  rintros [ident u, ident v, ident uo, ident vo, ident hsuv, "⟨", ident f, ",", ident hfs, ",", ident hfu, "⟩", "⟨", ident g, ",", ident hgs, ",", ident hgv, "⟩"],
  rcases [expr exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g, "with", "⟨", ident I, ",", ident hI, "⟩"],
  induction [expr I] ["using", ident finset.induction_on] ["with", ident i, ident I, ident hi, ident ihI] [],
  { refine [expr ⟨g, hgs, ⟨_, hgv⟩⟩],
    simpa [] [] [] [] [] ["using", expr hI] },
  { rw ["[", expr finset.piecewise_insert, "]"] ["at", ident hI],
    have [] [] [":=", expr I.piecewise_mem_set_pi hfs hgs],
    refine [expr (hsuv this).elim ihI (λ h, _)],
    set [] [ident S] [] [":="] [expr «expr '' »(update (I.piecewise f g) i, s i)] [],
    have [ident hsub] [":", expr «expr ⊆ »(S, pi univ s)] [],
    { refine [expr image_subset_iff.2 (λ z hz, _)],
      rwa [expr update_preimage_univ_pi] [],
      exact [expr λ j hj, this j trivial] },
    have [ident hconn] [":", expr is_preconnected S] [],
    from [expr (hs i).image _ (continuous_const.update i continuous_id).continuous_on],
    have [ident hSu] [":", expr «expr ∩ »(S, u).nonempty] [],
    from [expr ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩],
    have [ident hSv] [":", expr «expr ∩ »(S, v).nonempty] [],
    from [expr ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩],
    refine [expr (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono _],
    exact [expr inter_subset_inter_left _ hsub] }
end

@[simp]
theorem is_connected_univ_pi {ι : Type _} {π : ι → Type _} [∀ i, TopologicalSpace (π i)] {s : ∀ i, Set (π i)} :
  IsConnected (pi univ s) ↔ ∀ i, IsConnected (s i) :=
  by 
    simp only [IsConnected, ←univ_pi_nonempty_iff, forall_and_distrib, And.congr_right_iff]
    refine' fun hne => ⟨fun hc i => _, is_preconnected_univ_pi⟩
    rw [←eval_image_univ_pi hne]
    exact hc.image _ (continuous_apply _).ContinuousOn

/-- The connected component of a point is the maximal connected set
that contains this point. -/
def ConnectedComponent (x : α) : Set α :=
  ⋃₀{ s:Set α | IsPreconnected s ∧ x ∈ s }

/-- The connected component of a point inside a set. -/
def ConnectedComponentIn (F : Set α) (x : F) : Set α :=
  coeₓ '' ConnectedComponent x

theorem mem_connected_component {x : α} : x ∈ ConnectedComponent x :=
  mem_sUnion_of_mem (mem_singleton x) ⟨is_connected_singleton.IsPreconnected, mem_singleton x⟩

theorem is_preconnected_connected_component {x : α} : IsPreconnected (ConnectedComponent x) :=
  is_preconnected_sUnion x _ (fun _ => And.right) fun _ => And.left

theorem is_connected_connected_component {x : α} : IsConnected (ConnectedComponent x) :=
  ⟨⟨x, mem_connected_component⟩, is_preconnected_connected_component⟩

theorem IsPreconnected.subset_connected_component {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x ∈ s) :
  s ⊆ ConnectedComponent x :=
  fun z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩

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
  closure_eq_iff_is_closed.1$
    subset.antisymm
      (is_connected_connected_component.closure.subset_connected_component (subset_closure mem_connected_component))
      subset_closure

theorem Continuous.image_connected_component_subset {β : Type _} [TopologicalSpace β] {f : α → β} (h : Continuous f)
  (a : α) : f '' ConnectedComponent a ⊆ ConnectedComponent (f a) :=
  (is_connected_connected_component.Image f h.continuous_on).subset_connected_component
    ((mem_image f (ConnectedComponent a) (f a)).2 ⟨a, mem_connected_component, rfl⟩)

theorem irreducible_component_subset_connected_component {x : α} : IrreducibleComponent x ⊆ ConnectedComponent x :=
  is_irreducible_irreducible_component.IsConnected.subset_connected_component mem_irreducible_component

/-- A preconnected space is one where there is no non-trivial open partition. -/
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where 
  is_preconnected_univ : IsPreconnected (univ : Set α)

export PreconnectedSpace(is_preconnected_univ)

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

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem connected_space_iff_connected_component : «expr ↔ »(connected_space α, «expr∃ , »((x : α), «expr = »(connected_component x, univ))) :=
begin
  split,
  { rintros ["⟨", ident h, ",", "⟨", ident x, "⟩", "⟩"],
    exactI [expr ⟨x, «expr $ »(eq_univ_of_univ_subset, is_preconnected_univ.subset_connected_component (mem_univ x))⟩] },
  { rintros ["⟨", ident x, ",", ident h, "⟩"],
    haveI [] [":", expr preconnected_space α] [":=", expr ⟨by { rw ["<-", expr h] [],
        exact [expr is_preconnected_connected_component] }⟩],
    exact [expr ⟨⟨x⟩⟩] }
end

instance [TopologicalSpace β] [PreconnectedSpace α] [PreconnectedSpace β] : PreconnectedSpace (α × β) :=
  ⟨by 
      rw [←univ_prod_univ]
      exact is_preconnected_univ.prod is_preconnected_univ⟩

instance [TopologicalSpace β] [ConnectedSpace α] [ConnectedSpace β] : ConnectedSpace (α × β) :=
  ⟨Prod.nonempty⟩

instance {ι : Type _} {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [∀ i, PreconnectedSpace (π i)] :
  PreconnectedSpace (∀ i, π i) :=
  ⟨by 
      rw [←pi_univ univ]
      exact is_preconnected_univ_pi fun i => is_preconnected_univ⟩

instance {ι : Type _} {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [∀ i, ConnectedSpace (π i)] :
  ConnectedSpace (∀ i, π i) :=
  ⟨Classical.nonempty_pi.2$
      fun i =>
        by 
          infer_instance⟩

instance (priority := 100) PreirreducibleSpace.preconnected_space (α : Type u) [TopologicalSpace α]
  [PreirreducibleSpace α] : PreconnectedSpace α :=
  ⟨(PreirreducibleSpace.is_preirreducible_univ α).IsPreconnected⟩

instance (priority := 100) IrreducibleSpace.connected_space (α : Type u) [TopologicalSpace α] [IrreducibleSpace α] :
  ConnectedSpace α :=
  { to_nonempty := IrreducibleSpace.to_nonempty α }

theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
  IsOpen s → IsOpen t → s ∪ t = univ → s.nonempty → t.nonempty → (s ∩ t).Nonempty :=
  by 
    simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.is_preconnected_univ α _ _ s t

theorem is_clopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
      Classical.by_contradiction$
        fun h =>
          have h1 : s ≠ ∅ ∧ «expr ᶜ» s ≠ ∅ :=
            ⟨mt Or.inl h,
              mt
                (fun h2 =>
                  Or.inr$
                    (by 
                      rw [←compl_compl s, h2, compl_empty] :
                    s = univ))
                h⟩
          let ⟨_, h2, h3⟩ :=
            nonempty_inter hs.1 hs.2.is_open_compl (union_compl_self s) (ne_empty_iff_nonempty.1 h1.1)
              (ne_empty_iff_nonempty.1 h1.2)
          h3 h2,
    by 
      rintro (rfl | rfl) <;> [exact is_clopen_empty, exact is_clopen_univ]⟩

theorem eq_univ_of_nonempty_clopen [PreconnectedSpace α] {s : Set α} (h : s.nonempty) (h' : IsClopen s) : s = univ :=
  by 
    rw [is_clopen_iff] at h' 
    finish [h.ne_empty]

theorem Subtype.preconnected_space {s : Set α} (h : IsPreconnected s) : PreconnectedSpace s :=
  { is_preconnected_univ :=
      by 
        intro u v hu hv hs hsu hsv 
        rw [is_open_induced_iff] at hu hv 
        rcases hu with ⟨u, hu, rfl⟩
        rcases hv with ⟨v, hv, rfl⟩
        rcases hsu with ⟨⟨x, hxs⟩, hxs', hxu⟩
        rcases hsv with ⟨⟨y, hys⟩, hys', hyv⟩
        rcases h u v hu hv _ ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨z, hzs, ⟨hzu, hzv⟩⟩
        exact ⟨⟨z, hzs⟩, ⟨Set.mem_univ _, ⟨hzu, hzv⟩⟩⟩
        intro z hz 
        rcases hs (mem_univ ⟨z, hz⟩) with (hzu | hzv)
        ·
          left 
          assumption
        ·
          right 
          assumption }

theorem Subtype.connected_space {s : Set α} (h : IsConnected s) : ConnectedSpace s :=
  { is_preconnected_univ := (Subtype.preconnected_space h.is_preconnected).is_preconnected_univ,
    to_nonempty := h.nonempty.to_subtype }

theorem is_preconnected_iff_preconnected_space {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s :=
  ⟨Subtype.preconnected_space,
    by 
      intro 
      simpa using is_preconnected_univ.image (coeₓ : s → α) continuous_subtype_coe.continuous_on⟩

theorem is_connected_iff_connected_space {s : Set α} : IsConnected s ↔ ConnectedSpace s :=
  ⟨Subtype.connected_space, fun h => ⟨nonempty_subtype.mp h.2, is_preconnected_iff_preconnected_space.mpr h.1⟩⟩

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A set `s` is preconnected if and only if
for every cover by two open sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint
{s : set α} : «expr ↔ »(is_preconnected s, ∀
 (u v : set α)
 (hu : is_open u)
 (hv : is_open v)
 (hs : «expr ⊆ »(s, «expr ∪ »(u, v)))
 (huv : «expr = »(«expr ∩ »(s, «expr ∩ »(u, v)), «expr∅»())), «expr ∨ »(«expr ⊆ »(s, u), «expr ⊆ »(s, v))) :=
begin
  split; intro [ident h],
  { intros [ident u, ident v, ident hu, ident hv, ident hs, ident huv],
    specialize [expr h u v hu hv hs],
    contrapose ["!"] [ident huv],
    rw [expr ne_empty_iff_nonempty] [],
    simp [] [] [] ["[", expr not_subset, "]"] [] ["at", ident huv],
    rcases [expr huv, "with", "⟨", "⟨", ident x, ",", ident hxs, ",", ident hxu, "⟩", ",", "⟨", ident y, ",", ident hys, ",", ident hyv, "⟩", "⟩"],
    have [ident hxv] [":", expr «expr ∈ »(x, v)] [":=", expr or_iff_not_imp_left.mp (hs hxs) hxu],
    have [ident hyu] [":", expr «expr ∈ »(y, u)] [":=", expr or_iff_not_imp_right.mp (hs hys) hyv],
    exact [expr h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩] },
  { intros [ident u, ident v, ident hu, ident hv, ident hs, ident hsu, ident hsv],
    rw ["<-", expr ne_empty_iff_nonempty] [],
    intro [ident H],
    specialize [expr h u v hu hv hs H],
    contrapose [] [ident H],
    apply [expr ne_empty_iff_nonempty.mpr],
    cases [expr h] [],
    { rcases [expr hsv, "with", "⟨", ident x, ",", ident hxs, ",", ident hxv, "⟩"],
      exact [expr ⟨x, hxs, ⟨h hxs, hxv⟩⟩] },
    { rcases [expr hsu, "with", "⟨", ident x, ",", ident hxs, ",", ident hxu, "⟩"],
      exact [expr ⟨x, hxs, ⟨hxu, h hxs⟩⟩] } }
end

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
theorem is_connected_iff_sUnion_disjoint_open
{s : set α} : «expr ↔ »(is_connected s, ∀
 (U : finset (set α))
 (H : ∀ u v : set α, «expr ∈ »(u, U) → «expr ∈ »(v, U) → «expr ∩ »(s, «expr ∩ »(u, v)).nonempty → «expr = »(u, v))
 (hU : ∀ u «expr ∈ » U, is_open u)
 (hs : «expr ⊆ »(s, «expr⋃₀ »(«expr↑ »(U)))), «expr∃ , »((u «expr ∈ » U), «expr ⊆ »(s, u))) :=
begin
  rw ["[", expr is_connected, ",", expr is_preconnected_iff_subset_of_disjoint, "]"] [],
  split; intro [ident h],
  { intro [ident U],
    apply [expr finset.induction_on U],
    { rcases [expr h.left],
      suffices [] [":", expr «expr ⊆ »(s, «expr∅»()) → false],
      { simpa [] [] [] [] [] [] },
      intro [],
      solve_by_elim [] [] [] [] },
    { intros [ident u, ident U, ident hu, ident IH, ident hs, ident hU, ident H],
      rw ["[", expr finset.coe_insert, ",", expr sUnion_insert, "]"] ["at", ident H],
      cases [expr h.2 u «expr⋃₀ »(«expr↑ »(U)) _ _ H _] ["with", ident hsu, ident hsU],
      { exact [expr ⟨u, finset.mem_insert_self _ _, hsu⟩] },
      { rcases [expr IH _ _ hsU, "with", "⟨", ident v, ",", ident hvU, ",", ident hsv, "⟩"],
        { exact [expr ⟨v, finset.mem_insert_of_mem hvU, hsv⟩] },
        { intros [],
          apply [expr hs]; solve_by_elim [] [] ["[", expr finset.mem_insert_of_mem, "]"] [] },
        { intros [],
          solve_by_elim [] [] ["[", expr finset.mem_insert_of_mem, "]"] [] } },
      { solve_by_elim [] [] ["[", expr finset.mem_insert_self, "]"] [] },
      { apply [expr is_open_sUnion],
        intros [],
        solve_by_elim [] [] ["[", expr finset.mem_insert_of_mem, "]"] [] },
      { apply [expr eq_empty_of_subset_empty],
        rintro [ident x, "⟨", ident hxs, ",", ident hxu, ",", ident hxU, "⟩"],
        rw [expr mem_sUnion] ["at", ident hxU],
        rcases [expr hxU, "with", "⟨", ident v, ",", ident hvU, ",", ident hxv, "⟩"],
        rcases [expr hs u v (finset.mem_insert_self _ _) (finset.mem_insert_of_mem hvU) _, "with", ident rfl],
        { contradiction },
        { exact [expr ⟨x, hxs, hxu, hxv⟩] } } } },
  { split,
    { rw ["<-", expr ne_empty_iff_nonempty] [],
      by_contradiction [ident hs],
      subst [expr hs],
      simpa [] [] [] [] [] ["using", expr h «expr∅»() _ _ _]; simp [] [] [] [] [] [] },
    intros [ident u, ident v, ident hu, ident hv, ident hs, ident hsuv],
    rcases [expr h {u, v} _ _ _, "with", "⟨", ident t, ",", ident ht, ",", ident ht', "⟩"],
    { rw ["[", expr finset.mem_insert, ",", expr finset.mem_singleton, "]"] ["at", ident ht],
      rcases [expr ht, "with", ident rfl, "|", ident rfl]; tauto [] },
    { intros [ident t₁, ident t₂, ident ht₁, ident ht₂, ident hst],
      rw ["<-", expr ne_empty_iff_nonempty] ["at", ident hst],
      rw ["[", expr finset.mem_insert, ",", expr finset.mem_singleton, "]"] ["at", ident ht₁, ident ht₂],
      rcases [expr ht₁, "with", ident rfl, "|", ident rfl]; rcases [expr ht₂, "with", ident rfl, "|", ident rfl],
      all_goals { refl <|> contradiction <|> skip },
      rw [expr inter_comm t₁] ["at", ident hst],
      contradiction },
    { intro [ident t],
      rw ["[", expr finset.mem_insert, ",", expr finset.mem_singleton, "]"] [],
      rintro ["(", ident rfl, "|", ident rfl, ")"]; assumption },
    { simpa [] [] [] [] [] ["using", expr hs] } }
end

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem subset_or_disjoint_of_clopen
{α : Type*}
[topological_space α]
{s t : set α}
(h : is_preconnected t)
(h1 : is_clopen s) : «expr ∨ »(«expr = »(«expr ∩ »(s, t), «expr∅»()), «expr ⊆ »(t, s)) :=
begin
  by_contradiction [ident h2],
  have [ident h3] [":", expr «expr ∩ »(s, t).nonempty] [":=", expr ne_empty_iff_nonempty.mp (mt or.inl h2)],
  have [ident h4] [":", expr «expr ∩ »(t, «expr ᶜ»(s)).nonempty] [],
  { apply [expr inter_compl_nonempty_iff.2],
    push_neg ["at", ident h2],
    exact [expr h2.2] },
  rw ["[", expr inter_comm, "]"] ["at", ident h3],
  apply [expr ne_empty_iff_nonempty.2 (h s «expr ᶜ»(s) h1.1 (is_open_compl_iff.2 h1.2) _ h3 h4)],
  { rw ["[", expr inter_compl_self, ",", expr inter_empty, "]"] [] },
  { rw ["[", expr union_compl_self, "]"] [],
    exact [expr subset_univ t] }
end

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_disjoint_closed
{α : Type*}
{s : set α}
[topological_space α] : «expr ↔ »(is_preconnected s, ∀
 (u v : set α)
 (hu : is_closed u)
 (hv : is_closed v)
 (hs : «expr ⊆ »(s, «expr ∪ »(u, v)))
 (huv : «expr = »(«expr ∩ »(s, «expr ∩ »(u, v)), «expr∅»())), «expr ∨ »(«expr ⊆ »(s, u), «expr ⊆ »(s, v))) :=
begin
  split; intro [ident h],
  { intros [ident u, ident v, ident hu, ident hv, ident hs, ident huv],
    rw [expr is_preconnected_closed_iff] ["at", ident h],
    specialize [expr h u v hu hv hs],
    contrapose ["!"] [ident huv],
    rw [expr ne_empty_iff_nonempty] [],
    simp [] [] [] ["[", expr not_subset, "]"] [] ["at", ident huv],
    rcases [expr huv, "with", "⟨", "⟨", ident x, ",", ident hxs, ",", ident hxu, "⟩", ",", "⟨", ident y, ",", ident hys, ",", ident hyv, "⟩", "⟩"],
    have [ident hxv] [":", expr «expr ∈ »(x, v)] [":=", expr or_iff_not_imp_left.mp (hs hxs) hxu],
    have [ident hyu] [":", expr «expr ∈ »(y, u)] [":=", expr or_iff_not_imp_right.mp (hs hys) hyv],
    exact [expr h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩] },
  { rw [expr is_preconnected_closed_iff] [],
    intros [ident u, ident v, ident hu, ident hv, ident hs, ident hsu, ident hsv],
    rw ["<-", expr ne_empty_iff_nonempty] [],
    intro [ident H],
    specialize [expr h u v hu hv hs H],
    contrapose [] [ident H],
    apply [expr ne_empty_iff_nonempty.mpr],
    cases [expr h] [],
    { rcases [expr hsv, "with", "⟨", ident x, ",", ident hxs, ",", ident hxv, "⟩"],
      exact [expr ⟨x, hxs, ⟨h hxs, hxv⟩⟩] },
    { rcases [expr hsu, "with", "⟨", ident x, ",", ident hxs, ",", ident hxu, "⟩"],
      exact [expr ⟨x, hxs, ⟨hxu, h hxs⟩⟩] } }
end

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A closed set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint,
it is contained in one of the two covering sets. -/
theorem is_preconnected_iff_subset_of_fully_disjoint_closed
{s : set α}
(hs : is_closed s) : «expr ↔ »(is_preconnected s, ∀
 (u v : set α)
 (hu : is_closed u)
 (hv : is_closed v)
 (hss : «expr ⊆ »(s, «expr ∪ »(u, v)))
 (huv : «expr = »(«expr ∩ »(u, v), «expr∅»())), «expr ∨ »(«expr ⊆ »(s, u), «expr ⊆ »(s, v))) :=
begin
  split,
  { intros [ident h, ident u, ident v, ident hu, ident hv, ident hss, ident huv],
    apply [expr is_preconnected_iff_subset_of_disjoint_closed.1 h u v hu hv hss],
    rw [expr huv] [],
    exact [expr inter_empty s] },
  intro [ident H],
  rw [expr is_preconnected_iff_subset_of_disjoint_closed] [],
  intros [ident u, ident v, ident hu, ident hv, ident hss, ident huv],
  have [ident H1] [] [":=", expr H «expr ∩ »(u, s) «expr ∩ »(v, s)],
  rw ["[", expr subset_inter_iff, ",", expr subset_inter_iff, "]"] ["at", ident H1],
  simp [] [] ["only"] ["[", expr subset.refl, ",", expr and_true, "]"] [] ["at", ident H1],
  apply [expr H1 (is_closed.inter hu hs) (is_closed.inter hv hs)],
  { rw ["<-", expr inter_distrib_right] [],
    apply [expr subset_inter_iff.2],
    exact [expr ⟨hss, subset.refl s⟩] },
  { rw ["[", expr inter_comm v s, ",", expr inter_assoc, ",", "<-", expr inter_assoc s, ",", expr inter_self s, ",", expr inter_comm, ",", expr inter_assoc, ",", expr inter_comm v u, ",", expr huv, "]"] [] }
end

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
theorem connected_component_subset_Inter_clopen {x : α} :
  ConnectedComponent x ⊆ ⋂Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  by 
    apply subset_Inter fun Z => _ 
    cases subset_or_disjoint_of_clopen (@is_connected_connected_component _ _ x).2 Z.2.1
    ·
      exfalso 
      apply nonempty.ne_empty (nonempty_of_mem (mem_inter (@mem_connected_component _ _ x) Z.2.2))
      rw [inter_comm]
      exact h 
    exact h

/-- A clopen set is the union of its connected components. -/
theorem IsClopen.eq_union_connected_components {Z : Set α} (h : IsClopen Z) :
  Z = ⋃(x : α)(H : x ∈ Z), ConnectedComponent x :=
  eq_of_subset_of_subset (fun x xZ => mem_Union.2 ⟨x, mem_Union.2 ⟨xZ, mem_connected_component⟩⟩)
    (Union_subset$
      fun x =>
        Union_subset$
          fun xZ =>
            by 
              apply subset.trans connected_component_subset_Inter_clopen (Inter_subset _ ⟨Z, ⟨h, xZ⟩⟩))

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
theorem preimage_connected_component_connected
{β : Type*}
[topological_space β]
{f : α → β}
(connected_fibers : ∀ t : β, is_connected «expr ⁻¹' »(f, {t}))
(hcl : ∀ T : set β, «expr ↔ »(is_closed T, is_closed «expr ⁻¹' »(f, T)))
(t : β) : is_connected «expr ⁻¹' »(f, connected_component t) :=
begin
  have [ident hf] [":", expr surjective f] [":=", expr surjective.of_comp (λ t : β, (connected_fibers t).1)],
  split,
  { cases [expr hf t] ["with", ident s, ident hs],
    use [expr s],
    rw ["[", expr mem_preimage, ",", expr hs, "]"] [],
    exact [expr mem_connected_component] },
  have [ident hT] [":", expr is_closed «expr ⁻¹' »(f, connected_component t)] [":=", expr (hcl (connected_component t)).1 is_closed_connected_component],
  rw [expr is_preconnected_iff_subset_of_fully_disjoint_closed hT] [],
  intros [ident u, ident v, ident hu, ident hv, ident huv, ident uv_disj],
  let [ident T₁] [] [":=", expr {t' ∈ connected_component t | «expr ⊆ »(«expr ⁻¹' »(f, {t'}), u)}],
  let [ident T₂] [] [":=", expr {t' ∈ connected_component t | «expr ⊆ »(«expr ⁻¹' »(f, {t'}), v)}],
  have [ident fiber_decomp] [":", expr ∀
   t' «expr ∈ » connected_component t, «expr ∨ »(«expr ⊆ »(«expr ⁻¹' »(f, {t'}), u), «expr ⊆ »(«expr ⁻¹' »(f, {t'}), v))] [],
  { intros [ident t', ident ht'],
    apply [expr is_preconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv],
    { exact [expr subset.trans (hf.preimage_subset_preimage_iff.2 (singleton_subset_iff.2 ht')) huv] },
    rw [expr uv_disj] [],
    exact [expr inter_empty _] },
  have [ident T₁_u] [":", expr «expr = »(«expr ⁻¹' »(f, T₁), «expr ∩ »(«expr ⁻¹' »(f, connected_component t), u))] [],
  { apply [expr eq_of_subset_of_subset],
    { rw ["<-", expr bUnion_preimage_singleton] [],
      refine [expr bUnion_subset (λ t' ht', subset_inter _ ht'.2)],
      rw ["[", expr hf.preimage_subset_preimage_iff, ",", expr singleton_subset_iff, "]"] [],
      exact [expr ht'.1] },
    rintros [ident a, "⟨", ident hat, ",", ident hau, "⟩"],
    constructor,
    { exact [expr mem_preimage.1 hat] },
    dsimp ["only"] [] [] [],
    cases [expr fiber_decomp (f a) (mem_preimage.1 hat)] [],
    { exact [expr h] },
    { exfalso,
      rw ["<-", expr not_nonempty_iff_eq_empty] ["at", ident uv_disj],
      exact [expr uv_disj (nonempty_of_mem (mem_inter hau (h rfl)))] } },
  have [ident T₂_v] [":", expr «expr = »(«expr ⁻¹' »(f, T₂), «expr ∩ »(«expr ⁻¹' »(f, connected_component t), v))] [],
  { apply [expr eq_of_subset_of_subset],
    { rw ["<-", expr bUnion_preimage_singleton] [],
      refine [expr bUnion_subset (λ t' ht', subset_inter _ ht'.2)],
      rw ["[", expr hf.preimage_subset_preimage_iff, ",", expr singleton_subset_iff, "]"] [],
      exact [expr ht'.1] },
    rintros [ident a, "⟨", ident hat, ",", ident hav, "⟩"],
    constructor,
    { exact [expr mem_preimage.1 hat] },
    dsimp ["only"] [] [] [],
    cases [expr fiber_decomp (f a) (mem_preimage.1 hat)] [],
    { exfalso,
      rw ["<-", expr not_nonempty_iff_eq_empty] ["at", ident uv_disj],
      exact [expr uv_disj (nonempty_of_mem (mem_inter (h rfl) hav))] },
    { exact [expr h] } },
  have [ident hT₁] [":", expr is_closed T₁] [":=", expr (hcl T₁).2 «expr ▸ »(T₁_u.symm, is_closed.inter hT hu)],
  have [ident hT₂] [":", expr is_closed T₂] [":=", expr (hcl T₂).2 «expr ▸ »(T₂_v.symm, is_closed.inter hT hv)],
  have [ident T_decomp] [":", expr «expr ⊆ »(connected_component t, «expr ∪ »(T₁, T₂))] [],
  { intros [ident t', ident ht'],
    rw [expr mem_union t' T₁ T₂] [],
    cases [expr fiber_decomp t' ht'] ["with", ident htu, ident htv],
    { left,
      exact [expr ⟨ht', htu⟩] },
    right,
    exact [expr ⟨ht', htv⟩] },
  have [ident T_disjoint] [":", expr «expr = »(«expr ∩ »(T₁, T₂), «expr∅»())] [],
  { rw ["<-", expr image_preimage_eq «expr ∩ »(T₁, T₂) hf] [],
    suffices [] [":", expr «expr = »(«expr ⁻¹' »(f, «expr ∩ »(T₁, T₂)), «expr∅»())],
    { rw [expr this] [],
      exact [expr image_empty _] },
    rw ["[", expr preimage_inter, ",", expr T₁_u, ",", expr T₂_v, "]"] [],
    rw [expr inter_comm] ["at", ident uv_disj],
    conv [] [] { congr,
      rw ["[", expr inter_assoc, "]"],
      congr,
      skip,
      rw ["[", "<-", expr inter_assoc, ",", expr inter_comm, ",", "<-", expr inter_assoc, ",", expr uv_disj, ",", expr empty_inter, "]"] },
    exact [expr inter_empty _] },
  cases [expr (is_preconnected_iff_subset_of_fully_disjoint_closed is_closed_connected_component).1 is_preconnected_connected_component T₁ T₂ hT₁ hT₂ T_decomp T_disjoint] [],
  { left,
    rw [expr subset.antisymm_iff] ["at", ident T₁_u],
    suffices [] [":", expr «expr ⊆ »(«expr ⁻¹' »(f, connected_component t), «expr ⁻¹' »(f, T₁))],
    { exact [expr subset.trans (subset.trans this T₁_u.1) (inter_subset_right _ _)] },
    exact [expr preimage_mono h] },
  right,
  rw [expr subset.antisymm_iff] ["at", ident T₂_v],
  suffices [] [":", expr «expr ⊆ »(«expr ⁻¹' »(f, connected_component t), «expr ⁻¹' »(f, T₂))],
  { exact [expr subset.trans (subset.trans this T₂_v.1) (inter_subset_right _ _)] },
  exact [expr preimage_mono h]
end

end Preconnected

section TotallyDisconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, ie either empty or a singleton.-/
def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.subsingleton

theorem is_totally_disconnected_empty : IsTotallyDisconnected (∅ : Set α) :=
  fun _ ht _ _ x_in _ _ => (ht x_in).elim

theorem is_totally_disconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) :=
  fun _ ht _ => subsingleton.mono subsingleton_singleton ht

/-- A space is totally disconnected if all of its connected components are singletons. -/
class TotallyDisconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where 
  is_totally_disconnected_univ : IsTotallyDisconnected (univ : Set α)

theorem IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α} (h : IsPreconnected s) : s.subsingleton :=
  TotallyDisconnectedSpace.is_totally_disconnected_univ s (subset_univ s) h

instance Pi.totally_disconnected_space {α : Type _} {β : α → Type _} [t₂ : ∀ a, TopologicalSpace (β a)]
  [∀ a, TotallyDisconnectedSpace (β a)] : TotallyDisconnectedSpace (∀ a : α, β a) :=
  ⟨fun t h1 h2 =>
      have this : ∀ a, IsPreconnected ((fun x : ∀ a, β a => x a) '' t) :=
        fun a => h2.image (fun x => x a) (continuous_apply a).ContinuousOn 
      fun x x_in y y_in => funext$ fun a => (this a).Subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

instance Prod.totally_disconnected_space [TopologicalSpace β] [TotallyDisconnectedSpace α]
  [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β) :=
  ⟨fun t h1 h2 =>
      have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.ContinuousOn 
      have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.ContinuousOn 
      fun x hx y hy =>
        Prod.extₓ (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩) (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

/-- A space is totally disconnected iff its connected components are subsingletons. -/
theorem totally_disconnected_space_iff_connected_component_subsingleton :
  TotallyDisconnectedSpace α ↔ ∀ x : α, (ConnectedComponent x).Subsingleton :=
  by 
    split 
    ·
      intro h x 
      apply h.1
      ·
        exact subset_univ _ 
      exact is_preconnected_connected_component 
    intro h 
    constructor 
    intro s s_sub hs 
    rcases eq_empty_or_nonempty s with (rfl | ⟨x, x_in⟩)
    ·
      exact subsingleton_empty
    ·
      exact (h x).mono (hs.subset_connected_component x_in)

/-- A space is totally disconnected iff its connected components are singletons. -/
theorem totally_disconnected_space_iff_connected_component_singleton :
  TotallyDisconnectedSpace α ↔ ∀ x : α, ConnectedComponent x = {x} :=
  by 
    rw [totally_disconnected_space_iff_connected_component_subsingleton]
    apply forall_congrₓ fun x => _ 
    rw [Set.subsingleton_iff_singleton]
    exact mem_connected_component

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp]
theorem Continuous.image_connected_component_eq_singleton {β : Type _} [TopologicalSpace β] [TotallyDisconnectedSpace β]
  {f : α → β} (h : Continuous f) (a : α) : f '' ConnectedComponent a = {f a} :=
  (Set.subsingleton_iff_singleton$ mem_image_of_mem f mem_connected_component).mp
    (is_preconnected_connected_component.Image f h.continuous_on).Subsingleton

theorem is_totally_disconnected_of_totally_disconnected_space [TotallyDisconnectedSpace α] (s : Set α) :
  IsTotallyDisconnected s :=
  fun t hts ht => TotallyDisconnectedSpace.is_totally_disconnected_univ _ t.subset_univ ht

theorem is_totally_disconnected_of_image [TopologicalSpace β] {f : α → β} (hf : ContinuousOn f s) (hf' : injective f)
  (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  fun t hts ht x x_in y y_in =>
    hf'$ h _ (image_subset f hts) (ht.image f$ hf.mono hts) (mem_image_of_mem f x_in) (mem_image_of_mem f y_in)

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
  ∀ x _ : x ∈ s, ∀ y _ : y ∈ s, x ≠ y → ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ u ∩ v = ∅

theorem is_totally_separated_empty : IsTotallySeparated (∅ : Set α) :=
  fun x => False.elim

theorem is_totally_separated_singleton {x} : IsTotallySeparated ({x} : Set α) :=
  fun p hp q hq hpq => (hpq$ (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_totally_disconnected_of_is_totally_separated
{s : set α}
(H : is_totally_separated s) : is_totally_disconnected s :=
begin
  intros [ident t, ident hts, ident ht, ident x, ident x_in, ident y, ident y_in],
  by_contra [ident h],
  obtain ["⟨", ident u, ":", expr set α, ",", ident v, ":", expr set α, ",", ident hu, ":", expr is_open u, ",", ident hv, ":", expr is_open v, ",", ident hxu, ":", expr «expr ∈ »(x, u), ",", ident hyv, ":", expr «expr ∈ »(y, v), ",", ident hs, ":", expr «expr ⊆ »(s, «expr ∪ »(u, v)), ",", ident huv, ":", expr «expr = »(«expr ∩ »(u, v), «expr∅»()), "⟩", ":=", expr H x (hts x_in) y (hts y_in) h],
  have [] [":", expr «expr ∩ »(t, u).nonempty → «expr ∩ »(t, v).nonempty → «expr ∩ »(t, «expr ∩ »(u, v)).nonempty] [":=", expr ht _ _ hu hv (subset.trans hts hs)],
  obtain ["⟨", ident z, ",", ident hz, ":", expr «expr ∈ »(z, «expr ∩ »(t, «expr ∩ »(u, v))), "⟩", ":=", expr this ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩],
  simpa [] [] [] ["[", expr huv, "]"] [] ["using", expr hz]
end

alias is_totally_disconnected_of_is_totally_separated ← IsTotallySeparated.is_totally_disconnected

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
class TotallySeparatedSpace (α : Type u) [TopologicalSpace α] : Prop where 
  is_totally_separated_univ{} : IsTotallySeparated (univ : Set α)

instance (priority := 100) TotallySeparatedSpace.totally_disconnected_space (α : Type u) [TopologicalSpace α]
  [TotallySeparatedSpace α] : TotallyDisconnectedSpace α :=
  ⟨is_totally_disconnected_of_is_totally_separated$ TotallySeparatedSpace.is_totally_separated_univ α⟩

instance (priority := 100) TotallySeparatedSpace.of_discrete (α : Type _) [TopologicalSpace α] [DiscreteTopology α] :
  TotallySeparatedSpace α :=
  ⟨fun a _ b _ h =>
      ⟨«expr ᶜ» {b}, {b}, is_open_discrete _, is_open_discrete _,
        by 
          simpa⟩⟩

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_clopen_of_totally_separated
{α : Type*}
[topological_space α]
[totally_separated_space α]
{x y : α}
(hxy : «expr ≠ »(x, y)) : «expr∃ , »((U : set α)
 (hU : is_clopen U), «expr ∧ »(«expr ∈ »(x, U), «expr ∈ »(y, «expr ᶜ»(U)))) :=
begin
  obtain ["⟨", ident U, ",", ident V, ",", ident hU, ",", ident hV, ",", ident Ux, ",", ident Vy, ",", ident f, ",", ident disj, "⟩", ":=", expr totally_separated_space.is_totally_separated_univ α x (set.mem_univ x) y (set.mem_univ y) hxy],
  have [ident clopen_U] [] [":=", expr is_clopen_inter_of_disjoint_cover_clopen is_clopen_univ f hU hV disj],
  rw [expr set.univ_inter _] ["at", ident clopen_U],
  rw ["[", "<-", expr set.subset_compl_iff_disjoint, ",", expr set.subset_compl_comm, "]"] ["at", ident disj],
  exact [expr ⟨U, clopen_U, Ux, disj Vy⟩]
end

end TotallySeparated

section connectedComponentSetoid

/-- The setoid of connected components of a topological space -/
def connectedComponentSetoid (α : Type _) [TopologicalSpace α] : Setoidₓ α :=
  ⟨fun x y => ConnectedComponent x = ConnectedComponent y,
    ⟨fun x =>
        by 
          trivial,
      fun x y h1 => h1.symm, fun x y z h1 h2 => h1.trans h2⟩⟩

attribute [local instance] connectedComponentSetoid

theorem connected_component_rel_iff {x y : α} :
  «expr⟦ ⟧» x = «expr⟦ ⟧» y ↔ ConnectedComponent x = ConnectedComponent y :=
  ⟨fun h => Quotientₓ.exact h, fun h => Quotientₓ.sound h⟩

theorem connected_component_nrel_iff {x y : α} :
  «expr⟦ ⟧» x ≠ «expr⟦ ⟧» y ↔ ConnectedComponent x ≠ ConnectedComponent y :=
  by 
    rw [not_iff_not]
    exact connected_component_rel_iff

/-- The quotient of a space by its connected components -/
def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotientₓ (connectedComponentSetoid α)

instance [Inhabited α] : Inhabited (ConnectedComponents α) :=
  ⟨Quotientₓ.mk (default _)⟩

instance ConnectedComponents.topologicalSpace : TopologicalSpace (ConnectedComponents α) :=
  Quotientₓ.topologicalSpace

theorem Continuous.image_eq_of_equiv {β : Type _} [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α → β}
  (h : Continuous f) (a b : α) (hab : a ≈ b) : f a = f b :=
  singleton_eq_singleton_iff.1$
    h.image_connected_component_eq_singleton a ▸ h.image_connected_component_eq_singleton b ▸ hab ▸ rfl

/--
The lift to `connected_components α` of a continuous map from `α` to a totally disconnected space
-/
def Continuous.connectedComponentsLift {β : Type _} [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α → β}
  (h : Continuous f) : ConnectedComponents α → β :=
  Quotientₓ.lift f h.image_eq_of_equiv

@[continuity]
theorem Continuous.connected_components_lift_continuous {β : Type _} [TopologicalSpace β] [TotallyDisconnectedSpace β]
  {f : α → β} (h : Continuous f) : Continuous h.connected_components_lift :=
  continuous_quotient_lift h.image_eq_of_equiv h

@[simp]
theorem Continuous.connected_components_lift_factors {β : Type _} [TopologicalSpace β] [TotallyDisconnectedSpace β]
  {f : α → β} (h : Continuous f) : (h.connected_components_lift ∘ Quotientₓ.mk) = f :=
  rfl

theorem Continuous.connected_components_lift_unique {β : Type _} [TopologicalSpace β] [TotallyDisconnectedSpace β]
  {f : α → β} (h : Continuous f) (g : ConnectedComponents α → β) (hg : (g ∘ Quotientₓ.mk) = f) :
  g = h.connected_components_lift :=
  by 
    subst hg 
    ext1 x 
    exact Quotientₓ.induction_on x fun a => refl _

theorem connected_components_lift_unique' {β : Type _} (g₁ : ConnectedComponents α → β) (g₂ : ConnectedComponents α → β)
  (hg : (g₁ ∘ Quotientₓ.mk) = (g₂ ∘ Quotientₓ.mk)) : g₁ = g₂ :=
  by 
    ext1 x 
    refine' Quotientₓ.induction_on x fun a => _ 
    change (g₁ ∘ Quotientₓ.mk) a = (g₂ ∘ Quotientₓ.mk) a 
    rw [hg]

-- error in Topology.Connected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The preimage of a singleton in `connected_components` is the connected component
of an element in the equivalence class. -/
theorem connected_components_preimage_singleton
{t : α} : «expr = »(connected_component t, «expr ⁻¹' »(quotient.mk, {«expr⟦ ⟧»(t)})) :=
begin
  apply [expr set.eq_of_subset_of_subset]; intros [ident a, ident ha],
  { have [ident H] [":", expr «expr = »(«expr⟦ ⟧»(a), «expr⟦ ⟧»(t))] [":=", expr quotient.sound (connected_component_eq ha).symm],
    rw ["[", expr mem_preimage, ",", expr H, "]"] [],
    exact [expr mem_singleton «expr⟦ ⟧»(t)] },
  rw ["[", expr mem_preimage, ",", expr mem_singleton_iff, "]"] ["at", ident ha],
  have [ident ha'] [":", expr «expr = »(connected_component a, connected_component t)] [":=", expr quotient.exact ha],
  rw ["<-", expr ha'] [],
  exact [expr mem_connected_component]
end

/-- The preimage of the image of a set under the quotient map to `connected_components α`
is the union of the connected components of the elements in it. -/
theorem connected_components_preimage_image (U : Set α) :
  Quotientₓ.mk ⁻¹' (Quotientₓ.mk '' U) = ⋃(x : α)(h : x ∈ U), ConnectedComponent x :=
  by 
    apply Set.eq_of_subset_of_subset
    ·
      rintro a ⟨b, hb, hab⟩
      refine' mem_Union.2 ⟨b, mem_Union.2 ⟨hb, _⟩⟩
      rw [connected_component_rel_iff.1 hab]
      exact mem_connected_component 
    refine' Union_subset fun a => Union_subset fun ha => _ 
    rw [connected_components_preimage_singleton, (surjective_quotient_mk _).preimage_subset_preimage_iff,
      singleton_subset_iff]
    exact ⟨a, ha, refl _⟩

instance ConnectedComponents.totally_disconnected_space : TotallyDisconnectedSpace (ConnectedComponents α) :=
  by 
    rw [totally_disconnected_space_iff_connected_component_singleton]
    refine' fun x => Quotientₓ.induction_on x fun a => _ 
    apply eq_of_subset_of_subset _ (singleton_subset_iff.2 mem_connected_component)
    rw [subset_singleton_iff]
    refine' fun x => Quotientₓ.induction_on x fun b hb => _ 
    rw [connected_component_rel_iff, connected_component_eq]
    suffices  : IsPreconnected (Quotientₓ.mk ⁻¹' ConnectedComponent («expr⟦ ⟧» a))
    ·
      apply mem_of_subset_of_mem (this.subset_connected_component hb)
      exact mem_preimage.2 mem_connected_component 
    apply (@preimage_connected_component_connected _ _ _ _ _ _ _ _).2
    ·
      refine' fun t => Quotientₓ.induction_on t fun s => _ 
      rw [←connected_components_preimage_singleton]
      exact is_connected_connected_component 
    refine' fun T => ⟨fun hT => hT.preimage continuous_quotient_mk, fun hT => _⟩
    rwa [←is_open_compl_iff, ←preimage_compl, quotient_map_quotient_mk.is_open_preimage, is_open_compl_iff] at hT

/-- Functoriality of `connected_components` -/
def Continuous.connectedComponentsMap {β : Type _} [TopologicalSpace β] {f : α → β} (h : Continuous f) :
  ConnectedComponents α → ConnectedComponents β :=
  Continuous.connectedComponentsLift (continuous_quotient_mk.comp h)

theorem Continuous.connected_components_map_continuous {β : Type _} [TopologicalSpace β] {f : α → β}
  (h : Continuous f) : Continuous h.connected_components_map :=
  Continuous.connected_components_lift_continuous (continuous_quotient_mk.comp h)

end connectedComponentSetoid

