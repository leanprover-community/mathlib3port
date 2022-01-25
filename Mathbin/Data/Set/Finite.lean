import Mathbin.Data.Finset.Sort
import Mathbin.Data.Set.Functor

/-!
# Finite sets

This file defines predicates `finite : set α → Prop` and `infinite : set α → Prop` and proves some
basic facts about finite sets.
-/


open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-- A set is finite if the subtype is a fintype, i.e. there is a
  list that enumerates its members. -/
inductive finite (s : Set α) : Prop
  | intro : Fintype s → finite

theorem finite_def {s : Set α} : finite s ↔ Nonempty (Fintype s) :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

/-- A set is infinite if it is not finite. -/
def Infinite (s : Set α) : Prop :=
  ¬finite s

/-- The subtype corresponding to a finite set is a finite type. Note
that because `finite` isn't a typeclass, this will not fire if it
is made into an instance -/
noncomputable def finite.fintype {s : Set α} (h : finite s) : Fintype s :=
  Classical.choice $ finite_def.1 h

/-- Get a finset from a finite set -/
noncomputable def finite.to_finset {s : Set α} (h : finite s) : Finset α :=
  @Set.toFinset _ _ h.fintype

@[simp]
theorem not_infinite {s : Set α} : ¬s.infinite ↔ s.finite := by
  simp [Infinite]

/-- See also `fintype_or_infinite`. -/
theorem finite_or_infinite {s : Set α} : s.finite ∨ s.infinite :=
  em _

@[simp]
theorem finite.mem_to_finset {s : Set α} (h : finite s) {a : α} : a ∈ h.to_finset ↔ a ∈ s :=
  @mem_to_finset _ _ h.fintype _

@[simp]
theorem finite.to_finset.nonempty {s : Set α} (h : finite s) : h.to_finset.nonempty ↔ s.nonempty :=
  show (∃ x, x ∈ h.to_finset) ↔ ∃ x, x ∈ s from exists_congr fun _ => h.mem_to_finset

@[simp]
theorem finite.coe_to_finset {s : Set α} (h : finite s) : ↑h.to_finset = s :=
  @Set.coe_to_finset _ s h.fintype

@[simp]
theorem finite.coe_sort_to_finset {s : Set α} (h : finite s) : (h.to_finset : Type _) = s := by
  rw [← Finset.coe_sort_coe _, h.coe_to_finset]

@[simp]
theorem finite_empty_to_finset (h : finite (∅ : Set α)) : h.to_finset = ∅ := by
  rw [← Finset.coe_inj, h.coe_to_finset, Finset.coe_empty]

@[simp]
theorem finite.to_finset_inj {s t : Set α} {hs : finite s} {ht : finite t} : hs.to_finset = ht.to_finset ↔ s = t := by
  simp [← Finset.coe_inj]

theorem subset_to_finset_iff {s : Finset α} {t : Set α} (ht : finite t) : s ⊆ ht.to_finset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, ht.coe_to_finset]

@[simp]
theorem finite_to_finset_eq_empty_iff {s : Set α} {h : finite s} : h.to_finset = ∅ ↔ s = ∅ := by
  simp [← Finset.coe_inj]

theorem finite.exists_finset {s : Set α} : finite s → ∃ s' : Finset α, ∀ a : α, a ∈ s' ↔ a ∈ s
  | ⟨h⟩ => ⟨to_finset s, fun _ => mem_to_finset⟩

theorem finite.exists_finset_coe {s : Set α} (hs : finite s) : ∃ s' : Finset α, ↑s' = s :=
  ⟨hs.to_finset, hs.coe_to_finset⟩

/-- Finite sets can be lifted to finsets. -/
instance : CanLift (Set α) (Finset α) where
  coe := coe
  cond := finite
  prf := fun s hs => hs.exists_finset_coe

theorem finite_mem_finset (s : Finset α) : finite { a | a ∈ s } :=
  ⟨Fintype.ofFinset s fun _ => Iff.rfl⟩

theorem finite.of_fintype [Fintype α] (s : Set α) : finite s := by
  classical <;> exact ⟨setFintype s⟩

theorem exists_finite_iff_finset {p : Set α → Prop} : (∃ s, finite s ∧ p s) ↔ ∃ s : Finset α, p (↑s) :=
  ⟨fun ⟨s, hs, hps⟩ => ⟨hs.to_finset, hs.coe_to_finset.symm ▸ hps⟩, fun ⟨s, hs⟩ => ⟨↑s, finite_mem_finset s, hs⟩⟩

theorem finite.fin_embedding {s : Set α} (h : finite s) : ∃ (n : ℕ)(f : Finₓ n ↪ α), range f = s :=
  ⟨_, (Fintype.equivFin (h.to_finset : Set α)).symm.asEmbedding, by
    simp ⟩

theorem finite.fin_param {s : Set α} (h : finite s) : ∃ (n : ℕ)(f : Finₓ n → α), injective f ∧ range f = s :=
  let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.injective, hf⟩

/-- Membership of a subset of a finite type is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidable_mem_of_fintype [DecidableEq α] (s : Set α) [Fintype s] a : Decidable (a ∈ s) :=
  decidableOfIff _ mem_to_finset

instance fintype_empty : Fintype (∅ : Set α) :=
  Fintype.ofFinset ∅ $ by
    simp

theorem empty_card : Fintype.card (∅ : Set α) = 0 :=
  rfl

@[simp]
theorem empty_card' {h : Fintype.{u} (∅ : Set α)} : @Fintype.card (∅ : Set α) h = 0 :=
  Eq.trans
    (by
      congr)
    empty_card

@[simp]
theorem finite_empty : @finite α ∅ :=
  ⟨Set.fintypeEmpty⟩

instance finite.inhabited : Inhabited { s : Set α // finite s } :=
  ⟨⟨∅, finite_empty⟩⟩

/-- A `fintype` structure on `insert a s`. -/
def fintype_insert' {a : α} (s : Set α) [Fintype s] (h : a ∉ s) : Fintype (insert a s : Set α) :=
  Fintype.ofFinset
      ⟨a ::ₘ s.to_finset.1,
        Multiset.nodup_cons_of_nodup
          (by
            simp [h])
          s.to_finset.2⟩ $
    by
    simp

theorem card_fintype_insert' {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    @Fintype.card _ (fintype_insert' s h) = Fintype.card s + 1 := by
  rw [fintype_insert', Fintype.card_of_finset] <;> simp [Finset.card, to_finset] <;> rfl

@[simp]
theorem card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s) {d : Fintype.{u} (insert a s : Set α)} :
    @Fintype.card _ d = Fintype.card s + 1 := by
  rw [← card_fintype_insert' s h] <;> congr

theorem card_image_of_inj_on {s : Set α} [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : ∀, ∀ x ∈ s, ∀, ∀, ∀ y ∈ s, ∀, f x = f y → x = y) : Fintype.card (f '' s) = Fintype.card s :=
  have := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.to_finset.image f).card :=
      Fintype.card_of_finset' _
        (by
          simp )
    _ = s.to_finset.card :=
      Finset.card_image_of_inj_on fun x hx y hy hxy => H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy
    _ = Fintype.card s := (Fintype.card_of_finset' _ fun a => mem_to_finset).symm
    

theorem card_image_of_injective (s : Set α) [Fintype s] {f : α → β} [Fintype (f '' s)] (H : Function.Injective f) :
    Fintype.card (f '' s) = Fintype.card s :=
  card_image_of_inj_on $ fun _ _ _ _ h => H h

section

attribute [local instance] decidable_mem_of_fintype

instance fintype_insert [DecidableEq α] (a : α) (s : Set α) [Fintype s] : Fintype (insert a s : Set α) :=
  if h : a ∈ s then by
    rwa [insert_eq, union_eq_self_of_subset_left (singleton_subset_iff.2 h)]
  else fintype_insert' _ h

end

@[simp]
theorem finite.insert (a : α) {s : Set α} : finite s → finite (insert a s)
  | ⟨h⟩ => ⟨@Set.fintypeInsert _ (Classical.decEq α) _ _ h⟩

theorem to_finset_insert [DecidableEq α] {a : α} {s : Set α} (hs : finite s) :
    (hs.insert a).toFinset = insert a hs.to_finset :=
  Finset.ext $ by
    simp

@[simp]
theorem insert_to_finset [DecidableEq α] {a : α} {s : Set α} [Fintype s] :
    (insert a s).toFinset = insert a s.to_finset := by
  simp [Finset.ext_iff, mem_insert_iff]

@[elab_as_eliminator]
theorem finite.induction_on {C : Set α → Prop} {s : Set α} (h : finite s) (H0 : C ∅)
    (H1 : ∀ {a s}, a ∉ s → finite s → C s → C (insert a s)) : C s :=
  let ⟨t⟩ := h
  match s.to_finset, @mem_to_finset _ s _ with
  | ⟨l, nd⟩, al => by
    change ∀ a, a ∈ l ↔ a ∈ s at al
    clear _let_match _match t h
    revert s nd al
    refine' Multiset.induction_on l _ fun a l IH => _ <;> intro s nd al
    · rw
        [show s = ∅ from
          eq_empty_iff_forall_not_mem.2
            (by
              simpa using al)]
      exact H0
      
    · rw [←
        show insert a { x | x ∈ l } = s from
          Set.ext
            (by
              simpa using al)]
      cases' Multiset.nodup_cons.1 nd with m nd'
      refine' H1 _ ⟨Finset.subtype.fintype ⟨l, nd'⟩⟩ (IH nd' fun _ => Iff.rfl)
      exact m
      

@[elab_as_eliminator]
theorem finite.dinduction_on {C : ∀ s : Set α, finite s → Prop} {s : Set α} (h : finite s) (H0 : C ∅ finite_empty)
    (H1 : ∀ {a s}, a ∉ s → ∀ h : finite s, C s h → C (insert a s) (h.insert a)) : C s h :=
  have : ∀ h : finite s, C s h := finite.induction_on h (fun h => H0) fun a s has hs ih h => H1 has hs (ih _)
  this h

instance fintype_singleton (a : α) : Fintype ({a} : Set α) :=
  Unique.fintype

@[simp]
theorem card_singleton (a : α) : Fintype.card ({a} : Set α) = 1 :=
  Fintype.card_of_subsingleton _

@[simp]
theorem finite_singleton (a : α) : finite ({a} : Set α) :=
  ⟨Set.fintypeSingleton _⟩

theorem subsingleton.finite {s : Set α} (h : s.subsingleton) : finite s :=
  h.induction_on finite_empty finite_singleton

theorem to_finset_singleton (a : α) : ({a} : Set α).toFinset = {a} :=
  rfl

theorem finite_is_top (α : Type _) [PartialOrderₓ α] : finite { x : α | IsTop x } :=
  (subsingleton_is_top α).Finite

theorem finite_is_bot (α : Type _) [PartialOrderₓ α] : finite { x : α | IsBot x } :=
  (subsingleton_is_bot α).Finite

instance fintype_pure : ∀ a : α, Fintype (pure a : Set α) :=
  Set.fintypeSingleton

theorem finite_pure (a : α) : finite (pure a : Set α) :=
  ⟨Set.fintypePure a⟩

instance fintype_univ [Fintype α] : Fintype (@univ α) :=
  Fintype.ofEquiv α $ (Equivₓ.Set.univ α).symm

theorem finite_univ [Fintype α] : finite (@univ α) :=
  ⟨Set.fintypeUniv⟩

/-- If `(set.univ : set α)` is finite then `α` is a finite type. -/
noncomputable def fintype_of_univ_finite (H : (univ : Set α).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equivₓ.Set.univ _)

theorem univ_finite_iff_nonempty_fintype : (univ : Set α).Finite ↔ Nonempty (Fintype α) := by
  constructor
  · intro h
    exact ⟨fintype_of_univ_finite h⟩
    
  · rintro ⟨_i⟩
    exact finite_univ
    

theorem infinite_univ_iff : (@univ α).Infinite ↔ _root_.infinite α :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ $ @finite_univ α h₂⟩, fun ⟨h₁⟩ h₂ => h₁ (fintype_of_univ_finite h₂)⟩

theorem infinite_univ [h : _root_.infinite α] : Infinite (@univ α) :=
  infinite_univ_iff.2 h

theorem infinite_coe_iff {s : Set α} : _root_.infinite s ↔ Infinite s :=
  ⟨fun ⟨h₁⟩ h₂ => h₁ h₂.fintype, fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩⟩

theorem infinite.to_subtype {s : Set α} (h : Infinite s) : _root_.infinite s :=
  infinite_coe_iff.2 h

/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def Infinite.natEmbedding (s : Set α) (h : Infinite s) : ℕ ↪ s :=
  have := h.to_subtype
  Infinite.natEmbedding s

theorem Infinite.exists_subset_card_eq {s : Set α} (hs : Infinite s) (n : ℕ) : ∃ t : Finset α, ↑t ⊆ s ∧ t.card = n :=
  ⟨((Finset.range n).map (hs.nat_embedding _)).map (embedding.subtype _), by
    simp ⟩

theorem Infinite.nonempty {s : Set α} (h : s.infinite) : s.nonempty :=
  let a := Infinite.natEmbedding s h 37
  ⟨a.1, a.2⟩

instance fintype_union [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s ∪ t : Set α) :=
  Fintype.ofFinset (s.to_finset ∪ t.to_finset) $ by
    simp

theorem finite.union {s t : Set α} : finite s → finite t → finite (s ∪ t)
  | ⟨hs⟩, ⟨ht⟩ => ⟨@Set.fintypeUnion _ (Classical.decEq α) _ _ hs ht⟩

theorem finite.sup {s t : Set α} : finite s → finite t → finite (s⊔t) :=
  finite.union

theorem infinite_of_finite_compl [_root_.infinite α] {s : Set α} (hs : sᶜ.Finite) : s.infinite := fun h =>
  Set.infinite_univ
    (by
      simpa using hs.union h)

theorem finite.infinite_compl [_root_.infinite α] {s : Set α} (hs : s.finite) : sᶜ.Infinite := fun h =>
  Set.infinite_univ
    (by
      simpa using hs.union h)

instance fintype_sep (s : Set α) (p : α → Prop) [Fintype s] [DecidablePred p] : Fintype ({ a ∈ s | p a } : Set α) :=
  Fintype.ofFinset (s.to_finset.filter p) $ by
    simp

instance fintype_inter (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] : Fintype (s ∩ t : Set α) :=
  Set.fintypeSep s t

/-- A `fintype` structure on a set defines a `fintype` structure on its subset. -/
def fintype_subset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· ∈ t)] (h : t ⊆ s) : Fintype t := by
  rw [← inter_eq_self_of_subset_right h] <;> infer_instance

theorem finite.subset {s : Set α} : finite s → ∀ {t : Set α}, t ⊆ s → finite t
  | ⟨hs⟩, t, h => ⟨@Set.fintypeSubset _ _ _ hs (Classical.decPred t) h⟩

@[simp]
theorem finite_union {s t : Set α} : finite (s ∪ t) ↔ finite s ∧ finite t :=
  ⟨fun h => ⟨h.subset (subset_union_left _ _), h.subset (subset_union_right _ _)⟩, fun ⟨hs, ht⟩ => hs.union ht⟩

theorem finite.of_diff {s t : Set α} (hd : finite (s \ t)) (ht : finite t) : finite s :=
  (hd.union ht).Subset $ subset_diff_union _ _

theorem finite.inter_of_left {s : Set α} (h : finite s) (t : Set α) : finite (s ∩ t) :=
  h.subset (inter_subset_left _ _)

theorem finite.inter_of_right {s : Set α} (h : finite s) (t : Set α) : finite (t ∩ s) :=
  h.subset (inter_subset_right _ _)

theorem finite.inf_of_left {s : Set α} (h : finite s) (t : Set α) : finite (s⊓t) :=
  h.inter_of_left t

theorem finite.inf_of_right {s : Set α} (h : finite s) (t : Set α) : finite (t⊓s) :=
  h.inter_of_right t

theorem finite.sInter {α : Type _} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.finite) : (⋂₀s).Finite :=
  hf.subset (sInter_subset_of_mem ht)

protected theorem infinite.mono {s t : Set α} (h : s ⊆ t) : Infinite s → Infinite t :=
  mt fun ht => ht.subset h

theorem infinite.diff {s t : Set α} (hs : s.infinite) (ht : t.finite) : (s \ t).Infinite := fun h => hs $ h.of_diff ht

@[simp]
theorem infinite_union {s t : Set α} : Infinite (s ∪ t) ↔ Infinite s ∨ Infinite t := by
  simp only [Infinite, finite_union, not_and_distrib]

instance fintype_image [DecidableEq β] (s : Set α) (f : α → β) [Fintype s] : Fintype (f '' s) :=
  Fintype.ofFinset (s.to_finset.image f) $ by
    simp

instance fintype_range [DecidableEq α] (f : ι → α) [Fintype (Plift ι)] : Fintype (range f) :=
  Fintype.ofFinset (Finset.univ.Image $ f ∘ Plift.down) $ by
    simp [(@Equivₓ.plift ι).exists_congr_left]

theorem finite_range (f : ι → α) [Fintype (Plift ι)] : finite (range f) :=
  have := Classical.decEq α
  ⟨by
    infer_instance⟩

theorem finite.image {s : Set α} (f : α → β) : finite s → finite (f '' s)
  | ⟨h⟩ => ⟨@Set.fintypeImage _ _ (Classical.decEq β) _ _ h⟩

theorem infinite_of_infinite_image (f : α → β) {s : Set α} (hs : (f '' s).Infinite) : s.infinite :=
  mt (finite.image f) hs

theorem finite.dependent_image {s : Set α} (hs : finite s) (F : ∀, ∀ i ∈ s, ∀, β) :
    finite { y : β | ∃ (x : _)(hx : x ∈ s), y = F x hx } := by
  let this' : Fintype s := hs.fintype
  convert finite_range fun x : s => F x x.2
  simp only [SetCoe.exists, Subtype.coe_mk, eq_comm]

theorem finite.of_preimage {f : α → β} {s : Set β} (h : finite (f ⁻¹' s)) (hf : surjective f) : finite s :=
  hf.image_preimage s ▸ h.image _

instance fintype_map {α β} [DecidableEq β] : ∀ s : Set α f : α → β [Fintype s], Fintype (f <$> s) :=
  Set.fintypeImage

theorem finite.map {α β} {s : Set α} : ∀ f : α → β, finite s → finite (f <$> s) :=
  finite.image

/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[fintype]` instance,
then `s` has a `fintype` structure as well. -/
def fintype_of_fintype_image (s : Set α) {f : α → β} {g} (I : is_partial_inv f g) [Fintype (f '' s)] : Fintype s :=
  Fintype.ofFinset
      ⟨_, @Multiset.nodup_filter_map β α g _ (@injective_of_partial_inv_right _ _ f g I) (f '' s).toFinset.2⟩ $
    fun a => by
    suffices (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s by
      simpa [exists_and_distrib_left.symm, And.comm, And.left_comm, And.assoc]
    rw [exists_swap]
    suffices (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s by
      simpa [And.comm, And.left_comm, And.assoc]
    simp [I _, (injective_of_partial_inv I).eq_iff]

theorem finite_of_finite_image {s : Set α} {f : α → β} (hi : Set.InjOn f s) : finite (f '' s) → finite s
  | ⟨h⟩ =>
    ⟨(@Fintype.ofInjective _ _ h fun a : s => ⟨f a.1, mem_image_of_mem f a.2⟩) $ fun a b eq =>
        Subtype.eq $ hi a.2 b.2 $ Subtype.ext_iff_val.1 Eq⟩

theorem finite_image_iff {s : Set α} {f : α → β} (hi : inj_on f s) : finite (f '' s) ↔ finite s :=
  ⟨finite_of_finite_image hi, finite.image _⟩

theorem infinite_image_iff {s : Set α} {f : α → β} (hi : inj_on f s) : Infinite (f '' s) ↔ Infinite s :=
  not_congr $ finite_image_iff hi

theorem infinite_of_inj_on_maps_to {s : Set α} {t : Set β} {f : α → β} (hi : inj_on f s) (hm : maps_to f s t)
    (hs : Infinite s) : Infinite t :=
  ((infinite_image_iff hi).2 hs).mono (maps_to'.mp hm)

theorem infinite.exists_ne_map_eq_of_maps_to {s : Set α} {t : Set β} {f : α → β} (hs : Infinite s) (hf : maps_to f s t)
    (ht : finite t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  contrapose! ht
  exact infinite_of_inj_on_maps_to (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs

theorem infinite.exists_lt_map_eq_of_maps_to [LinearOrderₓ α] {s : Set α} {t : Set β} {f : α → β} (hs : Infinite s)
    (hf : maps_to f s t) (ht : finite t) : ∃ x ∈ s, ∃ y ∈ s, x < y ∧ f x = f y :=
  let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_maps_to hf ht
  hxy.lt_or_lt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩

theorem finite.exists_lt_map_eq_of_range_subset [LinearOrderₓ α] [_root_.infinite α] {t : Set β} {f : α → β}
    (hf : range f ⊆ t) (ht : finite t) : ∃ a b, a < b ∧ f a = f b := by
  rw [range_subset_iff, ← maps_univ_to] at hf
  obtain ⟨a, -, b, -, h⟩ := (@infinite_univ α _).exists_lt_map_eq_of_maps_to hf ht
  exact ⟨a, b, h⟩

theorem infinite_range_of_injective [_root_.infinite α] {f : α → β} (hi : injective f) : Infinite (range f) := by
  rw [← image_univ, infinite_image_iff (inj_on_of_injective hi _)]
  exact infinite_univ

theorem infinite_of_injective_forall_mem [_root_.infinite α] {s : Set β} {f : α → β} (hi : injective f)
    (hf : ∀ x : α, f x ∈ s) : Infinite s := by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf

theorem finite.preimage {s : Set β} {f : α → β} (I : Set.InjOn f (f ⁻¹' s)) (h : finite s) : finite (f ⁻¹' s) :=
  finite_of_finite_image I (h.subset (image_preimage_subset f s))

theorem finite.preimage_embedding {s : Set β} (f : α ↪ β) (h : s.finite) : (f ⁻¹' s).Finite :=
  finite.preimage (fun _ _ _ _ h' => f.injective h') h

theorem finite_option {s : Set (Option α)} : finite s ↔ finite { x : α | some x ∈ s } :=
  ⟨fun h => h.preimage_embedding embedding.some, fun h =>
    ((h.image some).insert none).Subset $ fun x =>
      Option.casesOn x (fun _ => Or.inl rfl) fun x hx => Or.inr $ mem_image_of_mem _ hx⟩

instance fintype_Union [DecidableEq α] [Fintype (Plift ι)] (f : ι → Set α) [∀ i, Fintype (f i)] : Fintype (⋃ i, f i) :=
  Fintype.ofFinset (Finset.univ.bUnion fun i : Plift ι => (f i.down).toFinset) $ by
    simp

theorem finite_Union [Fintype (Plift ι)] {f : ι → Set α} (H : ∀ i, finite (f i)) : finite (⋃ i, f i) :=
  ⟨@Set.fintypeUnionₓ _ _ (Classical.decEq α) _ _ fun i => finite.fintype (H i)⟩

/-- A union of sets with `fintype` structure over a set with `fintype` structure has a `fintype`
structure. -/
def fintype_bUnion [DecidableEq α] {ι : Type _} {s : Set ι} [Fintype s] (f : ι → Set α)
    (H : ∀, ∀ i ∈ s, ∀, Fintype (f i)) : Fintype (⋃ i ∈ s, f i) := by
  rw [bUnion_eq_Union] <;>
    exact
      @Set.fintypeUnionₓ _ _ _ _ _
        (by
          rintro ⟨i, hi⟩ <;> exact H i hi)

instance fintype_bUnion' [DecidableEq α] {ι : Type _} {s : Set ι} [Fintype s] (f : ι → Set α) [H : ∀ i, Fintype (f i)] :
    Fintype (⋃ i ∈ s, f i) :=
  fintype_bUnion _ fun i _ => H i

theorem finite.sUnion {s : Set (Set α)} (h : finite s) (H : ∀, ∀ t ∈ s, ∀, finite t) : finite (⋃₀s) := by
  rw [sUnion_eq_Union] <;> have := finite.fintype h <;> apply finite_Union <;> simpa using H

theorem finite.bUnion {α} {ι : Type _} {s : Set ι} {f : ∀, ∀ i ∈ s, ∀, Set α} :
    finite s → (∀, ∀ i ∈ s, ∀, finite (f i ‹_›)) → finite (⋃ i ∈ s, f i ‹_›)
  | ⟨hs⟩, h => by
    rw [bUnion_eq_Union] <;> exact finite_Union fun i => h _ _

instance fintype_lt_nat (n : ℕ) : Fintype { i | i < n } :=
  Fintype.ofFinset (Finset.range n) $ by
    simp

instance fintype_le_nat (n : ℕ) : Fintype { i | i ≤ n } := by
  simpa [Nat.lt_succ_iffₓ] using Set.fintypeLtNat (n + 1)

theorem finite_le_nat (n : ℕ) : finite { i | i ≤ n } :=
  ⟨Set.fintypeLeNat _⟩

theorem finite_lt_nat (n : ℕ) : finite { i | i < n } :=
  ⟨Set.fintypeLtNat _⟩

theorem infinite.exists_nat_lt {s : Set ℕ} (hs : Infinite s) (n : ℕ) : ∃ m ∈ s, n < m :=
  let ⟨m, hm⟩ := (hs.diff $ Set.finite_le_nat n).Nonempty
  ⟨m, by
    simpa using hm⟩

instance fintype_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] : Fintype (s ×ˢ t : Set _) :=
  Fintype.ofFinset (s.to_finset.product t.to_finset) $ by
    simp

theorem finite.prod {s : Set α} {t : Set β} : finite s → finite t → finite (s ×ˢ t)
  | ⟨hs⟩, ⟨ht⟩ => ⟨Set.fintypeProd s t⟩

/-- `image2 f s t` is finitype if `s` and `t` are. -/
instance fintype_image2 [DecidableEq γ] (f : α → β → γ) (s : Set α) (t : Set β) [hs : Fintype s] [ht : Fintype t] :
    Fintype (image2 f s t : Set γ) := by
  rw [← image_prod]
  apply Set.fintypeImage

theorem finite.image2 (f : α → β → γ) {s : Set α} {t : Set β} (hs : finite s) (ht : finite t) : finite (image2 f s t) :=
  by
  rw [← image_prod]
  exact (hs.prod ht).Image _

/-- If `s : set α` is a set with `fintype` instance and `f : α → set β` is a function such that
each `f a`, `a ∈ s`, has a `fintype` structure, then `s >>= f` has a `fintype` structure. -/
def fintype_bind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β) (H : ∀, ∀ a ∈ s, ∀, Fintype (f a)) :
    Fintype (s >>= f) :=
  Set.fintypeBUnion _ H

instance fintype_bind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β) [H : ∀ a, Fintype (f a)] :
    Fintype (s >>= f) :=
  fintype_bind _ _ fun i _ => H i

theorem finite.bind {α β} {s : Set α} {f : α → Set β} (h : finite s) (hf : ∀, ∀ a ∈ s, ∀, finite (f a)) :
    finite (s >>= f) :=
  h.bUnion hf

instance fintype_seq [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] : Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBUnion'

instance fintype_seq' {α β : Type u} [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f <*> s) :=
  Set.fintypeSeq f s

theorem finite.seq {f : Set (α → β)} {s : Set α} (hf : finite f) (hs : finite s) : finite (f.seq s) := by
  rw [seq_def]
  exact hf.bUnion fun f _ => hs.image _

theorem finite.seq' {α β : Type u} {f : Set (α → β)} {s : Set α} (hf : finite f) (hs : finite s) : finite (f <*> s) :=
  hf.seq hs

/-- There are finitely many subsets of a given finite set -/
theorem finite.finite_subsets {α : Type u} {a : Set α} (h : finite a) : finite { b | b ⊆ a } :=
  ⟨Fintype.ofFinset ((Finset.powerset h.to_finset).map Finset.coeEmb.1) $ fun s => by
      simpa [← @exists_finite_iff_finset α fun t => t ⊆ a ∧ t = s, subset_to_finset_iff, ← And.assoc] using h.subset⟩

theorem exists_min_image [LinearOrderₓ β] (s : Set α) (f : α → β) (h1 : finite s) :
    s.nonempty → ∃ a ∈ s, ∀, ∀ b ∈ s, ∀, f a ≤ f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, finite.mem_to_finset] using h1.to_finset.exists_min_image f ⟨x, h1.mem_to_finset.2 hx⟩

theorem exists_max_image [LinearOrderₓ β] (s : Set α) (f : α → β) (h1 : finite s) :
    s.nonempty → ∃ a ∈ s, ∀, ∀ b ∈ s, ∀, f b ≤ f a
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, finite.mem_to_finset] using h1.to_finset.exists_max_image f ⟨x, h1.mem_to_finset.2 hx⟩

theorem exists_lower_bound_image [hα : Nonempty α] [LinearOrderₓ β] (s : Set α) (f : α → β) (h : s.finite) :
    ∃ a : α, ∀, ∀ b ∈ s, ∀, f a ≤ f b := by
  by_cases' hs : Set.Nonempty s
  · exact
      let ⟨x₀, H, hx₀⟩ := Set.exists_min_image s f h hs
      ⟨x₀, fun x hx => hx₀ x hx⟩
    
  · exact Nonempty.elimₓ hα fun a => ⟨a, fun x hx => absurd (Set.nonempty_of_mem hx) hs⟩
    

theorem exists_upper_bound_image [hα : Nonempty α] [LinearOrderₓ β] (s : Set α) (f : α → β) (h : s.finite) :
    ∃ a : α, ∀, ∀ b ∈ s, ∀, f b ≤ f a := by
  by_cases' hs : Set.Nonempty s
  · exact
      let ⟨x₀, H, hx₀⟩ := Set.exists_max_image s f h hs
      ⟨x₀, fun x hx => hx₀ x hx⟩
    
  · exact Nonempty.elimₓ hα fun a => ⟨a, fun x hx => absurd (Set.nonempty_of_mem hx) hs⟩
    

end Set

namespace Finset

variable [DecidableEq β]

variable {s : Finset α}

theorem finite_to_set (s : Finset α) : Set.Finite (↑s : Set α) :=
  Set.finite_mem_finset s

@[simp]
theorem finite_to_set_to_finset {α : Type _} (s : Finset α) : (finite_to_set s).toFinset = s := by
  ext
  rw [Set.Finite.mem_to_finset, mem_coe]

end Finset

namespace Set

/-- Finite product of finite sets is finite -/
theorem finite.pi {δ : Type _} [Fintype δ] {κ : δ → Type _} {t : ∀ d, Set (κ d)} (ht : ∀ d, (t d).Finite) :
    (pi univ t).Finite := by
  lift t to ∀ d, Finset (κ d) using ht
  classical
  rw [← Fintype.coe_pi_finset]
  exact (Fintype.piFinset t).finite_to_set

/-- A finite union of finsets is finite. -/
theorem union_finset_finite_of_range_finite (f : α → Finset β) (h : (range f).Finite) : (⋃ a, (f a : Set β)).Finite :=
  by
  rw [← bUnion_range]
  exact h.bUnion fun y hy => y.finite_to_set

theorem finite_subset_Union {s : Set α} (hs : finite s) {ι} {t : ι → Set α} (h : s ⊆ ⋃ i, t i) :
    ∃ I : Set ι, finite I ∧ s ⊆ ⋃ i ∈ I, t i := by
  cases' hs
  choose f hf using
    show ∀ x : s, ∃ i, x.1 ∈ t i by
      simpa [subset_def] using h
  refine' ⟨range f, finite_range f, fun x hx => _⟩
  rw [bUnion_range, mem_Union]
  exact ⟨⟨x, hx⟩, hf _⟩

theorem eq_finite_Union_of_finite_subset_Union {ι} {s : ι → Set α} {t : Set α} (tfin : finite t) (h : t ⊆ ⋃ i, s i) :
    ∃ I : Set ι, finite I ∧ ∃ σ : { i | i ∈ I } → Set α, (∀ i, finite (σ i)) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
  let ⟨I, Ifin, hI⟩ := finite_subset_Union tfin h
  ⟨I, Ifin, fun x => s x ∩ t, fun i => tfin.subset (inter_subset_right _ _), fun i => inter_subset_left _ _, by
    ext x
    rw [mem_Union]
    constructor
    · intro x_in
      rcases mem_Union.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      use i, hi, H, x_in
      
    · rintro ⟨i, hi, H⟩
      exact H
      ⟩

/-- An increasing union distributes over finite intersection. -/
theorem Union_Inter_of_monotone {ι ι' α : Type _} [Fintype ι] [LinearOrderₓ ι'] [Nonempty ι'] {s : ι → ι' → Set α}
    (hs : ∀ i, Monotone (s i)) : (⋃ j : ι', ⋂ i : ι, s i j) = ⋂ i : ι, ⋃ j : ι', s i j := by
  ext x
  refine' ⟨fun hx => Union_Inter_subset hx, fun hx => _⟩
  simp only [mem_Inter, mem_Union, mem_Inter] at hx⊢
  choose j hj using hx
  obtain ⟨j₀⟩ :=
    show Nonempty ι' by
      infer_instance
  refine' ⟨finset.univ.fold max j₀ j, fun i => hs i _ (hj i)⟩
  rw [Finset.fold_op_rel_iff_or (@le_max_iff _ _)]
  exact Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩

theorem Union_pi_of_monotone {ι ι' : Type _} [LinearOrderₓ ι'] [Nonempty ι'] {α : ι → Type _} {I : Set ι}
    {s : ∀ i, ι' → Set (α i)} (hI : finite I) (hs : ∀, ∀ i ∈ I, ∀, Monotone (s i)) :
    (⋃ j : ι', I.pi fun i => s i j) = I.pi fun i => ⋃ j, s i j := by
  simp only [pi_def, bInter_eq_Inter, preimage_Union]
  have := hI.fintype
  exact Union_Inter_of_monotone fun i j₁ j₂ h => preimage_mono $ hs i i.2 h

theorem Union_univ_pi_of_monotone {ι ι' : Type _} [LinearOrderₓ ι'] [Nonempty ι'] [Fintype ι] {α : ι → Type _}
    {s : ∀ i, ι' → Set (α i)} (hs : ∀ i, Monotone (s i)) :
    (⋃ j : ι', pi univ fun i => s i j) = pi univ fun i => ⋃ j, s i j :=
  Union_pi_of_monotone (finite.of_fintype _) fun i _ => hs i

instance nat.fintype_Iio (n : ℕ) : Fintype (Iio n) :=
  Fintype.ofFinset (Finset.range n) $ by
    simp

/-- If `P` is some relation between terms of `γ` and sets in `γ`,
such that every finite set `t : set γ` has some `c : γ` related to it,
then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets
are totally bounded.)
-/
theorem seq_of_forall_finite_exists {γ : Type _} {P : γ → Set γ → Prop} (h : ∀ t, finite t → ∃ c, P c t) :
    ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) :=
  ⟨fun n =>
    @Nat.strongRecOn' (fun _ => γ) n $ fun n ih =>
      Classical.some $ h (range $ fun m : Iio n => ih m.1 m.2) (finite_range _),
    fun n => by
    classical
    refine' Nat.strongRecOn' n fun n ih => _
    rw [Nat.strong_rec_on_beta']
    convert Classical.some_spec (h _ _)
    ext x
    constructor
    · rintro ⟨m, hmn, rfl⟩
      exact ⟨⟨m, hmn⟩, rfl⟩
      
    · rintro ⟨⟨m, hmn⟩, rfl⟩
      exact ⟨m, hmn, rfl⟩
      ⟩

theorem finite_range_ite {p : α → Prop} [DecidablePred p] {f g : α → β} (hf : finite (range f))
    (hg : finite (range g)) : finite (range fun x => if p x then f x else g x) :=
  (hf.union hg).Subset range_ite_subset

theorem finite_range_const {c : β} : finite (range fun x : α => c) :=
  (finite_singleton c).Subset range_const_subset

theorem range_find_greatest_subset {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    (range fun x => Nat.findGreatest (P x) b) ⊆ ↑Finset.range (b + 1) := by
  rw [range_subset_iff]
  intro x
  simp [Nat.lt_succ_iffₓ, Nat.find_greatest_le]

theorem finite_range_find_greatest {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    finite (range fun x => Nat.findGreatest (P x) b) :=
  (Finset.range (b + 1)).finite_to_set.Subset range_find_greatest_subset

theorem card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) : Fintype.card s < Fintype.card t :=
  Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1) $ fun hst =>
    (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

theorem card_le_of_subset {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t) : Fintype.card s ≤ Fintype.card t :=
  Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)

theorem eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t)
    (hcard : Fintype.card t ≤ Fintype.card s) : s = t :=
  (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard $ not_le_of_lt $ card_lt_card h

theorem subset_iff_to_finset_subset (s t : Set α) [Fintype s] [Fintype t] : s ⊆ t ↔ s.to_finset ⊆ t.to_finset := by
  simp

@[simp, mono]
theorem finite.to_finset_mono {s t : Set α} {hs : finite s} {ht : finite t} : hs.to_finset ⊆ ht.to_finset ↔ s ⊆ t := by
  constructor
  · intro h x
    rw [← finite.mem_to_finset hs, ← finite.mem_to_finset ht]
    exact fun hx => h hx
    
  · intro h x
    rw [finite.mem_to_finset hs, finite.mem_to_finset ht]
    exact fun hx => h hx
    

@[simp, mono]
theorem finite.to_finset_strict_mono {s t : Set α} {hs : finite s} {ht : finite t} :
    hs.to_finset ⊂ ht.to_finset ↔ s ⊂ t := by
  rw [← lt_eq_ssubset, ← Finset.lt_iff_ssubset, lt_iff_le_and_ne, lt_iff_le_and_ne]
  simp

theorem card_range_of_injective [Fintype α] {f : α → β} (hf : injective f) [Fintype (range f)] :
    Fintype.card (range f) = Fintype.card α :=
  Eq.symm $ Fintype.card_congr $ Equivₓ.ofInjective f hf

theorem finite.exists_maximal_wrt [PartialOrderₓ β] (f : α → β) (s : Set α) (h : Set.Finite s) :
    s.nonempty → ∃ a ∈ s, ∀, ∀ a' ∈ s, ∀, f a ≤ f a' → f a = f a' := by
  classical
  refine' h.induction_on _ _
  · exact fun h => absurd h empty_not_nonempty
    
  intro a s his _ ih _
  cases' s.eq_empty_or_nonempty with h h
  · use a
    simp [h]
    
  rcases ih h with ⟨b, hb, ih⟩
  by_cases' f b ≤ f a
  · refine' ⟨a, Set.mem_insert _ _, fun c hc hac => le_antisymmₓ hac _⟩
    rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
    · rfl
      
    · rwa [← ih c hcs (le_transₓ h hac)]
      
    
  · refine' ⟨b, Set.mem_insert_of_mem _ hb, fun c hc hbc => _⟩
    rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
    · exact (h hbc).elim
      
    · exact ih c hcs hbc
      
    

theorem finite.card_to_finset {s : Set α} [Fintype s] (h : s.finite) : h.to_finset.card = Fintype.card s := by
  rw [← Finset.card_attach, Finset.attach_eq_univ, ← Fintype.card]
  refine' Fintype.card_congr (Equivₓ.setCongr _)
  ext x
  show x ∈ h.to_finset ↔ x ∈ s
  simp

theorem Infinite.exists_not_mem_finset {s : Set α} (hs : s.infinite) (f : Finset α) : ∃ a ∈ s, a ∉ f :=
  let ⟨a, has, haf⟩ := (hs.diff f.finite_to_set).Nonempty
  ⟨a, has, fun h => haf $ Finset.mem_coe.1 h⟩

section DecidableEq

theorem to_finset_compl {α : Type _} [Fintype α] [DecidableEq α] (s : Set α) [Fintype (sᶜ : Set α)] [Fintype s] :
    sᶜ.toFinset = s.to_finsetᶜ := by
  ext <;> simp

theorem to_finset_inter {α : Type _} [DecidableEq α] (s t : Set α) [Fintype (s ∩ t : Set α)] [Fintype s] [Fintype t] :
    (s ∩ t).toFinset = s.to_finset ∩ t.to_finset := by
  ext <;> simp

theorem to_finset_union {α : Type _} [DecidableEq α] (s t : Set α) [Fintype (s ∪ t : Set α)] [Fintype s] [Fintype t] :
    (s ∪ t).toFinset = s.to_finset ∪ t.to_finset := by
  ext <;> simp

instance fintype_sdiff {α : Type _} [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s \ t : Set α) :=
  Fintype.ofFinset (s.to_finset \ t.to_finset) $ by
    simp

theorem to_finset_sdiff {α : Type _} [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] [Fintype (s \ t : Set α)] :
    (s \ t).toFinset = s.to_finset \ t.to_finset := by
  ext <;> simp

theorem to_finset_ne_eq_erase {α : Type _} [DecidableEq α] [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    { x : α | x ≠ a }.toFinset = Finset.univ.erase a := by
  ext <;> simp

theorem card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    Fintype.card { x : α | x ≠ a } = Fintype.card α - 1 := by
  have := Classical.decEq α
  rw [← to_finset_card, to_finset_ne_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Nat.pred_eq_sub_one]

end DecidableEq

section

variable [SemilatticeSup α] [Nonempty α] {s : Set α}

/-- A finite set is bounded above.-/
protected theorem finite.bdd_above (hs : finite s) : BddAbove s :=
  finite.induction_on hs bdd_above_empty $ fun a s _ _ h => h.insert a

/-- A finite union of sets which are all bounded above is still bounded above.-/
theorem finite.bdd_above_bUnion {I : Set β} {S : β → Set α} (H : finite I) :
    BddAbove (⋃ i ∈ I, S i) ↔ ∀, ∀ i ∈ I, ∀, BddAbove (S i) :=
  finite.induction_on H
    (by
      simp only [bUnion_empty, bdd_above_empty, ball_empty_iff])
    fun a s ha _ hs => by
    simp only [bUnion_insert, ball_insert_iff, bdd_above_union, hs]

end

section

variable [SemilatticeInf α] [Nonempty α] {s : Set α}

/-- A finite set is bounded below.-/
protected theorem finite.bdd_below (hs : finite s) : BddBelow s :=
  @finite.bdd_above (OrderDual α) _ _ _ hs

/-- A finite union of sets which are all bounded below is still bounded below.-/
theorem finite.bdd_below_bUnion {I : Set β} {S : β → Set α} (H : finite I) :
    BddBelow (⋃ i ∈ I, S i) ↔ ∀, ∀ i ∈ I, ∀, BddBelow (S i) :=
  @finite.bdd_above_bUnion (OrderDual α) _ _ _ _ _ H

end

end Set

namespace Finset

/-- A finset is bounded above. -/
protected theorem BddAbove [SemilatticeSup α] [Nonempty α] (s : Finset α) : BddAbove (↑s : Set α) :=
  s.finite_to_set.bdd_above

/-- A finset is bounded below. -/
protected theorem BddBelow [SemilatticeInf α] [Nonempty α] (s : Finset α) : BddBelow (↑s : Set α) :=
  s.finite_to_set.bdd_below

end Finset

namespace Fintype

variable [Fintype α] {p q : α → Prop} [DecidablePred p] [DecidablePred q]

@[simp]
theorem card_subtype_compl : Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
  rw [Fintype.card_of_subtype (Set.toFinset (pᶜ)), Set.to_finset_compl p, Finset.card_compl,
      Fintype.card_of_subtype (Set.toFinset p)] <;>
    intros <;> simp <;> rfl

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
theorem card_compl_eq_card_compl (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  simp only [card_subtype_compl, h]

end Fintype

/-- If a set `s` does not contain any elements between any pair of elements `x, z ∈ s` with `x ≤ z`
(i.e if given `x, y, z ∈ s` such that `x ≤ y ≤ z`, then `y` is either `x` or `z`), then `s` is
finite.
-/
theorem Set.finite_of_forall_between_eq_endpoints {α : Type _} [LinearOrderₓ α] (s : Set α)
    (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, ∀ z ∈ s, ∀, x ≤ y → y ≤ z → x = y ∨ y = z) : Set.Finite s := by
  by_contra hinf
  change s.infinite at hinf
  rcases hinf.exists_subset_card_eq 3 with ⟨t, hts, ht⟩
  let f := t.order_iso_of_fin ht
  let x := f 0
  let y := f 1
  let z := f 2
  have :=
    h x (hts x.2) y (hts y.2) z (hts z.2)
      (f.monotone $ by
        decide)
      (f.monotone $ by
        decide)
  have key₁ : (0 : Finₓ 3) ≠ 1 := by
    decide
  have key₂ : (1 : Finₓ 3) ≠ 2 := by
    decide
  cases this
  · dsimp only [x, y]  at this
    exact key₁ (f.injective $ Subtype.coe_injective this)
    
  · dsimp only [y, z]  at this
    exact key₂ (f.injective $ Subtype.coe_injective this)
    

