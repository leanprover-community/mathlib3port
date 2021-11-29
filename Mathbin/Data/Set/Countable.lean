import Mathbin.Data.Equiv.List 
import Mathbin.Data.Set.Finite

/-!
# Countable sets
-/


noncomputable theory

open Function Set Encodable

open Classical hiding some

open_locale Classical

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Set

/-- A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
def countable (s : Set α) : Prop :=
  Nonempty (Encodable s)

theorem countable_iff_exists_injective {s : Set α} : countable s ↔ ∃ f : s → ℕ, injective f :=
  ⟨fun ⟨h⟩ =>
      by 
        exact ⟨encode, encode_injective⟩,
    fun ⟨f, h⟩ => ⟨⟨f, partial_inv f, partial_inv_left h⟩⟩⟩

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
theorem countable_iff_exists_inj_on {s : Set α} : countable s ↔ ∃ f : α → ℕ, inj_on f s :=
  countable_iff_exists_injective.trans
    ⟨fun ⟨f, hf⟩ =>
        ⟨fun a => if h : a ∈ s then f ⟨a, h⟩ else 0,
          fun a as b bs h =>
            congr_argₓ Subtype.val$
              hf$
                by 
                  simpa [as, bs] using h⟩,
      fun ⟨f, hf⟩ => ⟨_, inj_on_iff_injective.1 hf⟩⟩

-- error in Data.Set.Countable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem countable_iff_exists_surjective
[ne : nonempty α]
{s : set α} : «expr ↔ »(countable s, «expr∃ , »((f : exprℕ() → α), «expr ⊆ »(s, range f))) :=
⟨λ
 ⟨h⟩, by inhabit [expr α] []; exactI [expr ⟨λ
   n, ((decode s n).map subtype.val).iget, λ
   a
   as, ⟨encode (⟨a, as⟩ : s), by simp [] [] [] ["[", expr encodek, "]"] [] []⟩⟩], λ
 ⟨f, hf⟩, ⟨⟨λ x, inv_fun f x.1, λ n, if h : «expr ∈ »(f n, s) then some ⟨f n, h⟩ else none, λ ⟨x, hx⟩, begin
     have [] [] [":=", expr inv_fun_eq (hf hx)],
     dsimp [] [] [] ["at", ident this, "⊢"],
     simp [] [] [] ["[", expr this, ",", expr hx, "]"] [] []
   end⟩⟩⟩

/--
A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
theorem countable_iff_exists_surjective_to_subtype {s : Set α} (hs : s.nonempty) :
  countable s ↔ ∃ f : ℕ → s, surjective f :=
  have  : Inhabited s := ⟨Classical.choice hs.to_subtype⟩
  have  : countable s → ∃ f : ℕ → s, surjective f :=
    fun ⟨h⟩ =>
      by 
        exact
          ⟨fun n => (decode s n).iget,
            fun a =>
              ⟨encode a,
                by 
                  simp [encodek]⟩⟩
  have  : (∃ f : ℕ → s, surjective f) → countable s :=
    fun ⟨f, fsurj⟩ =>
      ⟨⟨inv_fun f, Option.some ∘ f,
          by 
            intro h <;> simp [(inv_fun_eq (fsurj h) : f (inv_fun f h) = h)]⟩⟩
  by 
    split  <;> assumption

/-- Convert `countable s` to `encodable s` (noncomputable). -/
def countable.to_encodable {s : Set α} : countable s → Encodable s :=
  Classical.choice

theorem countable_encodable' (s : Set α) [H : Encodable s] : countable s :=
  ⟨H⟩

theorem countable_encodable [Encodable α] (s : Set α) : countable s :=
  ⟨by 
      infer_instance⟩

-- error in Data.Set.Countable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
theorem countable.exists_surjective
{s : set α}
(hc : countable s)
(hs : s.nonempty) : «expr∃ , »((f : exprℕ() → α), «expr = »(s, range f)) :=
begin
  letI [] [":", expr encodable s] [":=", expr countable.to_encodable hc],
  letI [] [":", expr nonempty s] [":=", expr hs.to_subtype],
  have [] [":", expr countable (univ : set s)] [":=", expr countable_encodable _],
  rcases [expr countable_iff_exists_surjective.1 this, "with", "⟨", ident g, ",", ident hg, "⟩"],
  have [] [":", expr «expr = »(range g, univ)] [":=", expr univ_subset_iff.1 hg],
  use [expr «expr ∘ »(coe, g)],
  simp [] [] ["only"] ["[", expr range_comp, ",", expr this, ",", expr image_univ, ",", expr subtype.range_coe, "]"] [] []
end

@[simp]
theorem countable_empty : countable (∅ : Set α) :=
  ⟨⟨fun x => x.2.elim, fun n => none, fun x => x.2.elim⟩⟩

@[simp]
theorem countable_singleton (a : α) : countable ({a} : Set α) :=
  ⟨of_equiv _ (Equiv.Set.singleton a)⟩

theorem countable.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) : countable s₂ → countable s₁
| ⟨H⟩ => ⟨@of_inj _ _ H _ (embedding_of_subset _ _ h).2⟩

theorem countable.image {s : Set α} (hs : countable s) (f : α → β) : countable (f '' s) :=
  have  : surjective ((maps_to_image f s).restrict _ _ _) := surjective_maps_to_image_restrict f s
  ⟨@Encodable.ofInj _ _ hs.to_encodable (surj_inv this) (injective_surj_inv this)⟩

theorem countable_range [Encodable α] (f : α → β) : countable (range f) :=
  by 
    rw [←image_univ] <;> exact (countable_encodable _).Image _

theorem maps_to.countable_of_inj_on {s : Set α} {t : Set β} {f : α → β} (hf : maps_to f s t) (hf' : inj_on f s)
  (ht : countable t) : countable s :=
  have  : injective (hf.restrict f s t) := (inj_on_iff_injective.1 hf').codRestrict _
  ⟨@Encodable.ofInj _ _ ht.to_encodable _ this⟩

theorem countable.preimage_of_inj_on {s : Set β} (hs : countable s) {f : α → β} (hf : inj_on f (f ⁻¹' s)) :
  countable (f ⁻¹' s) :=
  (maps_to_preimage f s).countable_of_inj_on hf hs

protected theorem countable.preimage {s : Set β} (hs : countable s) {f : α → β} (hf : injective f) :
  countable (f ⁻¹' s) :=
  hs.preimage_of_inj_on (hf.inj_on _)

-- error in Data.Set.Countable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_seq_supr_eq_top_iff_countable
[complete_lattice α]
{p : α → exprProp()}
(h : «expr∃ , »((x), p x)) : «expr ↔ »(«expr∃ , »((s : exprℕ() → α), «expr ∧ »(∀
   n, p (s n), «expr = »(«expr⨆ , »((n), s n), «expr⊤»()))), «expr∃ , »((S : set α), «expr ∧ »(countable S, «expr ∧ »(∀
    s «expr ∈ » S, p s, «expr = »(Sup S, «expr⊤»()))))) :=
begin
  split,
  { rintro ["⟨", ident s, ",", ident hps, ",", ident hs, "⟩"],
    refine [expr ⟨range s, countable_range s, forall_range_iff.2 hps, _⟩],
    rwa [expr Sup_range] [] },
  { rintro ["⟨", ident S, ",", ident hSc, ",", ident hps, ",", ident hS, "⟩"],
    rcases [expr eq_empty_or_nonempty S, "with", ident rfl, "|", ident hne],
    { rw ["[", expr Sup_empty, "]"] ["at", ident hS],
      haveI [] [] [":=", expr subsingleton_of_bot_eq_top hS],
      rcases [expr h, "with", "⟨", ident x, ",", ident hx, "⟩"],
      exact [expr ⟨λ n, x, λ n, hx, subsingleton.elim _ _⟩] },
    { rcases [expr (countable_iff_exists_surjective_to_subtype hne).1 hSc, "with", "⟨", ident s, ",", ident hs, "⟩"],
      refine [expr ⟨λ n, s n, λ n, hps _ (s n).coe_prop, _⟩],
      rwa ["[", expr hs.supr_comp, ",", "<-", expr Sup_eq_supr', "]"] [] } }
end

theorem exists_seq_cover_iff_countable {p : Set α → Prop} (h : ∃ s, p s) :
  (∃ s : ℕ → Set α, (∀ n, p (s n)) ∧ (⋃n, s n) = univ) ↔
    ∃ S : Set (Set α), countable S ∧ (∀ s _ : s ∈ S, p s) ∧ ⋃₀S = univ :=
  exists_seq_supr_eq_top_iff_countable h

theorem countable_of_injective_of_countable_image {s : Set α} {f : α → β} (hf : inj_on f s) (hs : countable (f '' s)) :
  countable s :=
  let ⟨g, hg⟩ := countable_iff_exists_inj_on.1 hs 
  countable_iff_exists_inj_on.2 ⟨g ∘ f, hg.comp hf (maps_to_image _ _)⟩

-- error in Data.Set.Countable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem countable_Union {t : α → set β} [encodable α] (ht : ∀ a, countable (t a)) : countable «expr⋃ , »((a), t a) :=
by haveI [] [] [":=", expr λ a, (ht a).to_encodable]; rw [expr Union_eq_range_sigma] []; apply [expr countable_range]

-- error in Data.Set.Countable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem countable.bUnion
{s : set α}
{t : ∀ x «expr ∈ » s, set β}
(hs : countable s)
(ht : ∀ a «expr ∈ » s, countable (t a «expr‹ ›»(_))) : countable «expr⋃ , »((a «expr ∈ » s), t a «expr‹ ›»(_)) :=
begin
  rw [expr bUnion_eq_Union] [],
  haveI [] [] [":=", expr hs.to_encodable],
  exact [expr countable_Union (by simpa [] [] [] [] [] ["using", expr ht])]
end

theorem countable.sUnion {s : Set (Set α)} (hs : countable s) (h : ∀ a _ : a ∈ s, countable a) : countable (⋃₀s) :=
  by 
    rw [sUnion_eq_bUnion] <;> exact hs.bUnion h

theorem countable_Union_Prop {p : Prop} {t : p → Set β} (ht : ∀ h : p, countable (t h)) : countable (⋃h : p, t h) :=
  by 
    byCases' p <;> simp [h, ht]

theorem countable.union {s₁ s₂ : Set α} (h₁ : countable s₁) (h₂ : countable s₂) : countable (s₁ ∪ s₂) :=
  by 
    rw [union_eq_Union] <;> exact countable_Union (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp]
theorem countable_union {s t : Set α} : countable (s ∪ t) ↔ countable s ∧ countable t :=
  ⟨fun h => ⟨h.mono (subset_union_left s t), h.mono (subset_union_right _ _)⟩, fun h => h.1.union h.2⟩

@[simp]
theorem countable_insert {s : Set α} {a : α} : countable (insert a s) ↔ countable s :=
  by 
    simp only [insert_eq, countable_union, countable_singleton, true_andₓ]

theorem countable.insert {s : Set α} (a : α) (h : countable s) : countable (insert a s) :=
  countable_insert.2 h

theorem finite.countable {s : Set α} : finite s → countable s
| ⟨h⟩ =>
  Trunc.nonempty
    (by 
      exact trunc_encodable_of_fintype s)

theorem subsingleton.countable {s : Set α} (hs : s.subsingleton) : countable s :=
  hs.finite.countable

theorem countable_is_top (α : Type _) [PartialOrderₓ α] : countable { x:α | IsTop x } :=
  (finite_is_top α).Countable

theorem countable_is_bot (α : Type _) [PartialOrderₓ α] : countable { x:α | IsBot x } :=
  (finite_is_bot α).Countable

/-- The set of finite subsets of a countable set is countable. -/
theorem countable_set_of_finite_subset {s : Set α} : countable s → countable { t | finite t ∧ t ⊆ s }
| ⟨h⟩ =>
  by 
    skip 
    refine' countable.mono _ (countable_range fun t : Finset s => { a | ∃ h : a ∈ s, Subtype.mk a h ∈ t })
    rintro t ⟨⟨ht⟩, ts⟩
    skip 
    refine' ⟨finset.univ.map (embedding_of_subset _ _ ts), Set.ext$ fun a => _⟩
    suffices  : a ∈ s ∧ a ∈ t ↔ a ∈ t
    ·
      simpa 
    exact ⟨And.right, fun h => ⟨ts h, h⟩⟩

theorem countable_pi {π : α → Type _} [Fintype α] {s : ∀ a, Set (π a)} (hs : ∀ a, countable (s a)) :
  countable { f:∀ a, π a | ∀ a, f a ∈ s a } :=
  countable.mono
      (show { f:∀ a, π a | ∀ a, f a ∈ s a } ⊆ range fun f : ∀ a, s a => fun a => (f a).1 from
        fun f hf => ⟨fun a => ⟨f a, hf a⟩, funext$ fun a => rfl⟩)$
    have  : Trunc (Encodable (∀ a : α, s a)) := @Encodable.fintypePi α _ _ _ fun a => (hs a).toEncodable 
    Trunc.induction_on this$ fun h => @countable_range _ _ h _

-- error in Data.Set.Countable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem countable.prod {s : set α} {t : set β} (hs : countable s) (ht : countable t) : countable (set.prod s t) :=
begin
  haveI [] [":", expr encodable s] [":=", expr hs.to_encodable],
  haveI [] [":", expr encodable t] [":=", expr ht.to_encodable],
  haveI [] [":", expr encodable «expr × »(s, t)] [],
  { apply_instance },
  have [] [":", expr «expr = »(range (prod.map coe coe : «expr × »(s, t) → «expr × »(α, β)), set.prod s t)] [],
  by rw ["[", expr range_prod_map, ",", expr subtype.range_coe, ",", expr subtype.range_coe, "]"] [],
  rw ["<-", expr this] [],
  exact [expr countable_range _]
end

theorem countable.image2 {s : Set α} {t : Set β} (hs : countable s) (ht : countable t) (f : α → β → γ) :
  countable (image2 f s t) :=
  by 
    rw [←image_prod]
    exact (hs.prod ht).Image _

section Enumerate

/-- Enumerate elements in a countable set.-/
def enumerate_countable {s : Set α} (h : countable s) (default : α) : ℕ → α :=
  fun n =>
    match @Encodable.decode s h.to_encodable n with 
    | some y => y
    | none => default

theorem subset_range_enumerate {s : Set α} (h : countable s) (default : α) :
  s ⊆ range (enumerate_countable h default) :=
  fun x hx =>
    ⟨@Encodable.encode s h.to_encodable ⟨x, hx⟩,
      by 
        simp [enumerate_countable, Encodable.encodek]⟩

end Enumerate

end Set

theorem Finset.countable_to_set (s : Finset α) : Set.Countable («expr↑ » s : Set α) :=
  s.finite_to_set.countable

