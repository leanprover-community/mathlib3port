import Mathbin.Data.Set.Prod
import Mathbin.Logic.Function.Conjugate

/-!
# Functions over sets

## Main definitions

### Predicate

* `set.eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `set.maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `set.inj_on f s` : restriction of `f` to `s` is injective;
* `set.surj_on f s t` : every point in `s` has a preimage in `s`;
* `set.bij_on f s t` : `f` is a bijection between `s` and `t`;
* `set.left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `set.right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `set.inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `set.left_inv_on f' f s` and `set.right_inv_on f' f t`.

### Functions

* `set.restrict f s` : restrict the domain of `f` to the set `s`;
* `set.cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `set.maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/


universe u v w x y

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function

namespace Set

/-! ### Restrict -/


/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict (f : α → β) (s : Set α) : s → β := fun x => f x

theorem restrict_eq (f : α → β) (s : Set α) : s.restrict f = f ∘ coe :=
  rfl

@[simp]
theorem restrict_apply (f : α → β) (s : Set α) (x : s) : restrict f s x = f x :=
  rfl

@[simp]
theorem range_restrict (f : α → β) (s : Set α) : Set.Range (restrict f s) = f '' s :=
  (range_comp _ _).trans <| congr_argₓ ((· '' ·) f) Subtype.range_coe

theorem image_restrict (f : α → β) (s t : Set α) : s.restrict f '' (coe ⁻¹' t) = f '' (t ∩ s) := by
  rw [restrict, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (a «expr ∉ » s)
@[simp]
theorem restrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀, ∀ a ∈ s, ∀, β) (g : ∀ a _ : a ∉ s, β) :
    restrict (fun a => if h : a ∈ s then f a h else g a h) s = fun a => f a a.2 :=
  funext fun a => dif_pos a.2

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (a «expr ∉ » s)
@[simp]
theorem restrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀, ∀ a ∈ s, ∀, β) (g : ∀ a _ : a ∉ s, β) :
    restrict (fun a => if h : a ∈ s then f a h else g a h) (sᶜ) = fun a => g a a.2 :=
  funext fun a => dif_neg a.2

@[simp]
theorem restrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    restrict (fun a => if a ∈ s then f a else g a) s = restrict f s :=
  restrict_dite _ _

@[simp]
theorem restrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    restrict (fun a => if a ∈ s then f a else g a) (sᶜ) = restrict g (sᶜ) :=
  restrict_dite_compl _ _

@[simp]
theorem restrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    restrict (piecewise s f g) s = restrict f s :=
  restrict_ite _ _ _

@[simp]
theorem restrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    restrict (piecewise s f g) (sᶜ) = restrict g (sᶜ) :=
  restrict_ite_compl _ _ _

theorem restrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    restrict (extend f g g') (range f) = fun x => g x.coe_prop.some := by
  convert restrict_dite _ _

@[simp]
theorem restrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    restrict (extend f g g') (range fᶜ) = g' ∘ coe := by
  convert restrict_dite_compl _ _

theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) : range (extend f g g') ⊆ range g ∪ g' '' range fᶜ :=
  by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs
  exacts[Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]

theorem range_extend {f : α → β} (hf : injective f) (g : α → γ) (g' : β → γ) :
    range (extend f g g') = range g ∪ g' '' range fᶜ := by
  refine' (range_extend_subset _ _ _).antisymm _
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts[⟨f x, extend_apply hf _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]

/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def cod_restrict (f : α → β) (s : Set β) (h : ∀ x, f x ∈ s) : α → s := fun x => ⟨f x, h x⟩

@[simp]
theorem coe_cod_restrict_apply (f : α → β) (s : Set β) (h : ∀ x, f x ∈ s) (x : α) : (cod_restrict f s h x : β) = f x :=
  rfl

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ f₃ : α → β} {g g₁ g₂ : β → γ} {f' f₁' f₂' : β → α}
  {g' : γ → β}

@[simp]
theorem injective_cod_restrict (h : ∀ x, f x ∈ t) : injective (cod_restrict f t h) ↔ injective f := by
  simp only [injective, Subtype.ext_iff, coe_cod_restrict_apply]

alias injective_cod_restrict ↔ _ Function.Injective.cod_restrict

/-! ### Equality on a set -/


/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
def eq_on (f₁ f₂ : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

@[simp]
theorem eq_on_empty (f₁ f₂ : α → β) : eq_on f₁ f₂ ∅ := fun x => False.elim

@[symm]
theorem eq_on.symm (h : eq_on f₁ f₂ s) : eq_on f₂ f₁ s := fun x hx => (h hx).symm

theorem eq_on_comm : eq_on f₁ f₂ s ↔ eq_on f₂ f₁ s :=
  ⟨eq_on.symm, eq_on.symm⟩

@[refl]
theorem eq_on_refl (f : α → β) (s : Set α) : eq_on f f s := fun _ _ => rfl

@[trans]
theorem eq_on.trans (h₁ : eq_on f₁ f₂ s) (h₂ : eq_on f₂ f₃ s) : eq_on f₁ f₃ s := fun x hx => (h₁ hx).trans (h₂ hx)

theorem eq_on.image_eq (heq : eq_on f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  image_congr HEq

theorem eq_on.inter_preimage_eq (heq : eq_on f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t :=
  ext fun x =>
    And.congr_right_iff.2 fun hx => by
      rw [mem_preimage, mem_preimage, HEq hx]

theorem eq_on.mono (hs : s₁ ⊆ s₂) (hf : eq_on f₁ f₂ s₂) : eq_on f₁ f₂ s₁ := fun x hx => hf (hs hx)

theorem eq_on.comp_left (h : s.eq_on f₁ f₂) : s.eq_on (g ∘ f₁) (g ∘ f₂) := fun a ha => congr_argₓ _ <| h ha

theorem comp_eq_of_eq_on_range {ι : Sort _} {f : ι → α} {g₁ g₂ : α → β} (h : eq_on g₁ g₂ (range f)) : g₁ ∘ f = g₂ ∘ f :=
  funext fun x => h <| mem_range_self _

/-! ### Congruence lemmas -/


section Order

variable [Preorderₓ α] [Preorderₓ β]

theorem _root_.monotone_on.congr (h₁ : MonotoneOn f₁ s) (h : s.eq_on f₁ f₂) : MonotoneOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab

theorem _root_.antitone_on.congr (h₁ : AntitoneOn f₁ s) (h : s.eq_on f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h

theorem _root_.strict_mono_on.congr (h₁ : StrictMonoOn f₁ s) (h : s.eq_on f₁ f₂) : StrictMonoOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab

theorem _root_.strict_anti_on.congr (h₁ : StrictAntiOn f₁ s) (h : s.eq_on f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h

theorem eq_on.congr_monotone_on (h : s.eq_on f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

theorem eq_on.congr_antitone_on (h : s.eq_on f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

theorem eq_on.congr_strict_mono_on (h : s.eq_on f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

theorem eq_on.congr_strict_anti_on (h : s.eq_on f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

end Order

/-! ### maps to -/


/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
@[reducible]
def maps_to (f : α → β) (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x ∈ t

/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def maps_to.restrict (f : α → β) (s : Set α) (t : Set β) (h : maps_to f s t) : s → t :=
  Subtype.map f h

@[simp]
theorem maps_to.coe_restrict_apply (h : maps_to f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl

theorem maps_to_iff_exists_map_subtype : maps_to f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    erw [hg ⟨x, hx⟩]
    apply Subtype.coe_prop⟩

theorem maps_to' : maps_to f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm

@[simp]
theorem maps_to_singleton {x : α} : maps_to f {x} t ↔ f x ∈ t :=
  singleton_subset_iff

theorem maps_to_empty (f : α → β) (t : Set β) : maps_to f ∅ t :=
  empty_subset _

theorem maps_to.image_subset (h : maps_to f s t) : f '' s ⊆ t :=
  maps_to'.1 h

theorem maps_to.congr (h₁ : maps_to f₁ s t) (h : eq_on f₁ f₂ s) : maps_to f₂ s t := fun x hx => h hx ▸ h₁ hx

theorem eq_on.comp_right (hg : t.eq_on g₁ g₂) (hf : s.maps_to f t) : s.eq_on (g₁ ∘ f) (g₂ ∘ f) := fun a ha =>
  hg <| hf ha

theorem eq_on.maps_to_iff (H : eq_on f₁ f₂ s) : maps_to f₁ s t ↔ maps_to f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem maps_to.comp (h₁ : maps_to g t p) (h₂ : maps_to f s t) : maps_to (g ∘ f) s p := fun x h => h₁ (h₂ h)

theorem maps_to_id (s : Set α) : maps_to id s s := fun x => id

theorem maps_to.iterate {f : α → α} {s : Set α} (h : maps_to f s s) : ∀ n, maps_to (f^[n]) s s
  | 0 => fun _ => id
  | n + 1 => (maps_to.iterate n).comp h

theorem maps_to.iterate_restrict {f : α → α} {s : Set α} (h : maps_to f s s) (n : ℕ) :
    h.restrict f s s^[n] = (h.iterate n).restrict _ _ _ := by
  funext x
  rw [Subtype.ext_iff, maps_to.coe_restrict_apply]
  induction' n with n ihn generalizing x
  · rfl
    
  · simp [Nat.iterate, ihn]
    

theorem maps_to.mono (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) (hf : maps_to f s₁ t₁) : maps_to f s₂ t₂ := fun x hx =>
  ht (hf <| hs hx)

theorem maps_to.union_union (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) : maps_to f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx

theorem maps_to.union (h₁ : maps_to f s₁ t) (h₂ : maps_to f s₂ t) : maps_to f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂

@[simp]
theorem maps_to_union : maps_to f (s₁ ∪ s₂) t ↔ maps_to f s₁ t ∧ maps_to f s₂ t :=
  ⟨fun h => ⟨h.mono (subset_union_left s₁ s₂) (subset.refl t), h.mono (subset_union_right s₁ s₂) (subset.refl t)⟩,
    fun h => h.1.union h.2⟩

theorem maps_to.inter (h₁ : maps_to f s t₁) (h₂ : maps_to f s t₂) : maps_to f s (t₁ ∩ t₂) := fun x hx => ⟨h₁ hx, h₂ hx⟩

theorem maps_to.inter_inter (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) : maps_to f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun x hx =>
  ⟨h₁ hx.1, h₂ hx.2⟩

@[simp]
theorem maps_to_inter : maps_to f s (t₁ ∩ t₂) ↔ maps_to f s t₁ ∧ maps_to f s t₂ :=
  ⟨fun h => ⟨h.mono (subset.refl s) (inter_subset_left t₁ t₂), h.mono (subset.refl s) (inter_subset_right t₁ t₂)⟩,
    fun h => h.1.inter h.2⟩

theorem maps_to_univ (f : α → β) (s : Set α) : maps_to f s univ := fun x h => trivialₓ

theorem maps_to_image (f : α → β) (s : Set α) : maps_to f s (f '' s) := by
  rw [maps_to']

theorem maps_to_preimage (f : α → β) (t : Set β) : maps_to f (f ⁻¹' t) t :=
  subset.refl _

theorem maps_to_range (f : α → β) (s : Set α) : maps_to f s (range f) :=
  (maps_to_image f s).mono (subset.refl s) (image_subset_range _ _)

@[simp]
theorem maps_image_to (f : α → β) (g : γ → α) (s : Set γ) (t : Set β) : maps_to f (g '' s) t ↔ maps_to (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h d ⟨c, hc⟩ => hc.2 ▸ h hc.1⟩

@[simp]
theorem maps_univ_to (f : α → β) (s : Set β) : maps_to f univ s ↔ ∀ a, f a ∈ s :=
  ⟨fun h a => h (mem_univ _), fun h x _ => h x⟩

@[simp]
theorem maps_range_to (f : α → β) (g : γ → α) (s : Set β) : maps_to f (range g) s ↔ maps_to (f ∘ g) univ s := by
  rw [← image_univ, maps_image_to]

theorem surjective_maps_to_image_restrict (f : α → β) (s : Set α) :
    surjective ((maps_to_image f s).restrict f s (f '' s)) := fun ⟨y, x, hs, hxy⟩ => ⟨⟨x, hs⟩, Subtype.ext hxy⟩

theorem maps_to.mem_iff (h : maps_to f s t) (hc : maps_to f (sᶜ) (tᶜ)) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩

/-! ### Injectivity on a set -/


/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
@[reducible]
def inj_on (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

theorem subsingleton.inj_on (hs : s.subsingleton) (f : α → β) : inj_on f s := fun x hx y hy h => hs hx hy

@[simp]
theorem inj_on_empty (f : α → β) : inj_on f ∅ :=
  subsingleton_empty.InjOn f

@[simp]
theorem inj_on_singleton (f : α → β) (a : α) : inj_on f {a} :=
  subsingleton_singleton.InjOn f

theorem inj_on.eq_iff {x y} (h : inj_on f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩

theorem inj_on.congr (h₁ : inj_on f₁ s) (h : eq_on f₁ f₂ s) : inj_on f₂ s := fun x hx y hy => h hx ▸ h hy ▸ h₁ hx hy

theorem eq_on.inj_on_iff (H : eq_on f₁ f₂ s) : inj_on f₁ s ↔ inj_on f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem inj_on.mono (h : s₁ ⊆ s₂) (ht : inj_on f s₂) : inj_on f s₁ := fun x hx y hy H => ht (h hx) (h hy) H

theorem inj_on_union (h : Disjoint s₁ s₂) :
    inj_on f (s₁ ∪ s₂) ↔ inj_on f s₁ ∧ inj_on f s₂ ∧ ∀, ∀ x ∈ s₁, ∀, ∀ y ∈ s₂, ∀, f x ≠ f y := by
  refine' ⟨fun H => ⟨H.mono <| subset_union_left _ _, H.mono <| subset_union_right _ _, _⟩, _⟩
  · intro x hx y hy hxy
    obtain rfl : x = y
    exact H (Or.inl hx) (Or.inr hy) hxy
    exact h ⟨hx, hy⟩
    
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts[h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]
    

theorem inj_on_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := by
  have : Disjoint s {a} := fun x ⟨hxs, (hxa : x = a)⟩ => has (hxa ▸ hxs)
  rw [← union_singleton, inj_on_union this]
  simp

theorem injective_iff_inj_on_univ : injective f ↔ inj_on f univ :=
  ⟨fun h x hx y hy hxy => h hxy, fun h _ _ heq => h trivialₓ trivialₓ HEq⟩

theorem inj_on_of_injective (h : injective f) (s : Set α) : inj_on f s := fun x hx y hy hxy => h hxy

alias inj_on_of_injective ← Function.Injective.inj_on

theorem inj_on.comp (hg : inj_on g t) (hf : inj_on f s) (h : maps_to f s t) : inj_on (g ∘ f) s := fun x hx y hy heq =>
  hf hx hy <| hg (h hx) (h hy) HEq

theorem inj_on_iff_injective : inj_on f s ↔ injective (restrict f s) :=
  ⟨fun H a b h => Subtype.eq <| H a.2 b.2 h, fun H a as b bs h => congr_argₓ Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias inj_on_iff_injective ↔ Set.InjOn.injective _

theorem inj_on_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 range f) : inj_on (preimage f) B := fun s hs t ht hst =>
  (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

theorem inj_on.mem_of_mem_image {x} (hf : inj_on f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) : x ∈ s₁ :=
  let ⟨x', h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'

theorem inj_on.mem_image_iff {x} (hf : inj_on f s) (hs : s₁ ⊆ s) (hx : x ∈ s) : f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩

theorem inj_on.preimage_image_inter (hf : inj_on f s) (hs : s₁ ⊆ s) : f ⁻¹' (f '' s₁) ∩ s = s₁ :=
  ext fun x => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩

theorem eq_on.cancel_left (h : s.eq_on (g ∘ f₁) (g ∘ f₂)) (hg : t.inj_on g) (hf₁ : s.maps_to f₁ t)
    (hf₂ : s.maps_to f₂ t) : s.eq_on f₁ f₂ := fun a ha => hg (hf₁ ha) (hf₂ ha) (h ha)

theorem inj_on.cancel_left (hg : t.inj_on g) (hf₁ : s.maps_to f₁ t) (hf₂ : s.maps_to f₂ t) :
    s.eq_on (g ∘ f₁) (g ∘ f₂) ↔ s.eq_on f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, eq_on.comp_left⟩

/-! ### Surjectivity on a set -/


/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
@[reducible]
def surj_on (f : α → β) (s : Set α) (t : Set β) : Prop :=
  t ⊆ f '' s

theorem surj_on.subset_range (h : surj_on f s t) : t ⊆ range f :=
  subset.trans h <| image_subset_range f s

theorem surj_on_iff_exists_map_subtype :
    surj_on f s t ↔ ∃ (t' : Set β)(g : s → t'), t ⊆ t' ∧ surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h => ⟨_, (maps_to_image f s).restrict f s _, h, surjective_maps_to_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by
      rw [hfg, hx, Subtype.coe_mk]⟩⟩

theorem surj_on_empty (f : α → β) (s : Set α) : surj_on f s ∅ :=
  empty_subset _

theorem surj_on_image (f : α → β) (s : Set α) : surj_on f s (f '' s) :=
  subset.rfl

theorem surj_on.comap_nonempty (h : surj_on f s t) (ht : t.nonempty) : s.nonempty :=
  (ht.mono h).of_image

theorem surj_on.congr (h : surj_on f₁ s t) (H : eq_on f₁ f₂ s) : surj_on f₂ s t := by
  rwa [surj_on, ← H.image_eq]

theorem eq_on.surj_on_iff (h : eq_on f₁ f₂ s) : surj_on f₁ s t ↔ surj_on f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩

theorem surj_on.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : surj_on f s₁ t₂) : surj_on f s₂ t₁ :=
  subset.trans ht <| subset.trans hf <| image_subset _ hs

theorem surj_on.union (h₁ : surj_on f s t₁) (h₂ : surj_on f s t₂) : surj_on f s (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx

theorem surj_on.union_union (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) : surj_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono (subset_union_left _ _) (subset.refl _)).union (h₂.mono (subset_union_right _ _) (subset.refl _))

theorem surj_on.inter_inter (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
    surj_on f (s₁ ∩ s₂) (t₁ ∩ t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  have : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) HEq.symm
  subst x₂
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩

theorem surj_on.inter (h₁ : surj_on f s₁ t) (h₂ : surj_on f s₂ t) (h : inj_on f (s₁ ∪ s₂)) : surj_on f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h

theorem surj_on.comp (hg : surj_on g t p) (hf : surj_on f s t) : surj_on (g ∘ f) s p :=
  subset.trans hg <| subset.trans (image_subset g hf) <| image_comp g f s ▸ subset.refl _

theorem surjective_iff_surj_on_univ : surjective f ↔ surj_on f univ univ := by
  simp [surjective, surj_on, subset_def]

theorem surj_on_iff_surjective : surj_on f s univ ↔ surjective (restrict f s) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivialₓ
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩

theorem surj_on.image_eq_of_maps_to (h₁ : surj_on f s t) (h₂ : maps_to f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁

theorem image_eq_iff_surj_on_maps_to : f '' s = t ↔ s.surj_on f t ∧ s.maps_to f t := by
  refine' ⟨_, fun h => h.1.image_eq_of_maps_to h.2⟩
  rintro rfl
  exact ⟨s.surj_on_image f, s.maps_to_image f⟩

theorem surj_on.maps_to_compl (h : surj_on f s t) (h' : injective f) : maps_to f (sᶜ) (tᶜ) := fun x hs ht =>
  let ⟨x', hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'

theorem maps_to.surj_on_compl (h : maps_to f s t) (h' : surjective f) : surj_on f (sᶜ) (tᶜ) :=
  h'.forall.2 fun x ht => (mem_image_of_mem _) fun hs => ht (h hs)

theorem eq_on.cancel_right (hf : s.eq_on (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.surj_on f t) : t.eq_on g₁ g₂ := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha

theorem surj_on.cancel_right (hf : s.surj_on f t) (hf' : s.maps_to f t) : s.eq_on (g₁ ∘ f) (g₂ ∘ f) ↔ t.eq_on g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.comp_right hf'⟩

theorem eq_on_comp_right_iff : s.eq_on (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surj_on_image f).cancel_right <| s.maps_to_image f

/-! ### Bijectivity -/


/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
@[reducible]
def bij_on (f : α → β) (s : Set α) (t : Set β) : Prop :=
  maps_to f s t ∧ inj_on f s ∧ surj_on f s t

theorem bij_on.maps_to (h : bij_on f s t) : maps_to f s t :=
  h.left

theorem bij_on.inj_on (h : bij_on f s t) : inj_on f s :=
  h.right.left

theorem bij_on.surj_on (h : bij_on f s t) : surj_on f s t :=
  h.right.right

theorem bij_on.mk (h₁ : maps_to f s t) (h₂ : inj_on f s) (h₃ : surj_on f s t) : bij_on f s t :=
  ⟨h₁, h₂, h₃⟩

theorem bij_on_empty (f : α → β) : bij_on f ∅ ∅ :=
  ⟨maps_to_empty f ∅, inj_on_empty f, surj_on_empty f ∅⟩

theorem bij_on.inter (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
    bij_on f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.maps_to.inter_inter h₂.maps_to, h₁.inj_on.mono <| inter_subset_left _ _, h₁.surj_on.inter_inter h₂.surj_on h⟩

theorem bij_on.union (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) :
    bij_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.maps_to.union_union h₂.maps_to, h, h₁.surj_on.union_union h₂.surj_on⟩

theorem bij_on.subset_range (h : bij_on f s t) : t ⊆ range f :=
  h.surj_on.subset_range

theorem inj_on.bij_on_image (h : inj_on f s) : bij_on f s (f '' s) :=
  bij_on.mk (maps_to_image f s) h (subset.refl _)

theorem bij_on.congr (h₁ : bij_on f₁ s t) (h : eq_on f₁ f₂ s) : bij_on f₂ s t :=
  bij_on.mk (h₁.maps_to.congr h) (h₁.inj_on.congr h) (h₁.surj_on.congr h)

theorem eq_on.bij_on_iff (H : eq_on f₁ f₂ s) : bij_on f₁ s t ↔ bij_on f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem bij_on.image_eq (h : bij_on f s t) : f '' s = t :=
  h.surj_on.image_eq_of_maps_to h.maps_to

theorem bij_on.comp (hg : bij_on g t p) (hf : bij_on f s t) : bij_on (g ∘ f) s p :=
  bij_on.mk (hg.maps_to.comp hf.maps_to) (hg.inj_on.comp hf.inj_on hf.maps_to) (hg.surj_on.comp hf.surj_on)

theorem bij_on.bijective (h : bij_on f s t) :
    bijective ((t.cod_restrict (s.restrict f)) fun x => h.maps_to x.val_prop) :=
  ⟨fun x y h' => Subtype.ext <| h.inj_on x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨y, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.surj_on hy
    ⟨⟨x, hx⟩, Subtype.eq hxy⟩⟩

theorem bijective_iff_bij_on_univ : bijective f ↔ bij_on f univ univ :=
  Iff.intro
    (fun h =>
      let ⟨inj, surj⟩ := h
      ⟨maps_to_univ f _, inj.inj_on _, Iff.mp surjective_iff_surj_on_univ surj⟩)
    fun h =>
    let ⟨map, inj, surj⟩ := h
    ⟨Iff.mpr injective_iff_inj_on_univ inj, Iff.mpr surjective_iff_surj_on_univ surj⟩

theorem bij_on.compl (hst : bij_on f s t) (hf : bijective f) : bij_on f (sᶜ) (tᶜ) :=
  ⟨hst.surj_on.maps_to_compl hf.1, hf.1.InjOn _, hst.maps_to.surj_on_compl hf.2⟩

/-! ### left inverse -/


/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
@[reducible]
def left_inv_on (f' : β → α) (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f' (f x) = x

theorem left_inv_on.eq_on (h : left_inv_on f' f s) : eq_on (f' ∘ f) id s :=
  h

theorem left_inv_on.eq (h : left_inv_on f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx

theorem left_inv_on.congr_left (h₁ : left_inv_on f₁' f s) {t : Set β} (h₁' : maps_to f s t) (heq : eq_on f₁' f₂' t) :
    left_inv_on f₂' f s := fun x hx => HEq (h₁' hx) ▸ h₁ hx

theorem left_inv_on.congr_right (h₁ : left_inv_on f₁' f₁ s) (heq : eq_on f₁ f₂ s) : left_inv_on f₁' f₂ s := fun x hx =>
  HEq hx ▸ h₁ hx

theorem left_inv_on.inj_on (h : left_inv_on f₁' f s) : inj_on f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := congr_argₓ f₁' HEq
    _ = x₂ := h h₂
    

theorem left_inv_on.surj_on (h : left_inv_on f' f s) (hf : maps_to f s t) : surj_on f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩

theorem left_inv_on.maps_to (h : left_inv_on f' f s) (hf : surj_on f s t) : maps_to f' t s := fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]

theorem left_inv_on.comp (hf' : left_inv_on f' f s) (hg' : left_inv_on g' g t) (hf : maps_to f s t) :
    left_inv_on (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_argₓ f' (hg' (hf h))
    _ = x := hf' h
    

theorem left_inv_on.mono (hf : left_inv_on f' f s) (ht : s₁ ⊆ s) : left_inv_on f' f s₁ := fun x hx => hf (ht hx)

theorem left_inv_on.image_inter' (hf : left_inv_on f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s := by
  apply subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact
      ⟨by
        rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
    
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact
      mem_image_of_mem _
        ⟨by
          rwa [← hf h], h⟩
    

theorem left_inv_on.image_inter (hf : left_inv_on f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s := by
  rw [hf.image_inter']
  refine' subset.antisymm _ (inter_subset_inter_left _ (preimage_mono <| inter_subset_left _ _))
  rintro _ ⟨h₁, x, hx, rfl⟩
  exact
    ⟨⟨h₁, by
        rwa [hf hx]⟩,
      mem_image_of_mem _ hx⟩

theorem left_inv_on.image_image (hf : left_inv_on f' f s) : f' '' (f '' s) = s := by
  rw [image_image, image_congr hf, image_id']

theorem left_inv_on.image_image' (hf : left_inv_on f' f s) (hs : s₁ ⊆ s) : f' '' (f '' s₁) = s₁ :=
  (hf.mono hs).image_image

/-! ### Right inverse -/


/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible]
def right_inv_on (f' : β → α) (f : α → β) (t : Set β) : Prop :=
  left_inv_on f f' t

theorem right_inv_on.eq_on (h : right_inv_on f' f t) : eq_on (f ∘ f') id t :=
  h

theorem right_inv_on.eq (h : right_inv_on f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy

theorem left_inv_on.right_inv_on_image (h : left_inv_on f' f s) : right_inv_on f' f (f '' s) := fun y ⟨x, hx, Eq⟩ =>
  Eq ▸ congr_argₓ f <| h.eq hx

theorem right_inv_on.congr_left (h₁ : right_inv_on f₁' f t) (heq : eq_on f₁' f₂' t) : right_inv_on f₂' f t :=
  h₁.congr_right HEq

theorem right_inv_on.congr_right (h₁ : right_inv_on f' f₁ t) (hg : maps_to f' t s) (heq : eq_on f₁ f₂ s) :
    right_inv_on f' f₂ t :=
  left_inv_on.congr_left h₁ hg HEq

theorem right_inv_on.surj_on (hf : right_inv_on f' f t) (hf' : maps_to f' t s) : surj_on f s t :=
  hf.surj_on hf'

theorem right_inv_on.maps_to (h : right_inv_on f' f t) (hf : surj_on f' t s) : maps_to f s t :=
  h.maps_to hf

theorem right_inv_on.comp (hf : right_inv_on f' f t) (hg : right_inv_on g' g p) (g'pt : maps_to g' p t) :
    right_inv_on (f' ∘ g') (g ∘ f) p :=
  hg.comp hf g'pt

theorem right_inv_on.mono (hf : right_inv_on f' f t) (ht : t₁ ⊆ t) : right_inv_on f' f t₁ :=
  hf.mono ht

theorem inj_on.right_inv_on_of_left_inv_on (hf : inj_on f s) (hf' : left_inv_on f f' t) (h₁ : maps_to f s t)
    (h₂ : maps_to f' t s) : right_inv_on f f' s := fun x h => hf (h₂ <| h₁ h) h (hf' (h₁ h))

theorem eq_on_of_left_inv_on_of_right_inv_on (h₁ : left_inv_on f₁' f s) (h₂ : right_inv_on f₂' f t)
    (h : maps_to f₂' t s) : eq_on f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_argₓ f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
    

theorem surj_on.left_inv_on_of_right_inv_on (hf : surj_on f s t) (hf' : right_inv_on f f' s) : left_inv_on f f' t :=
  fun y hy => by
  let ⟨x, hx, HEq⟩ := hf hy
  rw [← HEq, hf' hx]

/-! ### Two-side inverses -/


/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
@[reducible]
def inv_on (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  left_inv_on g f s ∧ right_inv_on g f t

theorem inv_on.symm (h : inv_on f' f s t) : inv_on f f' t s :=
  ⟨h.right, h.left⟩

theorem inv_on.mono (h : inv_on f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : inv_on f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem inv_on.bij_on (h : inv_on f' f s t) (hf : maps_to f s t) (hf' : maps_to f' t s) : bij_on f s t :=
  ⟨hf, h.left.inj_on, h.right.surj_on hf'⟩

end Set

/-! ### `inv_fun_on` is a left/right inverse -/


namespace Function

variable [Nonempty α] {s : Set α} {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `function.injective.inv_of_mem_range`. -/
noncomputable def inv_fun_on (f : α → β) (s : Set α) (b : β) : α :=
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.some h else Classical.choice ‹Nonempty α›

theorem inv_fun_on_pos (h : ∃ a ∈ s, f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_pos h] <;> exact Classical.some_spec h

theorem inv_fun_on_mem (h : ∃ a ∈ s, f a = b) : inv_fun_on f s b ∈ s :=
  (inv_fun_on_pos h).left

theorem inv_fun_on_eq (h : ∃ a ∈ s, f a = b) : f (inv_fun_on f s b) = b :=
  (inv_fun_on_pos h).right

theorem inv_fun_on_neg (h : ¬∃ a ∈ s, f a = b) : inv_fun_on f s b = Classical.choice ‹Nonempty α› := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_neg h]

end Function

namespace Set

open Function

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

theorem inj_on.left_inv_on_inv_fun_on [Nonempty α] (h : inj_on f s) : left_inv_on (inv_fun_on f s) f s := fun a ha =>
  have : ∃ a' ∈ s, f a' = f a := ⟨a, ha, rfl⟩
  h (inv_fun_on_mem this) ha (inv_fun_on_eq this)

theorem inj_on.inv_fun_on_image [Nonempty α] (h : inj_on f s₂) (ht : s₁ ⊆ s₂) : inv_fun_on f s₂ '' (f '' s₁) = s₁ :=
  h.left_inv_on_inv_fun_on.image_image' ht

theorem surj_on.right_inv_on_inv_fun_on [Nonempty α] (h : surj_on f s t) : right_inv_on (inv_fun_on f s) f t :=
  fun y hy => inv_fun_on_eq <| mem_image_iff_bex.1 <| h hy

theorem bij_on.inv_on_inv_fun_on [Nonempty α] (h : bij_on f s t) : inv_on (inv_fun_on f s) f s t :=
  ⟨h.inj_on.left_inv_on_inv_fun_on, h.surj_on.right_inv_on_inv_fun_on⟩

theorem surj_on.inv_on_inv_fun_on [Nonempty α] (h : surj_on f s t) :
    inv_on (inv_fun_on f s) f (inv_fun_on f s '' t) t := by
  refine' ⟨_, h.right_inv_on_inv_fun_on⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.right_inv_on_inv_fun_on hy]

theorem surj_on.maps_to_inv_fun_on [Nonempty α] (h : surj_on f s t) : maps_to (inv_fun_on f s) t s := fun y hy =>
  mem_preimage.2 <| inv_fun_on_mem <| mem_image_iff_bex.1 <| h hy

theorem surj_on.bij_on_subset [Nonempty α] (h : surj_on f s t) : bij_on f (inv_fun_on f s '' t) t := by
  refine' h.inv_on_inv_fun_on.bij_on _ (maps_to_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.right_inv_on_inv_fun_on hy]

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (s' «expr ⊆ » s)
theorem surj_on_iff_exists_bij_on_subset : surj_on f s t ↔ ∃ (s' : _)(_ : s' ⊆ s), bij_on f s' t := by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bij_on_empty f⟩
      
    · intro h
      have : Nonempty α := ⟨Classical.some (h.comap_nonempty ht)⟩
      exact ⟨_, h.maps_to_inv_fun_on.image_subset, h.bij_on_subset⟩
      
    
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surj_on.mono hs' (subset.refl _)
    

theorem preimage_inv_fun_of_mem [n : Nonempty α] {f : α → β} (hf : injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : inv_fun f ⁻¹' s = f '' s ∪ range fᶜ := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp [left_inverse_inv_fun hf _, hf.mem_set_image]
    
  · simp [mem_preimage, inv_fun_neg hx, h, hx]
    

theorem preimage_inv_fun_of_not_mem [n : Nonempty α] {f : α → β} (hf : injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : inv_fun f ⁻¹' s = f '' s := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, left_inverse_inv_fun hf, hf.mem_set_image]
    
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, inv_fun_neg hx, h, this]
    

end Set

/-! ### Monotone -/


namespace Monotone

variable [Preorderₓ α] [Preorderₓ β] {f : α → β}

protected theorem restrict (h : Monotone f) (s : Set α) : Monotone (s.restrict f) := fun x y hxy => h hxy

protected theorem cod_restrict (h : Monotone f) {s : Set β} (hs : ∀ x, f x ∈ s) : Monotone (s.cod_restrict f hs) :=
  h

protected theorem range_factorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h

end Monotone

/-! ### Piecewise defined function -/


namespace Set

variable {δ : α → Sort y} (s : Set α) (f g : ∀ i, δ i)

@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Set α))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]

@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (Set.Univ : Set α))] : piecewise Set.Univ f g = f := by
  ext i
  simp [piecewise]

@[simp]
theorem piecewise_insert_self {j : α} [∀ i, Decidable (i ∈ insert j s)] : (insert j s).piecewise f g j = f j := by
  simp [piecewise]

variable [∀ j, Decidable (j ∈ s)]

instance compl.decidable_mem (j : α) : Decidable (j ∈ sᶜ) :=
  Not.decidable

theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) := by
  simp [piecewise]
  ext i
  by_cases' h : i = j
  · rw [h]
    simp
    
  · by_cases' h' : i ∈ s <;> simp [h, h']
    

@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
  if_pos hi

@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  if_neg hi

theorem piecewise_singleton (x : α) [∀ y, Decidable (y ∈ ({x} : Set α))] [DecidableEq α] (f g : α → β) :
    piecewise {x} f g = Function.update g x (f x) := by
  ext y
  by_cases' hy : y = x
  · subst y
    simp
    
  · simp [hy]
    

theorem piecewise_eq_on (f g : α → β) : eq_on (s.piecewise f g) f s := fun _ => piecewise_eq_of_mem _ _ _

theorem piecewise_eq_on_compl (f g : α → β) : eq_on (s.piecewise f g) g (sᶜ) := fun _ => piecewise_eq_of_not_mem _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (i «expr ∉ » s)
theorem piecewise_le {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g : ∀ i, δ i}
    (h₁ : ∀, ∀ i ∈ s, ∀, f₁ i ≤ g i) (h₂ : ∀ i _ : i ∉ s, f₂ i ≤ g i) : s.piecewise f₁ f₂ ≤ g := fun i =>
  if h : i ∈ s then by
    simp [*]
  else by
    simp [*]

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (i «expr ∉ » s)
theorem le_piecewise {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g : ∀ i, δ i}
    (h₁ : ∀, ∀ i ∈ s, ∀, g i ≤ f₁ i) (h₂ : ∀ i _ : i ∉ s, g i ≤ f₂ i) : g ≤ s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => OrderDual (δ i)) _ s _ _ _ _ h₁ h₂

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (i «expr ∉ » s)
theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g₁ g₂ : ∀ i, δ i} (h₁ : ∀, ∀ i ∈ s, ∀, f₁ i ≤ g₁ i) (h₂ : ∀ i _ : i ∉ s, f₂ i ≤ g₂ i) :
    s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ := by
  apply piecewise_le <;> intros <;> simp [*]

@[simp]
theorem piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g i = s.piecewise f g i := by
  simp [piecewise, h]

@[simp]
theorem piecewise_compl [∀ i, Decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
  funext fun x =>
    if hx : x ∈ s then by
      simp [hx]
    else by
      simp [hx]

@[simp]
theorem piecewise_range_comp {ι : Sort _} (f : ι → α) [∀ j, Decidable (j ∈ range f)] (g₁ g₂ : α → β) :
    (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  comp_eq_of_eq_on_range <| piecewise_eq_on _ _ _

theorem maps_to.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α → β} [∀ i, Decidable (i ∈ s)]
    (h₁ : maps_to f₁ (s₁ ∩ s) (t₁ ∩ t)) (h₂ : maps_to f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) :
    maps_to (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) := by
  refine' (h₁.congr _).union_union (h₂.congr _)
  exacts[(piecewise_eq_on s f₁ f₂).symm.mono (inter_subset_right _ _),
    (piecewise_eq_on_compl s f₁ f₂).symm.mono (inter_subset_right _ _)]

theorem eq_on_piecewise {f f' g : α → β} {t} : eq_on (s.piecewise f f') g t ↔ eq_on f g (t ∩ s) ∧ eq_on f' g (t ∩ sᶜ) :=
  by
  simp only [eq_on, ← forall_and_distrib]
  refine' forall_congrₓ fun a => _
  by_cases' a ∈ s <;> simp [*]

theorem eq_on.piecewise_ite' {f f' g : α → β} {t t'} (h : eq_on f g (t ∩ s)) (h' : eq_on f' g (t' ∩ sᶜ)) :
    eq_on (s.piecewise f f') g (s.ite t t') := by
  simp [eq_on_piecewise, *]

theorem eq_on.piecewise_ite {f f' g : α → β} {t t'} (h : eq_on f g t) (h' : eq_on f' g t') :
    eq_on (s.piecewise f f') g (s.ite t t') :=
  (h.mono (inter_subset_left _ _)).piecewise_ite' s (h'.mono (inter_subset_left _ _))

theorem piecewise_preimage (f g : α → β) t : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by
    by_cases' x ∈ s <;> simp [*, Set.Ite]

theorem apply_piecewise {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases' hx : x ∈ s <;> simp [hx]

theorem apply_piecewise₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x :=
  by
  by_cases' hx : x ∈ s <;> simp [hx]

theorem piecewise_op {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun x => (apply_piecewise _ _ _ _).symm

theorem piecewise_op₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun x => (apply_piecewise₂ _ _ _ _ _ _).symm

@[simp]
theorem piecewise_same : s.piecewise f f = f := by
  ext x
  by_cases' hx : x ∈ s <;> simp [hx]

theorem range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases' h : x ∈ s <;> [left, right] <;> use x <;> simp [h]
    
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
    

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (y «expr ∉ » s)
theorem injective_piecewise_iff {f g : α → β} :
    injective (s.piecewise f g) ↔ inj_on f s ∧ inj_on g (sᶜ) ∧ ∀, ∀ x ∈ s, ∀ y _ : y ∉ s, f x ≠ g y := by
  rw [injective_iff_inj_on_univ, ← union_compl_self s, inj_on_union (@disjoint_compl_right _ s _),
    (piecewise_eq_on s f g).inj_on_iff, (piecewise_eq_on_compl s f g).inj_on_iff]
  refine' and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congrₓ fun x hx y hy => _)
  rw [piecewise_eq_of_mem s f g hx, piecewise_eq_of_not_mem s f g hy]

theorem piecewise_mem_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ pi t t')
    (hg : g ∈ pi t t') : s.piecewise f g ∈ pi t t' := by
  intro i ht
  by_cases' hs : i ∈ s <;> simp [hf i ht, hg i ht, hs]

@[simp]
theorem pi_piecewise {ι : Type _} {α : ι → Type _} (s s' : Set ι) (t t' : ∀ i, Set (α i)) [∀ x, Decidable (x ∈ s')] :
    pi s (s'.piecewise t t') = pi (s ∩ s') t ∩ pi (s \ s') t' := by
  ext x
  simp only [mem_pi, mem_inter_eq, ← forall_and_distrib]
  refine' forall_congrₓ fun i => _
  by_cases' hi : i ∈ s' <;> simp [*]

theorem univ_pi_piecewise {ι : Type _} {α : ι → Type _} (s : Set ι) (t : ∀ i, Set (α i)) [∀ x, Decidable (x ∈ s)] :
    pi univ (s.piecewise t fun _ => univ) = pi s t := by
  simp

end Set

theorem StrictMonoOn.inj_on [LinearOrderₓ α] [Preorderₓ β] {f : α → β} {s : Set α} (H : StrictMonoOn f s) :
    s.inj_on f := fun x hx y hy hxy => show Ordering.eq.Compares x y from (H.compares hx hy).1 hxy

theorem StrictAntiOn.inj_on [LinearOrderₓ α] [Preorderₓ β] {f : α → β} {s : Set α} (H : StrictAntiOn f s) :
    s.inj_on f :=
  @StrictMonoOn.inj_on α (OrderDual β) _ _ f s H

theorem StrictMonoOn.comp [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α} {t : Set β}
    (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) : StrictMonoOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy

theorem StrictMonoOn.comp_strict_anti_on [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictMonoOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy

theorem StrictAntiOn.comp [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α} {t : Set β}
    (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) : StrictMonoOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy

theorem StrictAntiOn.comp_strict_mono_on [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictAntiOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy

theorem StrictMono.cod_restrict [Preorderₓ α] [Preorderₓ β] {f : α → β} (hf : StrictMono f) {s : Set β}
    (hs : ∀ x, f x ∈ s) : StrictMono (Set.codRestrict f s hs) :=
  hf

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

theorem injective.comp_inj_on (hg : injective g) (hf : s.inj_on f) : s.inj_on (g ∘ f) :=
  (hg.inj_on univ).comp hf (maps_to_univ _ _)

theorem surjective.surj_on (hf : surjective f) (s : Set β) : surj_on f univ s :=
  (surjective_iff_surj_on_univ.1 hf).mono (subset.refl _) (subset_univ _)

theorem left_inverse.left_inv_on {g : β → α} (h : left_inverse f g) (s : Set β) : left_inv_on f g s := fun x hx => h x

theorem right_inverse.right_inv_on {g : β → α} (h : RightInverse f g) (s : Set α) : right_inv_on f g s := fun x hx =>
  h x

theorem left_inverse.right_inv_on_range {g : β → α} (h : left_inverse f g) : right_inv_on f g (range g) :=
  forall_range_iff.2 fun i => congr_argₓ g (h i)

namespace Semiconj

theorem maps_to_image (h : semiconj f fa fb) (ha : maps_to fa s t) : maps_to fb (f '' s) (f '' t) :=
  fun y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩

theorem maps_to_range (h : semiconj f fa fb) : maps_to fb (range f) (range f) := fun y ⟨x, hy⟩ => hy ▸ ⟨fa x, h x⟩

theorem surj_on_image (h : semiconj f fa fb) (ha : surj_on fa s t) : surj_on fb (f '' s) (f '' t) := by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)

theorem surj_on_range (h : semiconj f fa fb) (ha : surjective fa) : surj_on fb (range f) (range f) := by
  rw [← image_univ]
  exact h.surj_on_image (ha.surj_on univ)

theorem inj_on_image (h : semiconj f fa fb) (ha : inj_on fa s) (hf : inj_on f (fa '' s)) : inj_on fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_argₓ f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)

theorem inj_on_range (h : semiconj f fa fb) (ha : injective fa) (hf : inj_on f (range fa)) : inj_on fb (range f) := by
  rw [← image_univ] at *
  exact h.inj_on_image (ha.inj_on univ) hf

theorem bij_on_image (h : semiconj f fa fb) (ha : bij_on fa s t) (hf : inj_on f t) : bij_on fb (f '' s) (f '' t) :=
  ⟨h.maps_to_image ha.maps_to, h.inj_on_image ha.inj_on (ha.image_eq.symm ▸ hf), h.surj_on_image ha.surj_on⟩

theorem bij_on_range (h : semiconj f fa fb) (ha : bijective fa) (hf : injective f) : bij_on fb (range f) (range f) := by
  rw [← image_univ]
  exact h.bij_on_image (bijective_iff_bij_on_univ.1 ha) (hf.inj_on univ)

theorem maps_to_preimage (h : semiconj f fa fb) {s t : Set β} (hb : maps_to fb s t) : maps_to fa (f ⁻¹' s) (f ⁻¹' t) :=
  fun x hx => by
  simp only [mem_preimage, h x, hb hx]

theorem inj_on_preimage (h : semiconj f fa fb) {s : Set β} (hb : inj_on fb s) (hf : inj_on f (f ⁻¹' s)) :
    inj_on fa (f ⁻¹' s) := by
  intro x hx y hy H
  have := congr_argₓ f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)

end Semiconj

theorem update_comp_eq_of_not_mem_range' {α β : Sort _} {γ : β → Sort _} [DecidableEq β] (g : ∀ b, γ b) {f : α → β}
    {i : β} (a : γ i) (h : i ∉ Set.Range f) : (fun j => (Function.update g i a) (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩

/-- Non-dependent version of `function.update_comp_eq_of_not_mem_range'` -/
theorem update_comp_eq_of_not_mem_range {α β γ : Sort _} [DecidableEq β] (g : β → γ) {f : α → β} {i : β} (a : γ)
    (h : i ∉ Set.Range f) : Function.update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_not_mem_range' g a h

end Function

