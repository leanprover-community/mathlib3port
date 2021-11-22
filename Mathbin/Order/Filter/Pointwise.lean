import Mathbin.Algebra.Pointwise 
import Mathbin.Order.Filter.Basic

/-!
# Pointwise operations on filters.

The pointwise operations on filters have nice properties, such as
  • `map m (f₁ * f₂) = map m f₁ * map m f₂`
  • `𝓝 x * 𝓝 y = 𝓝 (x * y)`

-/


open Classical Set

universe u v w

variable{α : Type u}{β : Type v}{γ : Type w}

open_locale Classical Pointwise

namespace Filter

open Set

@[toAdditive]
instance  [HasOne α] : HasOne (Filter α) :=
  ⟨principal 1⟩

@[simp, toAdditive]
theorem mem_one [HasOne α] (s : Set α) : s ∈ (1 : Filter α) ↔ (1 : α) ∈ s :=
  calc s ∈ (1 : Filter α) ↔ 1 ⊆ s := Iff.rfl 
    _ ↔ (1 : α) ∈ s :=
    by 
      simp 
    

@[toAdditive]
instance  [Monoidₓ α] : Mul (Filter α) :=
  ⟨fun f g =>
      { Sets := { s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ (t₁*t₂) ⊆ s },
        univ_sets :=
          by 
            have h₁ : ∃ x, x ∈ f := ⟨univ, univ_sets f⟩
            have h₂ : ∃ x, x ∈ g := ⟨univ, univ_sets g⟩
            simpa using And.intro h₁ h₂,
        sets_of_superset :=
          fun x y hx hxy =>
            by 
              rcases hx with ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩
              exact ⟨t₁, ht₁, t₂, ht₂, subset.trans t₁t₂ hxy⟩,
        inter_sets :=
          fun x y =>
            by 
              simp only [exists_prop, mem_set_of_eq, subset_inter_iff]
              rintro ⟨s₁, s₂, hs₁, hs₂, s₁s₂⟩ ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩
              exact
                ⟨s₁ ∩ t₁, s₂ ∩ t₂, inter_sets f hs₁ ht₁, inter_sets g hs₂ ht₂,
                  subset.trans (mul_subset_mul (inter_subset_left _ _) (inter_subset_left _ _)) s₁s₂,
                  subset.trans (mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _)) t₁t₂⟩ }⟩

@[toAdditive]
theorem mem_mul [Monoidₓ α] {f g : Filter α} {s : Set α} : (s ∈ f*g) ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ (t₁*t₂) ⊆ s :=
  Iff.rfl

@[toAdditive]
theorem mul_mem_mul [Monoidₓ α] {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : (s*t) ∈ f*g :=
  ⟨_, _, hs, ht, subset.refl _⟩

@[toAdditive]
protected theorem mul_le_mul [Monoidₓ α] {f₁ f₂ g₁ g₂ : Filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : (f₁*g₁) ≤ f₂*g₂ :=
  fun _ ⟨s, t, hs, ht, hst⟩ => ⟨s, t, hf hs, hg ht, hst⟩

@[toAdditive]
theorem ne_bot.mul [Monoidₓ α] {f g : Filter α} : ne_bot f → ne_bot g → ne_bot (f*g) :=
  by 
    simp only [forall_mem_nonempty_iff_ne_bot.symm]
    rintro hf hg s ⟨a, b, ha, hb, ab⟩
    exact ((hf a ha).mul (hg b hb)).mono ab

@[toAdditive]
protected theorem mul_assocₓ [Monoidₓ α] (f g h : Filter α) : ((f*g)*h) = f*g*h :=
  by 
    ext s 
    split 
    ·
      rintro ⟨a, b, ⟨a₁, a₂, ha₁, ha₂, a₁a₂⟩, hb, ab⟩
      refine' ⟨a₁, a₂*b, ha₁, mul_mem_mul ha₂ hb, _⟩
      rw [←mul_assocₓ]
      calc ((a₁*a₂)*b) ⊆ a*b := mul_subset_mul a₁a₂ (subset.refl _)_ ⊆ s := ab
    ·
      rintro ⟨a, b, ha, ⟨b₁, b₂, hb₁, hb₂, b₁b₂⟩, ab⟩
      refine' ⟨a*b₁, b₂, mul_mem_mul ha hb₁, hb₂, _⟩
      rw [mul_assocₓ]
      calc (a*b₁*b₂) ⊆ a*b := mul_subset_mul (subset.refl _) b₁b₂ _ ⊆ s := ab

@[toAdditive]
protected theorem one_mulₓ [Monoidₓ α] (f : Filter α) : (1*f) = f :=
  by 
    ext s 
    split 
    ·
      rintro ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩
      refine' mem_of_superset (mem_of_superset ht₂ _) t₁t₂ 
      intro x hx 
      exact
        ⟨1, x,
          by 
            rwa [←mem_one],
          hx, one_mulₓ _⟩
    ·
      intro hs 
      refine'
        ⟨(1 : Set α), s, mem_principal_self _, hs,
          by 
            simp only [one_mulₓ]⟩

@[toAdditive]
protected theorem mul_oneₓ [Monoidₓ α] (f : Filter α) : (f*1) = f :=
  by 
    ext s 
    split 
    ·
      rintro ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩
      refine' mem_of_superset (mem_of_superset ht₁ _) t₁t₂ 
      intro x hx 
      exact
        ⟨x, 1, hx,
          by 
            rwa [←mem_one],
          mul_oneₓ _⟩
    ·
      intro hs 
      refine'
        ⟨s, (1 : Set α), hs, mem_principal_self _,
          by 
            simp only [mul_oneₓ]⟩

@[toAdditive Filter.addMonoid]
instance  [Monoidₓ α] : Monoidₓ (Filter α) :=
  { Filter.hasMul, Filter.hasOne with mul_assoc := Filter.mul_assoc, one_mul := Filter.one_mul,
    mul_one := Filter.mul_one }

section Map

variable[Monoidₓ α][Monoidₓ β]{f : Filter α}(m : MulHom α β)(φ : α →* β)

@[toAdditive]
protected theorem map_mul {f₁ f₂ : Filter α} : map m (f₁*f₂) = map m f₁*map m f₂ :=
  by 
    ext s 
    simp only [mem_mul]
    split 
    ·
      rintro ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩
      have  : (m '' t₁*t₂) ⊆ s := subset.trans (image_subset m t₁t₂) (image_preimage_subset _ _)
      refine' ⟨m '' t₁, m '' t₂, image_mem_map ht₁, image_mem_map ht₂, _⟩
      rwa [←image_mul m]
    ·
      rintro ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩
      refine' ⟨m ⁻¹' t₁, m ⁻¹' t₂, ht₁, ht₂, image_subset_iff.1 _⟩
      rw [image_mul m]
      exact subset.trans (mul_subset_mul (image_preimage_subset _ _) (image_preimage_subset _ _)) t₁t₂

@[toAdditive]
protected theorem map_one : map φ (1 : Filter α) = 1 :=
  le_antisymmₓ
    (le_principal_iff.2$
      mem_map_iff_exists_image.2
        ⟨(1 : Set α),
          by 
            simp ,
          by 
            intro x 
            simp [φ.map_one]⟩)
    (le_map$
      fun s hs =>
        by 
          simp only [mem_one]
          exact ⟨(1 : α), (mem_one s).1 hs, φ.map_one⟩)

/-- If `φ : α →* β` then `map_monoid_hom φ` is the monoid homomorphism
`filter α →* filter β` induced by `map φ`. -/
@[toAdditive
      "If `φ : α →+ β` then `map_add_monoid_hom φ` is the monoid homomorphism\n`filter α →+ filter β` induced by `map φ`."]
def map_monoid_hom : Filter α →* Filter β :=
  { toFun := map φ, map_one' := Filter.map_one φ, map_mul' := fun _ _ => Filter.map_mul φ.to_mul_hom }

@[toAdditive]
theorem comap_mul_comap_le {f₁ f₂ : Filter β} : (comap m f₁*comap m f₂) ≤ comap m (f₁*f₂) :=
  by 
    rintro s ⟨t, ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩, mt⟩
    refine' ⟨m ⁻¹' t₁, m ⁻¹' t₂, ⟨t₁, ht₁, subset.refl _⟩, ⟨t₂, ht₂, subset.refl _⟩, _⟩
    have  := subset.trans (preimage_mono t₁t₂) mt 
    exact subset.trans (preimage_mul_preimage_subset _) this

@[toAdditive]
theorem tendsto.mul_mul {f₁ g₁ : Filter α} {f₂ g₂ : Filter β} :
  tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁*g₁) (f₂*g₂) :=
  fun hf hg =>
    by 
      rw [tendsto, Filter.map_mul m]
      exact Filter.mul_le_mul hf hg

end Map

end Filter

