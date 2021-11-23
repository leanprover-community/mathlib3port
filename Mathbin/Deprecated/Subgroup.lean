import Mathbin.GroupTheory.Subgroup.Basic 
import Mathbin.Deprecated.Submonoid

/-!
# Unbundled subgroups

This file defines unbundled multiplicative and additive subgroups `is_subgroup` and
`is_add_subgroup`. These are not the preferred way to talk about subgroups and should
not be used for any new projects. The preferred way in mathlib are the bundled
versions `subgroup G` and `add_subgroup G`.

## Main definitions

`is_add_subgroup (S : set G)` : the predicate that `S` is the underlying subset of an additive
subgroup of `G`. The bundled variant `add_subgroup G` should be used in preference to this.

`is_subgroup (S : set G)` : the predicate that `S` is the underlying subset of a subgroup
of `G`. The bundled variant `subgroup G` should be used in preference to this.

## Tags

subgroup, subgroups, is_subgroup
-/


open Set Function

variable{G : Type _}{H : Type _}{A : Type _}{a a₁ a₂ b c : G}

section Groupₓ

variable[Groupₓ G][AddGroupₓ A]

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
structure IsAddSubgroup(s : Set A) extends IsAddSubmonoid s : Prop where 
  neg_mem {a} : a ∈ s → -a ∈ s

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
@[toAdditive]
structure IsSubgroup(s : Set G) extends IsSubmonoid s : Prop where 
  inv_mem {a} : a ∈ s → a⁻¹ ∈ s

@[toAdditive]
theorem IsSubgroup.div_mem {s : Set G} (hs : IsSubgroup s) {x y : G} (hx : x ∈ s) (hy : y ∈ s) : x / y ∈ s :=
  by 
    simpa only [div_eq_mul_inv] using hs.mul_mem hx (hs.inv_mem hy)

theorem Additive.is_add_subgroup {s : Set G} (hs : IsSubgroup s) : @IsAddSubgroup (Additive G) _ s :=
  @IsAddSubgroup.mk (Additive G) _ _ (Additive.is_add_submonoid hs.to_is_submonoid) hs.inv_mem

theorem Additive.is_add_subgroup_iff {s : Set G} : @IsAddSubgroup (Additive G) _ s ↔ IsSubgroup s :=
  ⟨by 
      rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact @IsSubgroup.mk G _ _ ⟨h₁, @h₂⟩ @h₃,
    fun h =>
      by 
        exact Additive.is_add_subgroup h⟩

theorem Multiplicative.is_subgroup {s : Set A} (hs : IsAddSubgroup s) : @IsSubgroup (Multiplicative A) _ s :=
  @IsSubgroup.mk (Multiplicative A) _ _ (Multiplicative.is_submonoid hs.to_is_add_submonoid) hs.neg_mem

theorem Multiplicative.is_subgroup_iff {s : Set A} : @IsSubgroup (Multiplicative A) _ s ↔ IsAddSubgroup s :=
  ⟨by 
      rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact @IsAddSubgroup.mk A _ _ ⟨h₁, @h₂⟩ @h₃,
    fun h =>
      by 
        exact Multiplicative.is_subgroup h⟩

@[toAdditive of_add_neg]
theorem IsSubgroup.of_div (s : Set G) (one_mem : (1 : G) ∈ s) (div_mem : ∀ {a b : G}, a ∈ s → b ∈ s → (a*b⁻¹) ∈ s) :
  IsSubgroup s :=
  have inv_mem : ∀ a, a ∈ s → a⁻¹ ∈ s :=
    fun a ha =>
      have  : (1*a⁻¹) ∈ s := div_mem one_mem ha 
      by 
        simpa
  { inv_mem,
    mul_mem :=
      fun a b ha hb =>
        have  : (a*b⁻¹⁻¹) ∈ s := div_mem ha (inv_mem b hb)
        by 
          simpa,
    one_mem }

theorem IsAddSubgroup.of_sub (s : Set A) (zero_mem : (0 : A) ∈ s) (sub_mem : ∀ {a b : A}, a ∈ s → b ∈ s → a - b ∈ s) :
  IsAddSubgroup s :=
  IsAddSubgroup.of_add_neg s zero_mem
    fun x y hx hy =>
      by 
        simpa only [sub_eq_add_neg] using sub_mem hx hy

@[toAdditive]
theorem IsSubgroup.inter {s₁ s₂ : Set G} (hs₁ : IsSubgroup s₁) (hs₂ : IsSubgroup s₂) : IsSubgroup (s₁ ∩ s₂) :=
  { IsSubmonoid.inter hs₁.to_is_submonoid hs₂.to_is_submonoid with
    inv_mem := fun x hx => ⟨hs₁.inv_mem hx.1, hs₂.inv_mem hx.2⟩ }

@[toAdditive]
theorem IsSubgroup.Inter {ι : Sort _} {s : ι → Set G} (hs : ∀ y : ι, IsSubgroup (s y)) : IsSubgroup (Set.Interₓ s) :=
  { IsSubmonoid.Inter fun y => (hs y).to_is_submonoid with
    inv_mem := fun x h => Set.mem_Inter.2$ fun y => IsSubgroup.inv_mem (hs _) (Set.mem_Inter.1 h y) }

@[toAdditive]
theorem is_subgroup_Union_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set G} (hs : ∀ i, IsSubgroup (s i))
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) : IsSubgroup (⋃i, s i) :=
  { inv_mem :=
      fun a ha =>
        let ⟨i, hi⟩ := Set.mem_Union.1 ha 
        Set.mem_Union.2 ⟨i, (hs i).inv_mem hi⟩,
    to_is_submonoid := is_submonoid_Union_of_directed (fun i => (hs i).to_is_submonoid) Directed }

end Groupₓ

namespace IsSubgroup

open IsSubmonoid

variable[Groupₓ G]{s : Set G}(hs : IsSubgroup s)

include hs

@[toAdditive]
theorem inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
  ⟨fun h =>
      by 
        simpa using hs.inv_mem h,
    inv_mem hs⟩

@[toAdditive]
theorem mul_mem_cancel_right (h : a ∈ s) : (b*a) ∈ s ↔ b ∈ s :=
  ⟨fun hba =>
      by 
        simpa using hs.mul_mem hba (hs.inv_mem h),
    fun hb => hs.mul_mem hb h⟩

@[toAdditive]
theorem mul_mem_cancel_left (h : a ∈ s) : (a*b) ∈ s ↔ b ∈ s :=
  ⟨fun hab =>
      by 
        simpa using hs.mul_mem (hs.inv_mem h) hab,
    hs.mul_mem h⟩

end IsSubgroup

/-- `is_normal_add_subgroup (s : set A)` expresses the fact that `s` is a normal additive subgroup
of the additive group `A`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : add_subgroup A` and `hs : S.normal`, and not via this structure. -/
structure IsNormalAddSubgroup[AddGroupₓ A](s : Set A) extends IsAddSubgroup s : Prop where 
  Normal : ∀ n _ : n ∈ s, ∀ g : A, ((g+n)+-g) ∈ s

/-- `is_normal_subgroup (s : set G)` expresses the fact that `s` is a normal subgroup
of the group `G`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : subgroup G` and not via this structure. -/
@[toAdditive]
structure IsNormalSubgroup[Groupₓ G](s : Set G) extends IsSubgroup s : Prop where 
  Normal : ∀ n _ : n ∈ s, ∀ g : G, ((g*n)*g⁻¹) ∈ s

@[toAdditive]
theorem is_normal_subgroup_of_comm_group [CommGroupₓ G] {s : Set G} (hs : IsSubgroup s) : IsNormalSubgroup s :=
  { hs with
    Normal :=
      fun n hn g =>
        by 
          rwa [mul_right_commₓ, mul_right_invₓ, one_mulₓ] }

theorem Additive.is_normal_add_subgroup [Groupₓ G] {s : Set G} (hs : IsNormalSubgroup s) :
  @IsNormalAddSubgroup (Additive G) _ s :=
  @IsNormalAddSubgroup.mk (Additive G) _ _ (Additive.is_add_subgroup hs.to_is_subgroup) (IsNormalSubgroup.normal hs)

theorem Additive.is_normal_add_subgroup_iff [Groupₓ G] {s : Set G} :
  @IsNormalAddSubgroup (Additive G) _ s ↔ IsNormalSubgroup s :=
  ⟨by 
      rintro ⟨h₁, h₂⟩ <;> exact @IsNormalSubgroup.mk G _ _ (Additive.is_add_subgroup_iff.1 h₁) @h₂,
    fun h =>
      by 
        exact Additive.is_normal_add_subgroup h⟩

theorem Multiplicative.is_normal_subgroup [AddGroupₓ A] {s : Set A} (hs : IsNormalAddSubgroup s) :
  @IsNormalSubgroup (Multiplicative A) _ s :=
  @IsNormalSubgroup.mk (Multiplicative A) _ _ (Multiplicative.is_subgroup hs.to_is_add_subgroup)
    (IsNormalAddSubgroup.normal hs)

theorem Multiplicative.is_normal_subgroup_iff [AddGroupₓ A] {s : Set A} :
  @IsNormalSubgroup (Multiplicative A) _ s ↔ IsNormalAddSubgroup s :=
  ⟨by 
      rintro ⟨h₁, h₂⟩ <;> exact @IsNormalAddSubgroup.mk A _ _ (Multiplicative.is_subgroup_iff.1 h₁) @h₂,
    fun h =>
      by 
        exact Multiplicative.is_normal_subgroup h⟩

namespace IsSubgroup

variable[Groupₓ G]

@[toAdditive]
theorem mem_norm_comm {s : Set G} (hs : IsNormalSubgroup s) {a b : G} (hab : (a*b) ∈ s) : (b*a) ∈ s :=
  have h : ((a⁻¹*a*b)*a⁻¹⁻¹) ∈ s := hs.normal (a*b) hab (a⁻¹)
  by 
    simp  at h <;> exact h

@[toAdditive]
theorem mem_norm_comm_iff {s : Set G} (hs : IsNormalSubgroup s) {a b : G} : (a*b) ∈ s ↔ (b*a) ∈ s :=
  ⟨mem_norm_comm hs, mem_norm_comm hs⟩

/-- The trivial subgroup -/
@[toAdditive "the trivial additive subgroup"]
def trivialₓ (G : Type _) [Groupₓ G] : Set G :=
  {1}

@[simp, toAdditive]
theorem mem_trivial {g : G} : g ∈ trivialₓ G ↔ g = 1 :=
  mem_singleton_iff

-- error in Deprecated.Subgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]] theorem trivial_normal : is_normal_subgroup (trivial G) :=
by refine [expr { .. }]; simp [] [] [] ["[", expr trivial, "]"] [] [] { contextual := tt }

@[toAdditive]
theorem eq_trivial_iff {s : Set G} (hs : IsSubgroup s) : s = trivialₓ G ↔ ∀ x _ : x ∈ s, x = (1 : G) :=
  by 
    simp only [Set.ext_iff, IsSubgroup.mem_trivial] <;>
      exact ⟨fun h x => (h x).1, fun h x => ⟨h x, fun hx => hx.symm ▸ hs.to_is_submonoid.one_mem⟩⟩

@[toAdditive]
theorem univ_subgroup : IsNormalSubgroup (@univ G) :=
  by 
    refine' { .. } <;> simp 

/-- The underlying set of the center of a group. -/
@[toAdditive add_center "The underlying set of the center of an additive group."]
def center (G : Type _) [Groupₓ G] : Set G :=
  { z | ∀ g, (g*z) = z*g }

@[toAdditive mem_add_center]
theorem mem_center {a : G} : a ∈ center G ↔ ∀ g, (g*a) = a*g :=
  Iff.rfl

@[toAdditive add_center_normal]
theorem center_normal : IsNormalSubgroup (center G) :=
  { one_mem :=
      by 
        simp [center],
    mul_mem :=
      fun a b ha hb g =>
        by 
          rw [←mul_assocₓ, mem_center.2 ha g, mul_assocₓ, mem_center.2 hb g, ←mul_assocₓ],
    inv_mem :=
      fun a ha g =>
        calc (g*a⁻¹) = (a⁻¹*g*a)*a⁻¹ :=
          by 
            simp [ha g]
          _ = a⁻¹*g :=
          by 
            rw [←mul_assocₓ, mul_assocₓ] <;> simp 
          ,
    Normal :=
      fun n ha g h =>
        calc (h*(g*n)*g⁻¹) = h*n :=
          by 
            simp [ha g, mul_assocₓ]
          _ = ((g*g⁻¹)*n)*h :=
          by 
            rw [ha h] <;> simp 
          _ = ((g*n)*g⁻¹)*h :=
          by 
            rw [mul_assocₓ g, ha (g⁻¹), ←mul_assocₓ]
           }

/-- The underlying set of the normalizer of a subset `S : set G` of a group `G`. That is,
  the elements `g : G` such that `g * S * g⁻¹ = S`. -/
@[toAdditive add_normalizer
      "The underlying set of the normalizer of a subset `S : set A` of an\n  additive group `A`. That is, the elements `a : A` such that `a + S - a = S`."]
def normalizer (s : Set G) : Set G :=
  { g:G | ∀ n, n ∈ s ↔ ((g*n)*g⁻¹) ∈ s }

@[toAdditive]
theorem normalizer_is_subgroup (s : Set G) : IsSubgroup (normalizer s) :=
  { one_mem :=
      by 
        simp [normalizer],
    mul_mem :=
      fun a b ha : ∀ n, n ∈ s ↔ ((a*n)*a⁻¹) ∈ s hb : ∀ n, n ∈ s ↔ ((b*n)*b⁻¹) ∈ s n =>
        by 
          rw [mul_inv_rev, ←mul_assocₓ, mul_assocₓ a, mul_assocₓ a, ←ha, ←hb],
    inv_mem :=
      fun a ha : ∀ n, n ∈ s ↔ ((a*n)*a⁻¹) ∈ s n =>
        by 
          rw [ha ((a⁻¹*n)*a⁻¹⁻¹)] <;> simp [mul_assocₓ] }

@[toAdditive subset_add_normalizer]
theorem subset_normalizer {s : Set G} (hs : IsSubgroup s) : s ⊆ normalizer s :=
  fun g hg n =>
    by 
      rw [IsSubgroup.mul_mem_cancel_right hs ((IsSubgroup.inv_mem_iff hs).2 hg), IsSubgroup.mul_mem_cancel_left hs hg]

end IsSubgroup

namespace IsGroupHom

open IsSubmonoid IsSubgroup

open is_mul_hom(map_mul)

/-- `ker f : set G` is the underlying subset of the kernel of a map `G → H`. -/
@[toAdditive "`ker f : set A` is the underlying subset of the kernel of a map `A → B`"]
def ker [Groupₓ H] (f : G → H) : Set G :=
  preimage f (trivialₓ H)

@[toAdditive]
theorem mem_ker [Groupₓ H] (f : G → H) {x : G} : x ∈ ker f ↔ f x = 1 :=
  mem_trivial

variable[Groupₓ G][Groupₓ H]

@[toAdditive]
theorem one_ker_inv {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a*b⁻¹) = 1) : f a = f b :=
  by 
    rw [hf.map_mul, hf.map_inv] at h 
    rw [←inv_invₓ (f b), eq_inv_of_mul_eq_one h]

@[toAdditive]
theorem one_ker_inv' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a⁻¹*b) = 1) : f a = f b :=
  by 
    rw [hf.map_mul, hf.map_inv] at h 
    apply inv_injective 
    rw [eq_inv_of_mul_eq_one h]

@[toAdditive]
theorem inv_ker_one {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) : f (a*b⁻¹) = 1 :=
  have  : (f a*f b⁻¹) = 1 :=
    by 
      rw [h, mul_right_invₓ]
  by 
    rwa [←hf.map_inv, ←hf.map_mul] at this

@[toAdditive]
theorem inv_ker_one' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) : f (a⁻¹*b) = 1 :=
  have  : (f a⁻¹*f b) = 1 :=
    by 
      rw [h, mul_left_invₓ]
  by 
    rwa [←hf.map_inv, ←hf.map_mul] at this

@[toAdditive]
theorem one_iff_ker_inv {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a*b⁻¹) = 1 :=
  ⟨hf.inv_ker_one, hf.one_ker_inv⟩

@[toAdditive]
theorem one_iff_ker_inv' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a⁻¹*b) = 1 :=
  ⟨hf.inv_ker_one', hf.one_ker_inv'⟩

@[toAdditive]
theorem inv_iff_ker {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ (a*b⁻¹) ∈ ker f :=
  by 
    rw [mem_ker] <;> exact one_iff_ker_inv hf _ _

@[toAdditive]
theorem inv_iff_ker' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ (a⁻¹*b) ∈ ker f :=
  by 
    rw [mem_ker] <;> exact one_iff_ker_inv' hf _ _

@[toAdditive]
theorem image_subgroup {f : G → H} (hf : IsGroupHom f) {s : Set G} (hs : IsSubgroup s) : IsSubgroup (f '' s) :=
  { mul_mem :=
      fun a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩ =>
        ⟨b₁*b₂, hs.mul_mem hb₁ hb₂,
          by 
            simp [eq₁, eq₂, hf.map_mul]⟩,
    one_mem := ⟨1, hs.to_is_submonoid.one_mem, hf.map_one⟩,
    inv_mem :=
      fun a ⟨b, hb, Eq⟩ =>
        ⟨b⁻¹, hs.inv_mem hb,
          by 
            rw [hf.map_inv]
            simp ⟩ }

@[toAdditive]
theorem range_subgroup {f : G → H} (hf : IsGroupHom f) : IsSubgroup (Set.Range f) :=
  @Set.image_univ _ _ f ▸ hf.image_subgroup univ_subgroup.to_is_subgroup

attribute [local simp] one_mem inv_mem mul_mem IsNormalSubgroup.normal

-- error in Deprecated.Subgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem preimage {f : G → H} (hf : is_group_hom f) {s : set H} (hs : is_subgroup s) : is_subgroup «expr ⁻¹' »(f, s) :=
by { refine [expr { .. }]; simp [] [] [] ["[", expr hs.one_mem, ",", expr hs.mul_mem, ",", expr hs.inv_mem, ",", expr hf.map_mul, ",", expr hf.map_one, ",", expr hf.map_inv, ",", expr @inv_mem H _ s, "]"] [] [] { contextual := tt } }

-- error in Deprecated.Subgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem preimage_normal
{f : G → H}
(hf : is_group_hom f)
{s : set H}
(hs : is_normal_subgroup s) : is_normal_subgroup «expr ⁻¹' »(f, s) :=
{ one_mem := by simp [] [] [] ["[", expr hf.map_one, ",", expr hs.to_is_subgroup.one_mem, "]"] [] [],
  mul_mem := by simp [] [] [] ["[", expr hf.map_mul, ",", expr hs.to_is_subgroup.mul_mem, "]"] [] [] { contextual := tt },
  inv_mem := by simp [] [] [] ["[", expr hf.map_inv, ",", expr hs.to_is_subgroup.inv_mem, "]"] [] [] { contextual := tt },
  normal := by simp [] [] [] ["[", expr hs.normal, ",", expr hf.map_mul, ",", expr hf.map_inv, "]"] [] [] { contextual := tt } }

@[toAdditive]
theorem is_normal_subgroup_ker {f : G → H} (hf : IsGroupHom f) : IsNormalSubgroup (ker f) :=
  hf.preimage_normal trivial_normal

-- error in Deprecated.Subgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem injective_of_trivial_ker
{f : G → H}
(hf : is_group_hom f)
(h : «expr = »(ker f, trivial G)) : function.injective f :=
begin
  intros [ident a₁, ident a₂, ident hfa],
  simp [] [] [] ["[", expr ext_iff, ",", expr ker, ",", expr is_subgroup.trivial, "]"] [] ["at", ident h],
  have [ident ha] [":", expr «expr = »(«expr * »(a₁, «expr ⁻¹»(a₂)), 1)] [],
  by rw ["<-", expr h] []; exact [expr hf.inv_ker_one hfa],
  rw ["[", expr eq_inv_of_mul_eq_one ha, ",", expr inv_inv a₂, "]"] []
end

-- error in Deprecated.Subgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem trivial_ker_of_injective
{f : G → H}
(hf : is_group_hom f)
(h : function.injective f) : «expr = »(ker f, trivial G) :=
«expr $ »(set.ext, assume
 x, iff.intro (assume hx, suffices «expr = »(f x, f 1), by simpa [] [] [] [] [] ["using", expr h this],
  by simp [] [] [] ["[", expr hf.map_one, "]"] [] []; rwa ["[", expr mem_ker, "]"] ["at", ident hx]) (by simp [] [] [] ["[", expr mem_ker, ",", expr hf.map_one, "]"] [] [] { contextual := tt }))

@[toAdditive]
theorem injective_iff_trivial_ker {f : G → H} (hf : IsGroupHom f) : Function.Injective f ↔ ker f = trivialₓ G :=
  ⟨hf.trivial_ker_of_injective, hf.injective_of_trivial_ker⟩

@[toAdditive]
theorem trivial_ker_iff_eq_one {f : G → H} (hf : IsGroupHom f) : ker f = trivialₓ G ↔ ∀ x, f x = 1 → x = 1 :=
  by 
    rw [Set.ext_iff] <;>
      simp [ker] <;>
        exact
          ⟨fun h x hx => (h x).1 hx,
            fun h x =>
              ⟨h x,
                fun hx =>
                  by 
                    rw [hx, hf.map_one]⟩⟩

end IsGroupHom

namespace AddGroupₓ

variable[AddGroupₓ A]

/-- If `A` is an additive group and `s : set A`, then `in_closure s : set A` is the underlying
subset of the subgroup generated by `s`. -/
inductive in_closure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → in_closure a
  | zero : in_closure 0
  | neg {a : A} : in_closure a → in_closure (-a)
  | add {a b : A} : in_closure a → in_closure b → in_closure (a+b)

end AddGroupₓ

namespace Groupₓ

open IsSubmonoid IsSubgroup

variable[Groupₓ G]{s : Set G}

/-- If `G` is a group and `s : set G`, then `in_closure s : set G` is the underlying
subset of the subgroup generated by `s`. -/
@[toAdditive]
inductive in_closure (s : Set G) : G → Prop
  | basic {a : G} : a ∈ s → in_closure a
  | one : in_closure 1
  | inv {a : G} : in_closure a → in_closure (a⁻¹)
  | mul {a b : G} : in_closure a → in_closure b → in_closure (a*b)

/-- `group.closure s` is the subgroup generated by `s`, i.e. the smallest subgroup containg `s`. -/
@[toAdditive
      "`add_group.closure s` is the additive subgroup generated by `s`, i.e., the\n  smallest additive subgroup containing `s`."]
def closure (s : Set G) : Set G :=
  { a | in_closure s a }

@[toAdditive]
theorem mem_closure {a : G} : a ∈ s → a ∈ closure s :=
  in_closure.basic

@[toAdditive]
theorem closure.is_subgroup (s : Set G) : IsSubgroup (closure s) :=
  { one_mem := in_closure.one, mul_mem := fun a b => in_closure.mul, inv_mem := fun a => in_closure.inv }

@[toAdditive]
theorem subset_closure {s : Set G} : s ⊆ closure s :=
  fun a => mem_closure

@[toAdditive]
theorem closure_subset {s t : Set G} (ht : IsSubgroup t) (h : s ⊆ t) : closure s ⊆ t :=
  fun a ha =>
    by 
      induction ha <;> simp [h _, ht.one_mem, ht.mul_mem, inv_mem_iff]

@[toAdditive]
theorem closure_subset_iff {s t : Set G} (ht : IsSubgroup t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨fun h b ha => h (mem_closure ha), fun h b ha => closure_subset ht h ha⟩

@[toAdditive]
theorem closure_mono {s t : Set G} (h : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset (closure.is_subgroup _)$ Set.Subset.trans h subset_closure

@[simp, toAdditive]
theorem closure_subgroup {s : Set G} (hs : IsSubgroup s) : closure s = s :=
  Set.Subset.antisymm (closure_subset hs$ Set.Subset.refl s) subset_closure

@[toAdditive]
theorem exists_list_of_mem_closure {s : Set G} {a : G} (h : a ∈ closure s) :
  ∃ l : List G, (∀ x _ : x ∈ l, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.prod = a :=
  in_closure.rec_on h (fun x hxs => ⟨[x], List.forall_mem_singleton.2$ Or.inl hxs, one_mulₓ _⟩)
    ⟨[], List.forall_mem_nil _, rfl⟩
    (fun x _ ⟨L, HL1, HL2⟩ =>
      ⟨L.reverse.map HasInv.inv,
        fun x hx =>
          let ⟨y, hy1, hy2⟩ := List.exists_of_mem_mapₓ hx 
          hy2 ▸
            Or.imp id
              (by 
                rw [inv_invₓ] <;> exact id)
              (HL1 _$ List.mem_reverseₓ.1 hy1).symm,
        HL2 ▸
          List.recOn L one_inv.symm
            fun hd tl ih =>
              by 
                rw [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_cons,
                  List.prod_nil, mul_oneₓ, List.prod_cons, mul_inv_rev]⟩)
    fun x y hx hy ⟨L1, HL1, HL2⟩ ⟨L2, HL3, HL4⟩ =>
      ⟨L1 ++ L2, List.forall_mem_appendₓ.2 ⟨HL1, HL3⟩,
        by 
          rw [List.prod_append, HL2, HL4]⟩

-- error in Deprecated.Subgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
@[to_additive #[]]
theorem image_closure
[group H]
{f : G → H}
(hf : is_group_hom f)
(s : set G) : «expr = »(«expr '' »(f, closure s), closure «expr '' »(f, s)) :=
le_antisymm (begin
   rintros ["_", "⟨", ident x, ",", ident hx, ",", ident rfl, "⟩"],
   apply [expr in_closure.rec_on hx]; intros [],
   { solve_by_elim [] [] ["[", expr subset_closure, ",", expr set.mem_image_of_mem, "]"] [] },
   { rw ["[", expr hf.to_is_monoid_hom.map_one, "]"] [],
     apply [expr is_submonoid.one_mem (closure.is_subgroup _).to_is_submonoid] },
   { rw ["[", expr hf.map_inv, "]"] [],
     apply [expr is_subgroup.inv_mem (closure.is_subgroup _)],
     assumption },
   { rw ["[", expr hf.to_is_monoid_hom.map_mul, "]"] [],
     solve_by_elim [] [] ["[", expr is_submonoid.mul_mem (closure.is_subgroup _).to_is_submonoid, "]"] [] }
 end) «expr $ »(closure_subset «expr $ »(hf.image_subgroup, closure.is_subgroup _), set.image_subset _ subset_closure)

@[toAdditive]
theorem mclosure_subset {s : Set G} : Monoidₓ.Closure s ⊆ closure s :=
  Monoidₓ.closure_subset (closure.is_subgroup _).to_is_submonoid$ subset_closure

@[toAdditive]
theorem mclosure_inv_subset {s : Set G} : Monoidₓ.Closure (HasInv.inv ⁻¹' s) ⊆ closure s :=
  Monoidₓ.closure_subset (closure.is_subgroup _).to_is_submonoid$
    fun x hx => inv_invₓ x ▸ ((closure.is_subgroup _).inv_mem$ subset_closure hx)

@[toAdditive]
theorem closure_eq_mclosure {s : Set G} : closure s = Monoidₓ.Closure (s ∪ HasInv.inv ⁻¹' s) :=
  Set.Subset.antisymm
    (@closure_subset _ _ _ (Monoidₓ.Closure (s ∪ HasInv.inv ⁻¹' s))
      { one_mem := (Monoidₓ.Closure.is_submonoid _).one_mem, mul_mem := (Monoidₓ.Closure.is_submonoid _).mul_mem,
        inv_mem :=
          fun x hx =>
            Monoidₓ.InClosure.rec_on hx
              (fun x hx =>
                Or.cases_on hx (fun hx => Monoidₓ.subset_closure$ Or.inr$ show x⁻¹⁻¹ ∈ s from (inv_invₓ x).symm ▸ hx)
                  fun hx => Monoidₓ.subset_closure$ Or.inl hx)
              ((@one_inv G _).symm ▸ IsSubmonoid.one_mem (Monoidₓ.Closure.is_submonoid _))
              fun x y hx hy ihx ihy =>
                (mul_inv_rev x y).symm ▸ IsSubmonoid.mul_mem (Monoidₓ.Closure.is_submonoid _) ihy ihx }
      (Set.Subset.trans (Set.subset_union_left _ _) Monoidₓ.subset_closure))
    (Monoidₓ.closure_subset (closure.is_subgroup _).to_is_submonoid$
      Set.union_subset subset_closure$
        fun x hx => inv_invₓ x ▸ (IsSubgroup.inv_mem (closure.is_subgroup _)$ subset_closure hx))

@[toAdditive]
theorem mem_closure_union_iff {G : Type _} [CommGroupₓ G] {s t : Set G} {x : G} :
  x ∈ closure (s ∪ t) ↔ ∃ (y : _)(_ : y ∈ closure s), ∃ (z : _)(_ : z ∈ closure t), (y*z) = x :=
  by 
    simp only [closure_eq_mclosure, Monoidₓ.mem_closure_union_iff, exists_prop, preimage_union]
    split 
    ·
      rintro ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, rfl⟩
      refine' ⟨_, ⟨_, hys, _, hzs, rfl⟩, _, ⟨_, hyt, _, hzt, rfl⟩, _⟩
      rw [mul_assocₓ, mul_assocₓ, mul_left_commₓ zs]
    ·
      rintro ⟨_, ⟨ys, hys, zs, hzs, rfl⟩, _, ⟨yt, hyt, zt, hzt, rfl⟩, rfl⟩
      refine' ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, _⟩
      rw [mul_assocₓ, mul_assocₓ, mul_left_commₓ yt]

end Groupₓ

namespace IsSubgroup

variable[Groupₓ G]

@[toAdditive]
theorem trivial_eq_closure : trivialₓ G = Groupₓ.Closure ∅ :=
  subset.antisymm
    (by 
      simp [Set.subset_def, (Groupₓ.Closure.is_subgroup _).one_mem])
    (Groupₓ.closure_subset trivial_normal.to_is_subgroup$
      by 
        simp )

end IsSubgroup

namespace Groupₓ

variable{s : Set G}[Groupₓ G]

-- error in Deprecated.Subgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem conjugates_of_subset
{t : set G}
(ht : is_normal_subgroup t)
{a : G}
(h : «expr ∈ »(a, t)) : «expr ⊆ »(conjugates_of a, t) :=
λ x hc, begin
  obtain ["⟨", ident c, ",", ident w, "⟩", ":=", expr is_conj_iff.1 hc],
  have [ident H] [] [":=", expr is_normal_subgroup.normal ht a h c],
  rwa ["<-", expr w] []
end

theorem conjugates_of_set_subset' {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) : conjugates_of_set s ⊆ t :=
  Set.bUnion_subset fun x H => conjugates_of_subset ht (h H)

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def normal_closure (s : Set G) : Set G :=
  closure (conjugates_of_set s)

theorem conjugates_of_set_subset_normal_closure : conjugates_of_set s ⊆ normal_closure s :=
  subset_closure

theorem subset_normal_closure : s ⊆ normal_closure s :=
  Set.Subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure

/-- The normal closure of a set is a subgroup. -/
theorem normal_closure.is_subgroup (s : Set G) : IsSubgroup (normal_closure s) :=
  closure.is_subgroup (conjugates_of_set s)

/-- The normal closure of s is a normal subgroup. -/
theorem normal_closure.is_normal : IsNormalSubgroup (normal_closure s) :=
  { normal_closure.is_subgroup _ with
    Normal :=
      fun n h g =>
        by 
          induction' h with x hx x hx ihx x y hx hy ihx ihy
          ·
            exact conjugates_of_set_subset_normal_closure (conj_mem_conjugates_of_set hx)
          ·
            simpa using (normal_closure.is_subgroup s).one_mem
          ·
            rw [←conj_inv]
            exact (normal_closure.is_subgroup _).inv_mem ihx
          ·
            rw [←conj_mul]
            exact (normal_closure.is_subgroup _).to_is_submonoid.mul_mem ihx ihy }

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normal_closure_subset {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) : normal_closure s ⊆ t :=
  fun a w =>
    by 
      induction' w with x hx x hx ihx x y hx hy ihx ihy
      ·
        exact conjugates_of_set_subset' ht h$ hx
      ·
        exact ht.to_is_subgroup.to_is_submonoid.one_mem
      ·
        exact ht.to_is_subgroup.inv_mem ihx
      ·
        exact ht.to_is_subgroup.to_is_submonoid.mul_mem ihx ihy

theorem normal_closure_subset_iff {s t : Set G} (ht : IsNormalSubgroup t) : s ⊆ t ↔ normal_closure s ⊆ t :=
  ⟨normal_closure_subset ht, Set.Subset.trans subset_normal_closure⟩

theorem normal_closure_mono {s t : Set G} : s ⊆ t → normal_closure s ⊆ normal_closure t :=
  fun h => normal_closure_subset normal_closure.is_normal (Set.Subset.trans h subset_normal_closure)

end Groupₓ

/-- Create a bundled subgroup from a set `s` and `[is_subgroup s]`. -/
@[toAdditive "Create a bundled additive subgroup from a set `s` and `[is_add_subgroup s]`."]
def Subgroup.of [Groupₓ G] {s : Set G} (h : IsSubgroup s) : Subgroup G :=
  { Carrier := s, one_mem' := h.1.1, mul_mem' := h.1.2, inv_mem' := h.2 }

@[toAdditive]
theorem Subgroup.is_subgroup [Groupₓ G] (K : Subgroup G) : IsSubgroup (K : Set G) :=
  { one_mem := K.one_mem', mul_mem := K.mul_mem', inv_mem := K.inv_mem' }

@[toAdditive]
theorem Subgroup.of_normal [Groupₓ G] (s : Set G) (h : IsSubgroup s) (n : IsNormalSubgroup s) :
  Subgroup.Normal (Subgroup.of h) :=
  { conj_mem := n.normal }

