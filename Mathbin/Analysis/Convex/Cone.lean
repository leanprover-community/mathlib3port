/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
import Mathbin.Analysis.Convex.Hull
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Convex cones

In a `𝕜`-module `E`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `complete_lattice`, and define their
images (`convex_cone.map`) and preimages (`convex_cone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We also define `convex.to_cone` to be the minimal cone that includes a given convex set.

We define `set.inner_dual_cone` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`.

## Main statements

We prove two extension theorems:
* `riesz_extension`:
  [M. Riesz extension theorem](https://en.wikipedia.org/wiki/M._Riesz_extension_theorem) says that
  if `s` is a convex cone in a real vector space `E`, `p` is a submodule of `E`
  such that `p + s = E`, and `f` is a linear function `p → ℝ` which is
  nonnegative on `p ∩ s`, then there exists a globally defined linear function
  `g : E → ℝ` that agrees with `f` on `p`, and is nonnegative on `s`.
* `exists_extension_of_le_sublinear`:
  Hahn-Banach theorem: if `N : E → ℝ` is a sublinear map, `f` is a linear map
  defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
  then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
  for all `x`

## Implementation notes

While `convex 𝕜` is a predicate on sets, `convex_cone 𝕜 E` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
-/


open Set LinearMap

open Classical Pointwise

variable {𝕜 E F G : Type _}

/-! ### Definition of `convex_cone` and basic properties -/


section Definitions

variable (𝕜 E) [OrderedSemiring 𝕜]

/-- A convex cone is a subset `s` of a `𝕜`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure ConvexCone [AddCommMonoidₓ E] [HasSmul 𝕜 E] where
  Carrier : Set E
  smul_mem' : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (hx : x ∈ carrier) ⦃y⦄ (hy : y ∈ carrier), x + y ∈ carrier

end Definitions

variable {𝕜 E}

namespace ConvexCone

section OrderedSemiring

variable [OrderedSemiring 𝕜] [AddCommMonoidₓ E]

section HasSmul

variable [HasSmul 𝕜 E] (S T : ConvexCone 𝕜 E)

instance : SetLike (ConvexCone 𝕜 E) E where
  coe := Carrier
  coe_injective' := fun S T h => by
    cases S <;> cases T <;> congr

@[simp]
theorem coe_mk {s : Set E} {h₁ h₂} : ↑(@mk 𝕜 _ _ _ _ s h₁ h₂) = s :=
  rfl

@[simp]
theorem mem_mk {s : Set E} {h₁ h₂ x} : x ∈ @mk 𝕜 _ _ _ _ s h₁ h₂ ↔ x ∈ s :=
  Iff.rfl

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext]
theorem ext {S T : ConvexCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

theorem smul_mem {c : 𝕜} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S :=
  S.smul_mem' hc hx

theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S :=
  S.add_mem' hx hy

instance : AddMemClass (ConvexCone 𝕜 E) E where add_mem := fun c a b ha hb => add_mem c ha hb

instance : HasInf (ConvexCone 𝕜 E) :=
  ⟨fun S T =>
    ⟨S ∩ T, fun c hc x hx => ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩, fun x hx y hy =>
      ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

@[simp]
theorem coe_inf : ((S⊓T : ConvexCone 𝕜 E) : Set E) = ↑S ∩ ↑T :=
  rfl

theorem mem_inf {x} : x ∈ S⊓T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

instance : HasInfₓ (ConvexCone 𝕜 E) :=
  ⟨fun S =>
    ⟨⋂ s ∈ S, ↑s, fun c hc x hx => mem_bInter fun s hs => s.smul_mem hc <| mem_Inter₂.1 hx s hs, fun x hx y hy =>
      mem_bInter fun s hs => s.add_mem (mem_Inter₂.1 hx s hs) (mem_Inter₂.1 hy s hs)⟩⟩

@[simp]
theorem coe_Inf (S : Set (ConvexCone 𝕜 E)) : ↑(inf S) = ⋂ s ∈ S, (s : Set E) :=
  rfl

theorem mem_Inf {x : E} {S : Set (ConvexCone 𝕜 E)} : x ∈ inf S ↔ ∀ s ∈ S, x ∈ s :=
  mem_Inter₂

@[simp]
theorem coe_infi {ι : Sort _} (f : ι → ConvexCone 𝕜 E) : ↑(infi f) = ⋂ i, (f i : Set E) := by
  simp [infi]

theorem mem_infi {ι : Sort _} {x : E} {f : ι → ConvexCone 𝕜 E} : x ∈ infi f ↔ ∀ i, x ∈ f i :=
  mem_Inter₂.trans <| by
    simp

variable (𝕜)

instance : HasBot (ConvexCone 𝕜 E) :=
  ⟨⟨∅, fun c hc x => False.elim, fun x => False.elim⟩⟩

theorem mem_bot (x : E) : (x ∈ (⊥ : ConvexCone 𝕜 E)) = False :=
  rfl

@[simp]
theorem coe_bot : ↑(⊥ : ConvexCone 𝕜 E) = (∅ : Set E) :=
  rfl

instance : HasTop (ConvexCone 𝕜 E) :=
  ⟨⟨Univ, fun c hc x hx => mem_univ _, fun x hx y hy => mem_univ _⟩⟩

theorem mem_top (x : E) : x ∈ (⊤ : ConvexCone 𝕜 E) :=
  mem_univ x

@[simp]
theorem coe_top : ↑(⊤ : ConvexCone 𝕜 E) = (Univ : Set E) :=
  rfl

instance : CompleteLattice (ConvexCone 𝕜 E) :=
  { SetLike.partialOrder with le := (· ≤ ·), lt := (· < ·), bot := ⊥, bot_le := fun S x => False.elim, top := ⊤,
    le_top := fun S x hx => mem_top 𝕜 x, inf := (·⊓·), inf := HasInfₓ.inf, sup := fun a b => inf { x | a ≤ x ∧ b ≤ x },
    sup := fun s => inf { T | ∀ S ∈ s, S ≤ T }, le_sup_left := fun a b => fun x hx => mem_Inf.2 fun s hs => hs.1 hx,
    le_sup_right := fun a b => fun x hx => mem_Inf.2 fun s hs => hs.2 hx,
    sup_le := fun a b c ha hb x hx => mem_Inf.1 hx c ⟨ha, hb⟩, le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩,
    inf_le_left := fun a b x => And.left, inf_le_right := fun a b x => And.right,
    le_Sup := fun s p hs x hx => mem_Inf.2 fun t ht => ht p hs hx, Sup_le := fun s p hs x hx => mem_Inf.1 hx p hs,
    le_Inf := fun s a ha x hx => mem_Inf.2 fun t ht => ha t ht hx, Inf_le := fun s a ha x hx => mem_Inf.1 hx _ ha }

instance : Inhabited (ConvexCone 𝕜 E) :=
  ⟨⊥⟩

end HasSmul

section Module

variable [Module 𝕜 E] (S : ConvexCone 𝕜 E)

protected theorem convex : Convex 𝕜 (S : Set E) :=
  convex_iff_forall_pos.2 fun x hx y hy a b ha hb _ => S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

end Module

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F] [AddCommMonoidₓ G]

section MulAction

variable [MulAction 𝕜 E] (S : ConvexCone 𝕜 E)

theorem smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : E} : c • x ∈ S ↔ x ∈ S :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hc⟩

end MulAction

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]

/-- The image of a convex cone under a `𝕜`-linear map is a convex cone. -/
def map (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) : ConvexCone 𝕜 F where
  Carrier := f '' S
  smul_mem' := fun c hc y ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx)
  add_mem' := fun y₁ ⟨x₁, hx₁, hy₁⟩ y₂ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (S.add_mem hx₁ hx₂)

@[simp]
theorem mem_map {f : E →ₗ[𝕜] F} {S : ConvexCone 𝕜 E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex

theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image g f S

@[simp]
theorem map_id (S : ConvexCone 𝕜 E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| image_id _

/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : ConvexCone 𝕜 E where
  Carrier := f ⁻¹' S
  smul_mem' := fun c hc x hx => by
    rw [mem_preimage, f.map_smul c]
    exact S.smul_mem hc hx
  add_mem' := fun x hx y hy => by
    rw [mem_preimage, f.map_add]
    exact S.add_mem hx hy

@[simp]
theorem coe_comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl

@[simp]
theorem comap_id (S : ConvexCone 𝕜 E) : S.comap LinearMap.id = S :=
  SetLike.coe_injective preimage_id

theorem comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 G) : (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| preimage_comp.symm

@[simp]
theorem mem_comap {f : E →ₗ[𝕜] F} {S : ConvexCone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

end Module

end AddCommMonoidₓ

section OrderedAddCommGroup

variable [OrderedAddCommGroup E] [Module 𝕜 E]

/-- Constructs an ordered module given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_ordered_smul (S : ConvexCone 𝕜 E) (h : ∀ x y : E, x ≤ y ↔ y - x ∈ S) : OrderedSmul 𝕜 E :=
  OrderedSmul.mk'
    (by
      intro x y z xy hz
      rw [h (z • x) (z • y), ← smul_sub z y x]
      exact smul_mem S hz ((h x y).mp xy.le))

end OrderedAddCommGroup

end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [HasSmul 𝕜 E] (S : ConvexCone 𝕜 E)

/-- A convex cone is pointed if it includes `0`. -/
def Pointed (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∈ S

/-- A convex cone is blunt if it doesn't include `0`. -/
def Blunt (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∉ S

theorem pointed_iff_not_blunt (S : ConvexCone 𝕜 E) : S.Pointed ↔ ¬S.Blunt :=
  ⟨fun h₁ h₂ => h₂ h₁, not_not.mp⟩

theorem blunt_iff_not_pointed (S : ConvexCone 𝕜 E) : S.Blunt ↔ ¬S.Pointed := by
  rw [pointed_iff_not_blunt, not_not]

theorem Pointed.mono {S T : ConvexCone 𝕜 E} (h : S ≤ T) : S.Pointed → T.Pointed :=
  @h _

theorem Blunt.anti {S T : ConvexCone 𝕜 E} (h : T ≤ S) : S.Blunt → T.Blunt :=
  (· ∘ @h)

end AddCommMonoidₓ

section AddCommGroupₓ

variable [AddCommGroupₓ E] [HasSmul 𝕜 E] (S : ConvexCone 𝕜 E)

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def Flat : Prop :=
  ∃ x ∈ S, x ≠ (0 : E) ∧ -x ∈ S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def Salient : Prop :=
  ∀ x ∈ S, x ≠ (0 : E) → -x ∉ S

theorem salient_iff_not_flat (S : ConvexCone 𝕜 E) : S.Salient ↔ ¬S.Flat := by
  constructor
  · rintro h₁ ⟨x, xs, H₁, H₂⟩
    exact h₁ x xs H₁ H₂
    
  · intro h
    unfold flat  at h
    push_neg  at h
    exact h
    

theorem Flat.mono {S T : ConvexCone 𝕜 E} (h : S ≤ T) : S.Flat → T.Flat
  | ⟨x, hxS, hx, hnxS⟩ => ⟨x, h hxS, hx, h hnxS⟩

theorem Salient.anti {S T : ConvexCone 𝕜 E} (h : T ≤ S) : S.Salient → T.Salient := fun hS x hxT hx hnT =>
  hS x (h hxT) hx (h hnT)

/-- A flat cone is always pointed (contains `0`). -/
theorem Flat.pointed {S : ConvexCone 𝕜 E} (hS : S.Flat) : S.Pointed := by
  obtain ⟨x, hx, _, hxneg⟩ := hS
  rw [pointed, ← add_neg_selfₓ x]
  exact add_mem S hx hxneg

/-- A blunt cone (one not containing `0`) is always salient. -/
theorem Blunt.salient {S : ConvexCone 𝕜 E} : S.Blunt → S.Salient := by
  rw [salient_iff_not_flat, blunt_iff_not_pointed]
  exact mt flat.pointed

/-- A pointed convex cone defines a preorder. -/
def toPreorder (h₁ : S.Pointed) : Preorderₓ E where
  le := fun x y => y - x ∈ S
  le_refl := fun x => by
    change x - x ∈ S <;> rw [sub_self x] <;> exact h₁
  le_trans := fun x y z xy zy => by
    simpa using add_mem S zy xy

/-- A pointed and salient cone defines a partial order. -/
def toPartialOrder (h₁ : S.Pointed) (h₂ : S.Salient) : PartialOrderₓ E :=
  { toPreorder S h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a ≠ 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def toOrderedAddCommGroup (h₁ : S.Pointed) (h₂ : S.Salient) : OrderedAddCommGroup E :=
  { toPartialOrder S h₁ h₂,
    show AddCommGroupₓ E by
      infer_instance with
    add_le_add_left := by
      intro a b hab c
      change c + b - (c + a) ∈ S
      rw [add_sub_add_left_eq_sub]
      exact hab }

end AddCommGroupₓ

end OrderedSemiring

/-! ### Positive cone of an ordered module -/


section PositiveCone

variable (𝕜 E) [OrderedSemiring 𝕜] [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSmul 𝕜 E]

/-- The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive : ConvexCone 𝕜 E where
  Carrier := Set.Ici 0
  smul_mem' := fun c hc x (hx : _ ≤ _) => smul_nonneg hc.le hx
  add_mem' := fun x (hx : _ ≤ _) y (hy : _ ≤ _) => add_nonneg hx hy

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = Set.Ici (0 : E) :=
  rfl

/-- The positive cone of an ordered module is always salient. -/
theorem salient_positive : Salient (positive 𝕜 E) := fun x xs hx hx' =>
  lt_irreflₓ (0 : E)
    (calc
      0 < x := lt_of_le_of_neₓ xs hx.symm
      _ ≤ x + -x := le_add_of_nonneg_right hx'
      _ = 0 := add_neg_selfₓ x
      )

/-- The positive cone of an ordered module is always pointed. -/
theorem pointed_positive : Pointed (positive 𝕜 E) :=
  le_reflₓ 0

/-- The cone of strictly positive elements.

Note that this naming diverges from the mathlib convention of `pos` and `nonneg` due to "positive
cone" (`convex_cone.positive`) being established terminology for the non-negative elements. -/
def strictlyPositive : ConvexCone 𝕜 E where
  Carrier := Set.Ioi 0
  smul_mem' := fun c hc x (hx : _ < _) => smul_pos hc hx
  add_mem' := fun x hx y hy => add_pos hx hy

@[simp]
theorem mem_strictly_positive {x : E} : x ∈ strictlyPositive 𝕜 E ↔ 0 < x :=
  Iff.rfl

@[simp]
theorem coe_strictly_positive : ↑(strictlyPositive 𝕜 E) = Set.Ioi (0 : E) :=
  rfl

theorem positive_le_strictly_positive : strictlyPositive 𝕜 E ≤ positive 𝕜 E := fun x => le_of_ltₓ

/-- The strictly positive cone of an ordered module is always salient. -/
theorem salient_strictly_positive : Salient (strictlyPositive 𝕜 E) :=
  (salient_positive 𝕜 E).anti <| positive_le_strictly_positive 𝕜 E

/-- The strictly positive cone of an ordered module is always blunt. -/
theorem blunt_strictly_positive : Blunt (strictlyPositive 𝕜 E) :=
  lt_irreflₓ 0

end PositiveCone

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable [LinearOrderedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

namespace Convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def toCone (s : Set E) (hs : Convex 𝕜 s) : ConvexCone 𝕜 E := by
  apply ConvexCone.mk (⋃ (c : 𝕜) (H : 0 < c), c • s) <;> simp only [mem_Union, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
    
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine' ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, _⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left _ this.ne']
    

variable {s : Set E} (hs : Convex 𝕜 s) {x : E}

theorem mem_to_cone : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ ∃ y ∈ s, c • y = x := by
  simp only [to_cone, ConvexCone.mem_mk, mem_Union, mem_smul_set, eq_comm, exists_prop]

theorem mem_to_cone' : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ c • x ∈ s := by
  refine' hs.mem_to_cone.trans ⟨_, _⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact
      ⟨c⁻¹, inv_pos.2 hc, by
        rwa [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩
    
  · rintro ⟨c, hc, hcx⟩
    exact
      ⟨c⁻¹, inv_pos.2 hc, _, hcx, by
        rw [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩
    

theorem subset_to_cone : s ⊆ hs.toCone s := fun x hx =>
  hs.mem_to_cone'.2
    ⟨1, zero_lt_one, by
      rwa [one_smul]⟩

/-- `hs.to_cone s` is the least cone that includes `s`. -/
theorem to_cone_is_least : IsLeast { t : ConvexCone 𝕜 E | s ⊆ t } (hs.toCone s) := by
  refine' ⟨hs.subset_to_cone, fun t ht x hx => _⟩
  rcases hs.mem_to_cone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

theorem to_cone_eq_Inf : hs.toCone s = inf { t : ConvexCone 𝕜 E | s ⊆ t } :=
  hs.to_cone_is_least.IsGlb.Inf_eq.symm

end Convex

theorem convex_hull_to_cone_is_least (s : Set E) :
    IsLeast { t : ConvexCone 𝕜 E | s ⊆ t } ((convex_convex_hull 𝕜 s).toCone _) := by
  convert (convex_convex_hull 𝕜 s).to_cone_is_least
  ext t
  exact ⟨fun h => convex_hull_min h t.convex, (subset_convex_hull 𝕜 s).trans⟩

theorem convex_hull_to_cone_eq_Inf (s : Set E) :
    (convex_convex_hull 𝕜 s).toCone _ = inf { t : ConvexCone 𝕜 E | s ⊆ t } :=
  Eq.symm <| IsGlb.Inf_eq <| IsLeast.is_glb <| convex_hull_to_cone_is_least s

end ConeFromConvex

/-!
### M. Riesz extension theorem

Given a convex cone `s` in a vector space `E`, a submodule `p`, and a linear `f : p → ℝ`, assume
that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then there exists a globally defined linear
function `g : E → ℝ` that agrees with `f` on `p`, and is nonnegative on `s`.

We prove this theorem using Zorn's lemma. `riesz_extension.step` is the main part of the proof.
It says that if the domain `p` of `f` is not the whole space, then `f` can be extended to a larger
subspace `p ⊔ span ℝ {y}` without breaking the non-negativity condition.

In `riesz_extension.exists_top` we use Zorn's lemma to prove that we can extend `f`
to a linear map `g` on `⊤ : submodule E`. Mathematically this is the same as a linear map on `E`
but in Lean `⊤ : submodule E` is isomorphic but is not equal to `E`. In `riesz_extension`
we use this isomorphism to prove the theorem.
-/


variable [AddCommGroupₓ E] [Module ℝ E]

namespace riesz_extension

open Submodule

variable (s : ConvexCone ℝ E) (f : E →ₗ.[ℝ] ℝ)

/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain → ℝ`, assume that `f` is nonnegative on `f.domain ∩ p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
theorem step (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x) (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s)
    (hdom : f.domain ≠ ⊤) : ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x := by
  obtain ⟨y, -, hy⟩ : ∃ (y : E)(h : y ∈ ⊤), y ∉ f.domain :=
    @SetLike.exists_of_lt (Submodule ℝ E) _ _ _ _ (lt_top_iff_ne_top.2 hdom)
  obtain ⟨c, le_c, c_le⟩ :
    ∃ c, (∀ x : f.domain, -(x : E) - y ∈ s → f x ≤ c) ∧ ∀ x : f.domain, (x : E) + y ∈ s → c ≤ f x := by
    set Sp := f '' { x : f.domain | (x : E) + y ∈ s }
    set Sn := f '' { x : f.domain | -(x : E) - y ∈ s }
    suffices (UpperBounds Sn ∩ LowerBounds Sp).Nonempty by
      simpa only [Set.Nonempty, UpperBounds, LowerBounds, ball_image_iff] using this
    refine' exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (Dense y)) _
    · rcases Dense (-y) with ⟨x, hx⟩
      rw [← neg_negₓ x, AddSubgroupClass.coe_neg, ← sub_eq_add_neg] at hx
      exact ⟨_, hx⟩
      
    rintro a ⟨xn, hxn, rfl⟩ b ⟨xp, hxp, rfl⟩
    have := s.add_mem hxp hxn
    rw [add_assocₓ, add_sub_cancel'_right, ← sub_eq_add_neg, ← AddSubgroupClass.coe_sub] at this
    replace := nonneg _ this
    rwa [f.map_sub, sub_nonneg] at this
  have hy' : y ≠ 0 := fun hy₀ => hy (hy₀.symm ▸ zero_mem _)
  refine' ⟨f.sup_span_singleton y (-c) hy, _, _⟩
  · refine' lt_iff_le_not_leₓ.2 ⟨f.left_le_sup _ _, fun H => _⟩
    replace H := linear_pmap.domain_mono.monotone H
    rw [LinearPmap.domain_sup_span_singleton, sup_le_iff, span_le, singleton_subset_iff] at H
    exact hy H.2
    
  · rintro ⟨z, hz⟩ hzs
    rcases mem_sup.1 hz with ⟨x, hx, y', hy', rfl⟩
    rcases mem_span_singleton.1 hy' with ⟨r, rfl⟩
    simp only [Subtype.coe_mk] at hzs
    erw [LinearPmap.sup_span_singleton_apply_mk _ _ _ _ _ hx, smul_neg, ← sub_eq_add_neg, sub_nonneg]
    rcases lt_trichotomyₓ r 0 with (hr | hr | hr)
    · have : -(r⁻¹ • x) - y ∈ s := by
        rwa [← s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul, neg_negₓ, smul_smul, mul_inv_cancel hr.ne,
          one_smul, sub_eq_add_neg, neg_smul, neg_negₓ]
      replace := le_c (r⁻¹ • ⟨x, hx⟩) this
      rwa [← mul_le_mul_left (neg_pos.2 hr), neg_mul, neg_mul, neg_le_neg_iff, f.map_smul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel hr.ne, one_mulₓ] at this
      
    · subst r
      simp only [zero_smul, add_zeroₓ] at hzs⊢
      apply nonneg
      exact hzs
      
    · have : r⁻¹ • x + y ∈ s := by
        rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel hr.ne', one_smul]
      replace := c_le (r⁻¹ • ⟨x, hx⟩) this
      rwa [← mul_le_mul_left hr, f.map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel hr.ne', one_mulₓ] at this
      
    

theorem exists_top (p : E →ₗ.[ℝ] ℝ) (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
    (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) : ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x :=
  by
  replace hp_nonneg : p ∈ { p | _ }
  · rw [mem_set_of_eq]
    exact hp_nonneg
    
  obtain ⟨q, hqs, hpq, hq⟩ := zorn_nonempty_partial_order₀ _ _ _ hp_nonneg
  · refine' ⟨q, hpq, _, hqs⟩
    contrapose! hq
    rcases step s q hqs _ hq with ⟨r, hqr, hr⟩
    · exact ⟨r, hr, hqr.le, hqr.ne'⟩
      
    · exact fun y =>
        let ⟨x, hx⟩ := hp_dense y
        ⟨of_le hpq.left x, hx⟩
      
    
  · intro c hcs c_chain y hy
    clear hp_nonneg hp_dense p
    have cne : c.nonempty := ⟨y, hy⟩
    refine' ⟨LinearPmap.supₓ c c_chain.directed_on, _, fun _ => LinearPmap.le_Sup c_chain.directed_on⟩
    rintro ⟨x, hx⟩ hxs
    have hdir : DirectedOn (· ≤ ·) (LinearPmap.domain '' c) :=
      directed_on_image.2 (c_chain.directed_on.mono linear_pmap.domain_mono.monotone)
    rcases(mem_Sup_of_directed (cne.image _) hdir).1 hx with ⟨_, ⟨f, hfc, rfl⟩, hfx⟩
    have : f ≤ LinearPmap.supₓ c c_chain.directed_on := LinearPmap.le_Sup _ hfc
    convert ← hcs hfc ⟨x, hfx⟩ hxs
    apply this.2
    rfl
    

end riesz_extension

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p → ℝ`, assume that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then
there exists a globally defined linear function `g : E → ℝ` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem riesz_extension (s : ConvexCone ℝ E) (f : E →ₗ.[ℝ] ℝ) (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) : ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x :=
  by
  rcases RieszExtension.exists_top s f nonneg Dense with ⟨⟨g_dom, g⟩, ⟨hpg, hfg⟩, htop, hgs⟩
  clear hpg
  refine' ⟨g ∘ₗ ↑(LinearEquiv.ofTop _ htop).symm, _, _⟩ <;>
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.of_top_symm_apply]
  · exact fun x => (hfg (Submodule.coe_mk _ _).symm).symm
    
  · exact fun x hx => hgs ⟨x, _⟩ hx
    

/-- **Hahn-Banach theorem**: if `N : E → ℝ` is a sublinear map, `f` is a linear map
defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
for all `x`. -/
theorem exists_extension_of_le_sublinear (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x) (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) : ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  let s : ConvexCone ℝ (E × ℝ) :=
    { Carrier := { p : E × ℝ | N p.1 ≤ p.2 },
      smul_mem' := fun c hc p hp =>
        calc
          N (c • p.1) = c * N p.1 := N_hom c hc p.1
          _ ≤ c * p.2 := mul_le_mul_of_nonneg_left hp hc.le
          ,
      add_mem' := fun x hx y hy => (N_add _ _).trans (add_le_add hx hy) }
  obtain ⟨g, g_eq, g_nonneg⟩ := riesz_extension s ((-f).coprod (linear_map.id.to_pmap ⊤)) _ _ <;>
    try
      simp only [LinearPmap.coprod_apply, to_pmap_apply, id_apply, LinearPmap.neg_apply, ← sub_eq_neg_add, sub_nonneg,
        Subtype.coe_mk] at *
  replace g_eq : ∀ (x : f.domain) (y : ℝ), g (x, y) = y - f x
  · intro x y
    simpa only [Subtype.coe_mk, Subtype.coe_eta] using g_eq ⟨(x, y), ⟨x.2, trivialₓ⟩⟩
    
  · refine' ⟨-g.comp (inl ℝ E ℝ), _, _⟩ <;> simp only [neg_apply, inl_apply, comp_apply]
    · intro x
      simp [g_eq x 0]
      
    · intro x
      have A : (x, N x) = (x, 0) + (0, N x) := by
        simp
      have B := g_nonneg ⟨x, N x⟩ (le_reflₓ (N x))
      rw [A, map_add, ← neg_le_iff_add_nonneg'] at B
      have C := g_eq 0 (N x)
      simp only [Submodule.coe_zero, f.map_zero, sub_zero] at C
      rwa [← C]
      
    
  · exact fun x hx => le_transₓ (hf _) hx
    
  · rintro ⟨x, y⟩
    refine' ⟨⟨(0, N x - y), ⟨f.domain.zero_mem, trivialₓ⟩⟩, _⟩
    simp only [ConvexCone.mem_mk, mem_set_of_eq, Subtype.coe_mk, Prod.fst_add, Prod.snd_add, zero_addₓ, sub_add_cancel]
    

/-! ### The dual cone -/


section Dual

variable {H : Type _} [InnerProductSpace ℝ H] (s t : Set H)

open RealInnerProductSpace

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
def Set.innerDualCone (s : Set H) : ConvexCone ℝ H where
  Carrier := { y | ∀ x ∈ s, 0 ≤ ⟪x, y⟫ }
  smul_mem' := fun c hc y hy x hx => by
    rw [real_inner_smul_right]
    exact mul_nonneg hc.le (hy x hx)
  add_mem' := fun u hu v hv x hx => by
    rw [inner_add_right]
    exact add_nonneg (hu x hx) (hv x hx)

@[simp]
theorem mem_inner_dual_cone (y : H) (s : Set H) : y ∈ s.innerDualCone ↔ ∀ x ∈ s, 0 ≤ ⟪x, y⟫ :=
  Iff.rfl

@[simp]
theorem inner_dual_cone_empty : (∅ : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun x hy y => False.elim

theorem inner_dual_cone_le_inner_dual_cone (h : t ⊆ s) : s.innerDualCone ≤ t.innerDualCone := fun y hy x hx =>
  hy x (h hx)

theorem pointed_inner_dual_cone : s.innerDualCone.Pointed := fun x hx => by
  rw [inner_zero_right]

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `λ y, ⟪x, y⟫`. -/
theorem inner_dual_cone_singleton (x : H) : ({x} : Set H).innerDualCone = (ConvexCone.positive ℝ ℝ).comap (innerₛₗ x) :=
  ConvexCone.ext fun i => forall_eq

theorem inner_dual_cone_union (s t : Set H) : (s ∪ t).innerDualCone = s.innerDualCone⊓t.innerDualCone :=
  le_antisymmₓ (le_inf (fun x hx y hy => hx _ <| Or.inl hy) fun x hx y hy => hx _ <| Or.inr hy) fun x hx y =>
    Or.ndrec (hx.1 _) (hx.2 _)

theorem inner_dual_cone_insert (x : H) (s : Set H) :
    (insert x s).innerDualCone = Set.innerDualCone {x}⊓s.innerDualCone := by
  rw [insert_eq, inner_dual_cone_union]

theorem inner_dual_cone_Union {ι : Sort _} (f : ι → Set H) : (⋃ i, f i).innerDualCone = ⨅ i, (f i).innerDualCone := by
  refine' le_antisymmₓ (le_infi fun i x hx y hy => hx _ <| mem_Union_of_mem _ hy) _
  intro x hx y hy
  rw [ConvexCone.mem_infi] at hx
  obtain ⟨j, hj⟩ := mem_Union.mp hy
  exact hx _ _ hj

theorem inner_dual_cone_sUnion (S : Set (Set H)) : (⋃₀S).innerDualCone = inf (Set.innerDualCone '' S) := by
  simp_rw [Inf_image, sUnion_eq_bUnion, inner_dual_cone_Union]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
theorem inner_dual_cone_eq_Inter_inner_dual_cone_singleton :
    (s.innerDualCone : Set H) = ⋂ i : s, (({i} : Set H).innerDualCone : Set H) := by
  rw [← ConvexCone.coe_infi, ← inner_dual_cone_Union, Union_of_singleton_coe]

theorem is_closed_inner_dual_cone : IsClosed (s.innerDualCone : Set H) := by
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw [inner_dual_cone_eq_Inter_inner_dual_cone_singleton]
  apply is_closed_Inter
  intro x
  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : ↑({x} : Set H).innerDualCone = (inner x : H → ℝ) ⁻¹' Set.Ici 0 := by
    rw [inner_dual_cone_singleton, ConvexCone.coe_comap, ConvexCone.coe_positive, innerₛₗ_apply_coe]
  -- the preimage is closed as `inner x` is continuous and `[0, ∞)` is closed
  rw [h]
  exact
    is_closed_Ici.preimage
      (by
        continuity)

end Dual

