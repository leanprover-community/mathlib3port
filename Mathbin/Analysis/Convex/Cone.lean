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

open_locale Classical Pointwise

variable{𝕜 E F G : Type _}

/-! ### Definition of `convex_cone` and basic properties -/


section Definitions

variable(𝕜 E)[OrderedSemiring 𝕜]

/-- A convex cone is a subset `s` of a `𝕜`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure ConvexCone[AddCommMonoidₓ E][HasScalar 𝕜 E] where 
  Carrier : Set E 
  smul_mem' : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier 
  add_mem' : ∀ ⦃x⦄ hx : x ∈ carrier ⦃y⦄ hy : y ∈ carrier, (x+y) ∈ carrier

end Definitions

variable{𝕜 E}

namespace ConvexCone

section OrderedSemiring

variable[OrderedSemiring 𝕜][AddCommMonoidₓ E]

section HasScalar

variable[HasScalar 𝕜 E](S T : ConvexCone 𝕜 E)

instance  : Coe (ConvexCone 𝕜 E) (Set E) :=
  ⟨ConvexCone.Carrier⟩

instance  : HasMem E (ConvexCone 𝕜 E) :=
  ⟨fun m S => m ∈ S.carrier⟩

instance  : LE (ConvexCone 𝕜 E) :=
  ⟨fun S T => S.carrier ⊆ T.carrier⟩

instance  : LT (ConvexCone 𝕜 E) :=
  ⟨fun S T => S.carrier ⊂ T.carrier⟩

@[simp, normCast]
theorem mem_coe {x : E} : x ∈ (S : Set E) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_mk {s : Set E} {h₁ h₂ x} : x ∈ @mk 𝕜 _ _ _ _ s h₁ h₂ ↔ x ∈ s :=
  Iff.rfl

/-- Two `convex_cone`s are equal if the underlying sets are equal. -/
theorem ext' {S T : ConvexCone 𝕜 E} (h : (S : Set E) = T) : S = T :=
  by 
    cases S <;> cases T <;> congr

/-- Two `convex_cone`s are equal if and only if the underlying sets are equal. -/
protected theorem ext'_iff {S T : ConvexCone 𝕜 E} : (S : Set E) = T ↔ S = T :=
  ⟨ext', fun h => h ▸ rfl⟩

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext]
theorem ext {S T : ConvexCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  ext'$ Set.ext h

theorem smul_mem {c : 𝕜} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S :=
  S.smul_mem' hc hx

theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : (x+y) ∈ S :=
  S.add_mem' hx hy

instance  : HasInf (ConvexCone 𝕜 E) :=
  ⟨fun S T =>
      ⟨S ∩ T, fun c hc x hx => ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩,
        fun x hx y hy => ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

theorem coe_inf : ((S⊓T : ConvexCone 𝕜 E) : Set E) = «expr↑ » S ∩ «expr↑ » T :=
  rfl

theorem mem_inf {x} : x ∈ S⊓T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

instance  : HasInfₓ (ConvexCone 𝕜 E) :=
  ⟨fun S =>
      ⟨⋂(s : _)(_ : s ∈ S), «expr↑ » s,
        fun c hc x hx =>
          mem_bInter$
            fun s hs =>
              s.smul_mem hc$
                by 
                  apply mem_bInter_iff.1 hx s hs,
        fun x hx y hy =>
          mem_bInter$
            fun s hs =>
              s.add_mem
                (by 
                  apply mem_bInter_iff.1 hx s hs)
                (by 
                  apply mem_bInter_iff.1 hy s hs)⟩⟩

theorem mem_Inf {x : E} {S : Set (ConvexCone 𝕜 E)} : x ∈ Inf S ↔ ∀ s _ : s ∈ S, x ∈ s :=
  mem_bInter_iff

variable(𝕜)

instance  : HasBot (ConvexCone 𝕜 E) :=
  ⟨⟨∅, fun c hc x => False.elim, fun x => False.elim⟩⟩

theorem mem_bot (x : E) : (x ∈ (⊥ : ConvexCone 𝕜 E)) = False :=
  rfl

instance  : HasTop (ConvexCone 𝕜 E) :=
  ⟨⟨univ, fun c hc x hx => mem_univ _, fun x hx y hy => mem_univ _⟩⟩

theorem mem_top (x : E) : x ∈ (⊤ : ConvexCone 𝕜 E) :=
  mem_univ x

instance  : CompleteLattice (ConvexCone 𝕜 E) :=
  { PartialOrderₓ.lift (coeₓ : ConvexCone 𝕜 E → Set E) fun a b => ext' with le := · ≤ ·, lt := · < ·, bot := ⊥,
    bot_le := fun S x => False.elim, top := ⊤, le_top := fun S x hx => mem_top 𝕜 x, inf := ·⊓·, inf := HasInfₓ.inf,
    sup := fun a b => Inf { x | a ≤ x ∧ b ≤ x }, sup := fun s => Inf { T | ∀ S _ : S ∈ s, S ≤ T },
    le_sup_left := fun a b => fun x hx => mem_Inf.2$ fun s hs => hs.1 hx,
    le_sup_right := fun a b => fun x hx => mem_Inf.2$ fun s hs => hs.2 hx,
    sup_le := fun a b c ha hb x hx => mem_Inf.1 hx c ⟨ha, hb⟩, le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩,
    inf_le_left := fun a b x => And.left, inf_le_right := fun a b x => And.right,
    le_Sup := fun s p hs x hx => mem_Inf.2$ fun t ht => ht p hs hx, Sup_le := fun s p hs x hx => mem_Inf.1 hx p hs,
    le_Inf := fun s a ha x hx => mem_Inf.2$ fun t ht => ha t ht hx, Inf_le := fun s a ha x hx => mem_Inf.1 hx _ ha }

instance  : Inhabited (ConvexCone 𝕜 E) :=
  ⟨⊥⟩

end HasScalar

section Module

variable[Module 𝕜 E](S : ConvexCone 𝕜 E)

protected theorem Convex : Convex 𝕜 (S : Set E) :=
  convex_iff_forall_pos.2$ fun x y hx hy a b ha hb hab => S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

end Module

end OrderedSemiring

section LinearOrderedField

variable[LinearOrderedField 𝕜]

section AddCommMonoidₓ

variable[AddCommMonoidₓ E][AddCommMonoidₓ F][AddCommMonoidₓ G]

section MulAction

variable[MulAction 𝕜 E](S : ConvexCone 𝕜 E)

theorem smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : E} : c • x ∈ S ↔ x ∈ S :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hc⟩

end MulAction

section Module

variable[Module 𝕜 E][Module 𝕜 F][Module 𝕜 G]

/-- The image of a convex cone under a `𝕜`-linear map is a convex cone. -/
def map (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) : ConvexCone 𝕜 F :=
  { Carrier := f '' S,
    smul_mem' := fun c hc y ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx),
    add_mem' :=
      fun y₁ ⟨x₁, hx₁, hy₁⟩ y₂ ⟨x₂, hx₂, hy₂⟩ => hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (S.add_mem hx₁ hx₂) }

theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) : (S.map f).map g = S.map (g.comp f) :=
  ext'$ image_image g f S

@[simp]
theorem map_id (S : ConvexCone 𝕜 E) : S.map LinearMap.id = S :=
  ext'$ image_id _

/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : ConvexCone 𝕜 E :=
  { Carrier := f ⁻¹' S,
    smul_mem' :=
      fun c hc x hx =>
        by 
          rw [mem_preimage, f.map_smul c]
          exact S.smul_mem hc hx,
    add_mem' :=
      fun x hx y hy =>
        by 
          rw [mem_preimage, f.map_add]
          exact S.add_mem hx hy }

@[simp]
theorem comap_id (S : ConvexCone 𝕜 E) : S.comap LinearMap.id = S :=
  ext' preimage_id

theorem comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 G) : (S.comap g).comap f = S.comap (g.comp f) :=
  ext'$ preimage_comp.symm

@[simp]
theorem mem_comap {f : E →ₗ[𝕜] F} {S : ConvexCone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

end Module

end AddCommMonoidₓ

section OrderedAddCommGroup

variable[OrderedAddCommGroup E][Module 𝕜 E]

/--
Constructs an ordered module given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_ordered_smul (S : ConvexCone 𝕜 E) (h : ∀ x y : E, x ≤ y ↔ y - x ∈ S) : OrderedSmul 𝕜 E :=
  OrderedSmul.mk'
    (by 
      intro x y z xy hz 
      rw [h (z • x) (z • y), ←smul_sub z y x]
      exact smul_mem S hz ((h x y).mp xy.le))

end OrderedAddCommGroup

end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable[OrderedSemiring 𝕜]

section AddCommMonoidₓ

variable[AddCommMonoidₓ E][HasScalar 𝕜 E](S : ConvexCone 𝕜 E)

/-- A convex cone is pointed if it includes `0`. -/
def pointed (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∈ S

/-- A convex cone is blunt if it doesn't include `0`. -/
def blunt (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∉ S

theorem pointed_iff_not_blunt (S : ConvexCone 𝕜 E) : S.pointed ↔ ¬S.blunt :=
  ⟨fun h₁ h₂ => h₂ h₁, not_not.mp⟩

theorem blunt_iff_not_pointed (S : ConvexCone 𝕜 E) : S.blunt ↔ ¬S.pointed :=
  by 
    rw [pointed_iff_not_blunt, not_not]

end AddCommMonoidₓ

section AddCommGroupₓ

variable[AddCommGroupₓ E][HasScalar 𝕜 E](S : ConvexCone 𝕜 E)

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def flat : Prop :=
  ∃ (x : _)(_ : x ∈ S), x ≠ (0 : E) ∧ -x ∈ S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def salient : Prop :=
  ∀ x _ : x ∈ S, x ≠ (0 : E) → -x ∉ S

theorem salient_iff_not_flat (S : ConvexCone 𝕜 E) : S.salient ↔ ¬S.flat :=
  by 
    split 
    ·
      rintro h₁ ⟨x, xs, H₁, H₂⟩
      exact h₁ x xs H₁ H₂
    ·
      intro h 
      unfold flat  at h 
      pushNeg  at h 
      exact h

/-- A flat cone is always pointed (contains `0`). -/
theorem flat.pointed {S : ConvexCone 𝕜 E} (hS : S.flat) : S.pointed :=
  by 
    obtain ⟨x, hx, _, hxneg⟩ := hS 
    rw [pointed, ←add_neg_selfₓ x]
    exact add_mem S hx hxneg

/-- A blunt cone (one not containing `0`) is always salient. -/
theorem blunt.salient {S : ConvexCone 𝕜 E} : S.blunt → S.salient :=
  by 
    rw [salient_iff_not_flat, blunt_iff_not_pointed]
    exact mt flat.pointed

/-- A pointed convex cone defines a preorder. -/
def to_preorder (h₁ : S.pointed) : Preorderₓ E :=
  { le := fun x y => y - x ∈ S,
    le_refl :=
      fun x =>
        by 
          change x - x ∈ S <;> rw [sub_self x] <;> exact h₁,
    le_trans :=
      fun x y z xy zy =>
        by 
          simpa using add_mem S zy xy }

-- error in Analysis.Convex.Cone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A pointed and salient cone defines a partial order. -/
def to_partial_order (h₁ : S.pointed) (h₂ : S.salient) : partial_order E :=
{ le_antisymm := begin
    intros [ident a, ident b, ident ab, ident ba],
    by_contradiction [ident h],
    have [ident h'] [":", expr «expr ≠ »(«expr - »(b, a), 0)] [":=", expr λ h'', h (eq_of_sub_eq_zero h'').symm],
    have [ident H] [] [":=", expr h₂ «expr - »(b, a) ab h'],
    rw [expr neg_sub b a] ["at", ident H],
    exact [expr H ba]
  end,
  ..to_preorder S h₁ }

/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def to_ordered_add_comm_group (h₁ : S.pointed) (h₂ : S.salient) : OrderedAddCommGroup E :=
  { to_partial_order S h₁ h₂,
    show AddCommGroupₓ E by 
      infer_instance with
    add_le_add_left :=
      by 
        intro a b hab c 
        change ((c+b) - c+a) ∈ S 
        rw [add_sub_add_left_eq_sub]
        exact hab }

end AddCommGroupₓ

end OrderedSemiring

/-! ### Positive cone of an ordered module -/


section PositiveCone

variable(𝕜 E)[OrderedSemiring 𝕜][OrderedAddCommGroup E][Module 𝕜 E][OrderedSmul 𝕜 E]

/--
The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive_cone : ConvexCone 𝕜 E :=
  { Carrier := { x | 0 ≤ x },
    smul_mem' :=
      by 
        rintro c hc x (hx : _ ≤ _)
        rw [←smul_zero c]
        exact smul_le_smul_of_nonneg hx hc.le,
    add_mem' := fun x hx : _ ≤ _ y hy : _ ≤ _ => add_nonneg hx hy }

/-- The positive cone of an ordered module is always salient. -/
theorem salient_positive_cone : salient (positive_cone 𝕜 E) :=
  fun x xs hx hx' =>
    lt_irreflₓ (0 : E)
      (calc 0 < x := lt_of_le_of_neₓ xs hx.symm 
        _ ≤ x+-x := le_add_of_nonneg_right hx' 
        _ = 0 := add_neg_selfₓ x
        )

/-- The positive cone of an ordered module is always pointed. -/
theorem pointed_positive_cone : pointed (positive_cone 𝕜 E) :=
  le_reflₓ 0

end PositiveCone

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable[LinearOrderedField 𝕜][OrderedAddCommGroup E][Module 𝕜 E]

namespace Convex

-- error in Analysis.Convex.Cone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def to_cone (s : set E) (hs : convex 𝕜 s) : convex_cone 𝕜 E :=
begin
  apply [expr convex_cone.mk «expr⋃ , »((c : 𝕜)
    (H : «expr < »(0, c)), «expr • »(c, s))]; simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_smul_set, "]"] [] [],
  { rintros [ident c, ident c_pos, "_", "⟨", ident c', ",", ident c'_pos, ",", ident x, ",", ident hx, ",", ident rfl, "⟩"],
    exact [expr ⟨«expr * »(c, c'), mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩] },
  { rintros ["_", "⟨", ident cx, ",", ident cx_pos, ",", ident x, ",", ident hx, ",", ident rfl, "⟩", "_", "⟨", ident cy, ",", ident cy_pos, ",", ident y, ",", ident hy, ",", ident rfl, "⟩"],
    have [] [":", expr «expr < »(0, «expr + »(cx, cy))] [],
    from [expr add_pos cx_pos cy_pos],
    refine [expr ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, _⟩],
    simp [] [] ["only"] ["[", expr smul_add, ",", expr smul_smul, ",", expr mul_div_assoc', ",", expr mul_div_cancel_left _ this.ne', "]"] [] [] }
end

variable{s : Set E}(hs : Convex 𝕜 s){x : E}

theorem mem_to_cone : x ∈ hs.to_cone s ↔ ∃ c : 𝕜, 0 < c ∧ ∃ (y : _)(_ : y ∈ s), c • y = x :=
  by 
    simp only [to_cone, ConvexCone.mem_mk, mem_Union, mem_smul_set, eq_comm, exists_prop]

theorem mem_to_cone' : x ∈ hs.to_cone s ↔ ∃ c : 𝕜, 0 < c ∧ c • x ∈ s :=
  by 
    refine' hs.mem_to_cone.trans ⟨_, _⟩
    ·
      rintro ⟨c, hc, y, hy, rfl⟩
      exact
        ⟨c⁻¹, inv_pos.2 hc,
          by 
            rwa [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩
    ·
      rintro ⟨c, hc, hcx⟩
      exact
        ⟨c⁻¹, inv_pos.2 hc, _, hcx,
          by 
            rw [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩

theorem subset_to_cone : s ⊆ hs.to_cone s :=
  fun x hx =>
    hs.mem_to_cone'.2
      ⟨1, zero_lt_one,
        by 
          rwa [one_smul]⟩

/-- `hs.to_cone s` is the least cone that includes `s`. -/
theorem to_cone_is_least : IsLeast { t:ConvexCone 𝕜 E | s ⊆ t } (hs.to_cone s) :=
  by 
    refine' ⟨hs.subset_to_cone, fun t ht x hx => _⟩
    rcases hs.mem_to_cone.1 hx with ⟨c, hc, y, hy, rfl⟩
    exact t.smul_mem hc (ht hy)

theorem to_cone_eq_Inf : hs.to_cone s = Inf { t:ConvexCone 𝕜 E | s ⊆ t } :=
  hs.to_cone_is_least.is_glb.Inf_eq.symm

end Convex

theorem convex_hull_to_cone_is_least (s : Set E) :
  IsLeast { t:ConvexCone 𝕜 E | s ⊆ t } ((convex_convex_hull 𝕜 s).toCone _) :=
  by 
    convert (convex_convex_hull 𝕜 s).to_cone_is_least 
    ext t 
    exact ⟨fun h => convex_hull_min h t.convex, (subset_convex_hull 𝕜 s).trans⟩

theorem convex_hull_to_cone_eq_Inf (s : Set E) : (convex_convex_hull 𝕜 s).toCone _ = Inf { t:ConvexCone 𝕜 E | s ⊆ t } :=
  (convex_hull_to_cone_is_least s).IsGlb.Inf_eq.symm

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


variable[AddCommGroupₓ E][Module ℝ E]

namespace riesz_extension

open Submodule

variable(s : ConvexCone ℝ E)(f : LinearPmap ℝ E ℝ)

-- error in Analysis.Convex.Cone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain → ℝ`, assume that `f` is nonnegative on `f.domain ∩ p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
theorem step
(nonneg : ∀ x : f.domain, «expr ∈ »((x : E), s) → «expr ≤ »(0, f x))
(dense : ∀ y, «expr∃ , »((x : f.domain), «expr ∈ »(«expr + »((x : E), y), s)))
(hdom : «expr ≠ »(f.domain, «expr⊤»())) : «expr∃ , »((g), «expr ∧ »(«expr < »(f, g), ∀
  x : g.domain, «expr ∈ »((x : E), s) → «expr ≤ »(0, g x))) :=
begin
  obtain ["⟨", ident y, ",", "-", ",", ident hy, "⟩", ":", expr «expr∃ , »((y : E)
    (h : «expr ∈ »(y, «expr⊤»())), «expr ∉ »(y, f.domain))],
  { exact [expr @set_like.exists_of_lt (submodule exprℝ() E) _ _ _ _ (lt_top_iff_ne_top.2 hdom)] },
  obtain ["⟨", ident c, ",", ident le_c, ",", ident c_le, "⟩", ":", expr «expr∃ , »((c), «expr ∧ »(∀
     x : f.domain, «expr ∈ »(«expr - »(«expr- »((x : E)), y), s) → «expr ≤ »(f x, c), ∀
     x : f.domain, «expr ∈ »(«expr + »((x : E), y), s) → «expr ≤ »(c, f x)))],
  { set [] [ident Sp] [] [":="] [expr «expr '' »(f, {x : f.domain | «expr ∈ »(«expr + »((x : E), y), s)})] [],
    set [] [ident Sn] [] [":="] [expr «expr '' »(f, {x : f.domain | «expr ∈ »(«expr - »(«expr- »((x : E)), y), s)})] [],
    suffices [] [":", expr «expr ∩ »(upper_bounds Sn, lower_bounds Sp).nonempty],
    by simpa [] [] ["only"] ["[", expr set.nonempty, ",", expr upper_bounds, ",", expr lower_bounds, ",", expr ball_image_iff, "]"] [] ["using", expr this],
    refine [expr exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (dense y)) _],
    { rcases [expr dense «expr- »(y), "with", "⟨", ident x, ",", ident hx, "⟩"],
      rw ["[", "<-", expr neg_neg x, ",", expr coe_neg, ",", "<-", expr sub_eq_add_neg, "]"] ["at", ident hx],
      exact [expr ⟨_, hx⟩] },
    rintros [ident a, "⟨", ident xn, ",", ident hxn, ",", ident rfl, "⟩", ident b, "⟨", ident xp, ",", ident hxp, ",", ident rfl, "⟩"],
    have [] [] [":=", expr s.add_mem hxp hxn],
    rw ["[", expr add_assoc, ",", expr add_sub_cancel'_right, ",", "<-", expr sub_eq_add_neg, ",", "<-", expr coe_sub, "]"] ["at", ident this],
    replace [] [] [":=", expr nonneg _ this],
    rwa ["[", expr f.map_sub, ",", expr sub_nonneg, "]"] ["at", ident this] },
  have [ident hy'] [":", expr «expr ≠ »(y, 0)] [],
  from [expr λ hy₀, hy «expr ▸ »(hy₀.symm, zero_mem _)],
  refine [expr ⟨f.sup_span_singleton y «expr- »(c) hy, _, _⟩],
  { refine [expr lt_iff_le_not_le.2 ⟨f.left_le_sup _ _, λ H, _⟩],
    replace [ident H] [] [":=", expr linear_pmap.domain_mono.monotone H],
    rw ["[", expr linear_pmap.domain_sup_span_singleton, ",", expr sup_le_iff, ",", expr span_le, ",", expr singleton_subset_iff, "]"] ["at", ident H],
    exact [expr hy H.2] },
  { rintros ["⟨", ident z, ",", ident hz, "⟩", ident hzs],
    rcases [expr mem_sup.1 hz, "with", "⟨", ident x, ",", ident hx, ",", ident y', ",", ident hy', ",", ident rfl, "⟩"],
    rcases [expr mem_span_singleton.1 hy', "with", "⟨", ident r, ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr subtype.coe_mk, "]"] [] ["at", ident hzs],
    erw ["[", expr linear_pmap.sup_span_singleton_apply_mk _ _ _ _ _ hx, ",", expr smul_neg, ",", "<-", expr sub_eq_add_neg, ",", expr sub_nonneg, "]"] [],
    rcases [expr lt_trichotomy r 0, "with", ident hr, "|", ident hr, "|", ident hr],
    { have [] [":", expr «expr ∈ »(«expr - »(«expr- »(«expr • »(«expr ⁻¹»(r), x)), y), s)] [],
      by rwa ["[", "<-", expr s.smul_mem_iff (neg_pos.2 hr), ",", expr smul_sub, ",", expr smul_neg, ",", expr neg_smul, ",", expr neg_neg, ",", expr smul_smul, ",", expr mul_inv_cancel hr.ne, ",", expr one_smul, ",", expr sub_eq_add_neg, ",", expr neg_smul, ",", expr neg_neg, "]"] [],
      replace [] [] [":=", expr le_c «expr • »(«expr ⁻¹»(r), ⟨x, hx⟩) this],
      rwa ["[", "<-", expr mul_le_mul_left (neg_pos.2 hr), ",", "<-", expr neg_mul_eq_neg_mul, ",", "<-", expr neg_mul_eq_neg_mul, ",", expr neg_le_neg_iff, ",", expr f.map_smul, ",", expr smul_eq_mul, ",", "<-", expr mul_assoc, ",", expr mul_inv_cancel hr.ne, ",", expr one_mul, "]"] ["at", ident this] },
    { subst [expr r],
      simp [] [] ["only"] ["[", expr zero_smul, ",", expr add_zero, "]"] [] ["at", ident hzs, "⊢"],
      apply [expr nonneg],
      exact [expr hzs] },
    { have [] [":", expr «expr ∈ »(«expr + »(«expr • »(«expr ⁻¹»(r), x), y), s)] [],
      by rwa ["[", "<-", expr s.smul_mem_iff hr, ",", expr smul_add, ",", expr smul_smul, ",", expr mul_inv_cancel hr.ne', ",", expr one_smul, "]"] [],
      replace [] [] [":=", expr c_le «expr • »(«expr ⁻¹»(r), ⟨x, hx⟩) this],
      rwa ["[", "<-", expr mul_le_mul_left hr, ",", expr f.map_smul, ",", expr smul_eq_mul, ",", "<-", expr mul_assoc, ",", expr mul_inv_cancel hr.ne', ",", expr one_mul, "]"] ["at", ident this] } }
end

-- error in Analysis.Convex.Cone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_top
(p : linear_pmap exprℝ() E exprℝ())
(hp_nonneg : ∀ x : p.domain, «expr ∈ »((x : E), s) → «expr ≤ »(0, p x))
(hp_dense : ∀
 y, «expr∃ , »((x : p.domain), «expr ∈ »(«expr + »((x : E), y), s))) : «expr∃ , »((q «expr ≥ » p), «expr ∧ »(«expr = »(q.domain, «expr⊤»()), ∀
  x : q.domain, «expr ∈ »((x : E), s) → «expr ≤ »(0, q x))) :=
begin
  replace [ident hp_nonneg] [":", expr «expr ∈ »(p, {p | _})] [],
  by { rw [expr mem_set_of_eq] [],
    exact [expr hp_nonneg] },
  obtain ["⟨", ident q, ",", ident hqs, ",", ident hpq, ",", ident hq, "⟩", ":=", expr zorn.zorn_nonempty_partial_order₀ _ _ _ hp_nonneg],
  { refine [expr ⟨q, hpq, _, hqs⟩],
    contrapose ["!"] [ident hq],
    rcases [expr step s q hqs _ hq, "with", "⟨", ident r, ",", ident hqr, ",", ident hr, "⟩"],
    { exact [expr ⟨r, hr, hqr.le, hqr.ne'⟩] },
    { exact [expr λ y, let ⟨x, hx⟩ := hp_dense y in ⟨of_le hpq.left x, hx⟩] } },
  { intros [ident c, ident hcs, ident c_chain, ident y, ident hy],
    clear [ident hp_nonneg, ident hp_dense, ident p],
    have [ident cne] [":", expr c.nonempty] [":=", expr ⟨y, hy⟩],
    refine [expr ⟨linear_pmap.Sup c c_chain.directed_on, _, λ _, linear_pmap.le_Sup c_chain.directed_on⟩],
    rintros ["⟨", ident x, ",", ident hx, "⟩", ident hxs],
    have [ident hdir] [":", expr directed_on ((«expr ≤ »)) «expr '' »(linear_pmap.domain, c)] [],
    from [expr directed_on_image.2 (c_chain.directed_on.mono linear_pmap.domain_mono.monotone)],
    rcases [expr (mem_Sup_of_directed (cne.image _) hdir).1 hx, "with", "⟨", "_", ",", "⟨", ident f, ",", ident hfc, ",", ident rfl, "⟩", ",", ident hfx, "⟩"],
    have [] [":", expr «expr ≤ »(f, linear_pmap.Sup c c_chain.directed_on)] [],
    from [expr linear_pmap.le_Sup _ hfc],
    convert ["<-"] [expr hcs hfc ⟨x, hfx⟩ hxs] [],
    apply [expr this.2],
    refl }
end

end riesz_extension

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p → ℝ`, assume that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then
there exists a globally defined linear function `g : E → ℝ` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem riesz_extension (s : ConvexCone ℝ E) (f : LinearPmap ℝ E ℝ) (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
  (dense : ∀ y, ∃ x : f.domain, ((x : E)+y) ∈ s) :
  ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x _ : x ∈ s, 0 ≤ g x :=
  by 
    rcases RieszExtension.exists_top s f nonneg Dense with ⟨⟨g_dom, g⟩, ⟨hpg, hfg⟩, htop, hgs⟩
    clear hpg 
    refine' ⟨g ∘ₗ «expr↑ » (LinearEquiv.ofTop _ htop).symm, _, _⟩ <;>
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.of_top_symm_apply]
    ·
      exact fun x => (hfg (Submodule.coe_mk _ _).symm).symm
    ·
      exact fun x hx => hgs ⟨x, _⟩ hx

-- error in Analysis.Convex.Cone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Hahn-Banach theorem**: if `N : E → ℝ` is a sublinear map, `f` is a linear map
defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
for all `x`. -/
theorem exists_extension_of_le_sublinear
(f : linear_pmap exprℝ() E exprℝ())
(N : E → exprℝ())
(N_hom : ∀ c : exprℝ(), «expr < »(0, c) → ∀ x, «expr = »(N «expr • »(c, x), «expr * »(c, N x)))
(N_add : ∀ x y, «expr ≤ »(N «expr + »(x, y), «expr + »(N x, N y)))
(hf : ∀
 x : f.domain, «expr ≤ »(f x, N x)) : «expr∃ , »((g : «expr →ₗ[ ] »(E, exprℝ(), exprℝ())), «expr ∧ »(∀
  x : f.domain, «expr = »(g x, f x), ∀ x, «expr ≤ »(g x, N x))) :=
begin
  let [ident s] [":", expr convex_cone exprℝ() «expr × »(E, exprℝ())] [":=", expr { carrier := {p : «expr × »(E, exprℝ()) | «expr ≤ »(N p.1, p.2)},
     smul_mem' := λ c hc p hp, calc
       «expr = »(N «expr • »(c, p.1), «expr * »(c, N p.1)) : N_hom c hc p.1
       «expr ≤ »(..., «expr * »(c, p.2)) : mul_le_mul_of_nonneg_left hp hc.le,
     add_mem' := λ x hx y hy, (N_add _ _).trans (add_le_add hx hy) }],
  obtain ["⟨", ident g, ",", ident g_eq, ",", ident g_nonneg, "⟩", ":=", expr riesz_extension s («expr- »(f).coprod (linear_map.id.to_pmap «expr⊤»())) _ _]; try { simp [] [] ["only"] ["[", expr linear_pmap.coprod_apply, ",", expr to_pmap_apply, ",", expr id_apply, ",", expr linear_pmap.neg_apply, ",", "<-", expr sub_eq_neg_add, ",", expr sub_nonneg, ",", expr subtype.coe_mk, "]"] [] ["at", "*"] },
  replace [ident g_eq] [":", expr ∀ (x : f.domain) (y : exprℝ()), «expr = »(g (x, y), «expr - »(y, f x))] [],
  { intros [ident x, ident y],
    simpa [] [] ["only"] ["[", expr subtype.coe_mk, ",", expr subtype.coe_eta, "]"] [] ["using", expr g_eq ⟨(x, y), ⟨x.2, trivial⟩⟩] },
  { refine [expr ⟨«expr- »(g.comp (inl exprℝ() E exprℝ())), _, _⟩]; simp [] [] ["only"] ["[", expr neg_apply, ",", expr inl_apply, ",", expr comp_apply, "]"] [] [],
    { intro [ident x],
      simp [] [] [] ["[", expr g_eq x 0, "]"] [] [] },
    { intro [ident x],
      have [ident A] [":", expr «expr = »((x, N x), «expr + »((x, 0), (0, N x)))] [],
      by simp [] [] [] [] [] [],
      have [ident B] [] [":=", expr g_nonneg ⟨x, N x⟩ (le_refl (N x))],
      rw ["[", expr A, ",", expr map_add, ",", "<-", expr neg_le_iff_add_nonneg', "]"] ["at", ident B],
      have [ident C] [] [":=", expr g_eq 0 (N x)],
      simp [] [] ["only"] ["[", expr submodule.coe_zero, ",", expr f.map_zero, ",", expr sub_zero, "]"] [] ["at", ident C],
      rwa ["<-", expr C] [] } },
  { exact [expr λ x hx, le_trans (hf _) hx] },
  { rintros ["⟨", ident x, ",", ident y, "⟩"],
    refine [expr ⟨⟨(0, «expr - »(N x, y)), ⟨f.domain.zero_mem, trivial⟩⟩, _⟩],
    simp [] [] ["only"] ["[", expr convex_cone.mem_mk, ",", expr mem_set_of_eq, ",", expr subtype.coe_mk, ",", expr prod.fst_add, ",", expr prod.snd_add, ",", expr zero_add, ",", expr sub_add_cancel, "]"] [] [] }
end

/-! ### The dual cone -/


section Dual

variable{H : Type _}[InnerProductSpace ℝ H](s t : Set H)

open_locale RealInnerProductSpace

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
noncomputable def Set.innerDualCone (s : Set H) : ConvexCone ℝ H :=
  { Carrier := { y | ∀ x _ : x ∈ s, 0 ≤ ⟪x, y⟫ },
    smul_mem' :=
      fun c hc y hy x hx =>
        by 
          rw [real_inner_smul_right]
          exact mul_nonneg hc.le (hy x hx),
    add_mem' :=
      fun u hu v hv x hx =>
        by 
          rw [inner_add_right]
          exact add_nonneg (hu x hx) (hv x hx) }

theorem mem_inner_dual_cone (y : H) (s : Set H) : y ∈ s.inner_dual_cone ↔ ∀ x _ : x ∈ s, 0 ≤ ⟪x, y⟫ :=
  by 
    rfl

@[simp]
theorem inner_dual_cone_empty : (∅ : Set H).innerDualCone = ⊤ :=
  ConvexCone.ext' (eq_univ_of_forall fun x y hy => False.elim (Set.not_mem_empty _ hy))

theorem inner_dual_cone_le_inner_dual_cone (h : t ⊆ s) : s.inner_dual_cone ≤ t.inner_dual_cone :=
  fun y hy x hx => hy x (h hx)

theorem pointed_inner_dual_cone : s.inner_dual_cone.pointed :=
  fun x hx =>
    by 
      rw [inner_zero_right]

end Dual

