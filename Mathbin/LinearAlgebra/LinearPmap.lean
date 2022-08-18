/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Moritz Doll
-/
import Mathbin.LinearAlgebra.Basic
import Mathbin.LinearAlgebra.Prod

/-!
# Partially defined linear maps

A `linear_pmap R E F` or `E →ₗ.[R] F` is a linear map from a submodule of `E` to `F`.
We define a `semilattice_inf` with `order_bot` instance on this this, and define three operations:

* `mk_span_singleton` defines a partial linear map defined on the span of a singleton.
* `sup` takes two partial linear maps `f`, `g` that agree on the intersection of their
  domains, and returns the unique partial linear map on `f.domain ⊔ g.domain` that
  extends both `f` and `g`.
* `Sup` takes a `directed_on (≤)` set of partial linear maps, and returns the unique
  partial linear map on the `Sup` of their domains that extends all these maps.

Moreover, we define
* `linear_pmap.graph` is the graph of the partial linear map viewed as a submodule of `E × F`.

Partially defined maps are currently used in `mathlib` to prove Hahn-Banach theorem
and its variations. Namely, `linear_pmap.Sup` implies that every chain of `linear_pmap`s
is bounded above.
They are also the basis for the theory of unbounded operators.

-/


open Set

universe u v w

/-- A `linear_pmap R E F` or `E →ₗ.[R] F` is a linear map from a submodule of `E` to `F`. -/
structure LinearPmap (R : Type u) [Ringₓ R] (E : Type v) [AddCommGroupₓ E] [Module R E] (F : Type w) [AddCommGroupₓ F]
  [Module R F] where
  domain : Submodule R E
  toFun : domain →ₗ[R] F

-- mathport name: «expr →ₗ.[ ] »
notation:25 E " →ₗ.[" R:25 "] " F:0 => LinearPmap R E F

variable {R : Type _} [Ringₓ R] {E : Type _} [AddCommGroupₓ E] [Module R E] {F : Type _} [AddCommGroupₓ F] [Module R F]
  {G : Type _} [AddCommGroupₓ G] [Module R G]

namespace LinearPmap

open Submodule

instance : CoeFun (E →ₗ.[R] F) fun f : E →ₗ.[R] F => f.domain → F :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem to_fun_eq_coe (f : E →ₗ.[R] F) (x : f.domain) : f.toFun x = f x :=
  rfl

@[ext]
theorem ext {f g : E →ₗ.[R] F} (h : f.domain = g.domain)
    (h' : ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (h : (x : E) = y), f x = g y) : f = g := by
  rcases f with ⟨f_dom, f⟩
  rcases g with ⟨g_dom, g⟩
  obtain rfl : f_dom = g_dom := h
  obtain rfl : f = g := LinearMap.ext fun x => h' rfl
  rfl

@[simp]
theorem map_zero (f : E →ₗ.[R] F) : f 0 = 0 :=
  f.toFun.map_zero

theorem ext_iff {f g : E →ₗ.[R] F} :
    f = g ↔ ∃ domain_eq : f.domain = g.domain, ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (h : (x : E) = y), f x = g y :=
  ⟨fun EQ =>
    EQ ▸
      ⟨rfl, fun x y h => by
        congr
        exact_mod_cast h⟩,
    fun ⟨deq, feq⟩ => ext deq feq⟩

theorem map_add (f : E →ₗ.[R] F) (x y : f.domain) : f (x + y) = f x + f y :=
  f.toFun.map_add x y

theorem map_neg (f : E →ₗ.[R] F) (x : f.domain) : f (-x) = -f x :=
  f.toFun.map_neg x

theorem map_sub (f : E →ₗ.[R] F) (x y : f.domain) : f (x - y) = f x - f y :=
  f.toFun.map_sub x y

theorem map_smul (f : E →ₗ.[R] F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
  f.toFun.map_smul c x

@[simp]
theorem mk_apply (p : Submodule R E) (f : p →ₗ[R] F) (x : p) : mk p f x = f x :=
  rfl

/-- The unique `linear_pmap` on `R ∙ x` that sends `x` to `y`. This version works for modules
over rings, and requires a proof of `∀ c, c • x = 0 → c • y = 0`. -/
noncomputable def mkSpanSingleton' (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) : E →ₗ.[R] F where
  domain := R∙x
  toFun :=
    have H : ∀ c₁ c₂ : R, c₁ • x = c₂ • x → c₁ • y = c₂ • y := by
      intro c₁ c₂ h
      rw [← sub_eq_zero, ← sub_smul] at h⊢
      exact H _ h
    { toFun := fun z => Classical.some (mem_span_singleton.1 z.Prop) • y,
      map_add' := fun y z => by
        rw [← add_smul]
        apply H
        simp only [← add_smul, ← sub_smul, ← Classical.some_spec (mem_span_singleton.1 _)]
        apply coe_add,
      map_smul' := fun c z => by
        rw [smul_smul]
        apply H
        simp only [← mul_smul, ← Classical.some_spec (mem_span_singleton.1 _)]
        apply coe_smul }

@[simp]
theorem domain_mk_span_singleton (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
    (mkSpanSingleton' x y H).domain = R∙x :=
  rfl

@[simp]
theorem mk_span_singleton'_apply (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) (c : R) (h) :
    mkSpanSingleton' x y H ⟨c • x, h⟩ = c • y := by
  dsimp' [← mk_span_singleton']
  rw [← sub_eq_zero, ← sub_smul]
  apply H
  simp only [← sub_smul, ← one_smul, ← sub_eq_zero]
  apply Classical.some_spec (mem_span_singleton.1 h)

@[simp]
theorem mk_span_singleton'_apply_self (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) (h) :
    mkSpanSingleton' x y H ⟨x, h⟩ = y := by
  convert mk_span_singleton'_apply x y H 1 _ <;> rwa [one_smul]

/-- The unique `linear_pmap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings. -/
@[reducible]
noncomputable def mkSpanSingleton {K E F : Type _} [DivisionRing K] [AddCommGroupₓ E] [Module K E] [AddCommGroupₓ F]
    [Module K F] (x : E) (y : F) (hx : x ≠ 0) : E →ₗ.[K] F :=
  (mkSpanSingleton' x y) fun c hc =>
    (smul_eq_zero.1 hc).elim
      (fun hc => by
        rw [hc, zero_smul])
      fun hx' => absurd hx' hx

theorem mk_span_singleton_apply (K : Type _) {E F : Type _} [DivisionRing K] [AddCommGroupₓ E] [Module K E]
    [AddCommGroupₓ F] [Module K F] {x : E} (hx : x ≠ 0) (y : F) :
    mkSpanSingleton x y hx ⟨x, (Submodule.mem_span_singleton_self x : x ∈ Submodule.span K {x})⟩ = y :=
  LinearPmap.mk_span_singleton'_apply_self _ _ _ _

/-- Projection to the first coordinate as a `linear_pmap` -/
protected def fst (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] E where
  domain := p.Prod p'
  toFun := (LinearMap.fst R E F).comp (p.Prod p').Subtype

@[simp]
theorem fst_apply (p : Submodule R E) (p' : Submodule R F) (x : p.Prod p') : LinearPmap.fst p p' x = (x : E × F).1 :=
  rfl

/-- Projection to the second coordinate as a `linear_pmap` -/
protected def snd (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] F where
  domain := p.Prod p'
  toFun := (LinearMap.snd R E F).comp (p.Prod p').Subtype

@[simp]
theorem snd_apply (p : Submodule R E) (p' : Submodule R F) (x : p.Prod p') : LinearPmap.snd p p' x = (x : E × F).2 :=
  rfl

instance : Neg (E →ₗ.[R] F) :=
  ⟨fun f => ⟨f.domain, -f.toFun⟩⟩

@[simp]
theorem neg_apply (f : E →ₗ.[R] F) (x) : (-f) x = -f x :=
  rfl

instance : LE (E →ₗ.[R] F) :=
  ⟨fun f g => f.domain ≤ g.domain ∧ ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (h : (x : E) = y), f x = g y⟩

theorem eq_of_le_of_domain_eq {f g : E →ₗ.[R] F} (hle : f ≤ g) (heq : f.domain = g.domain) : f = g :=
  ext HEq hle.2

/-- Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule. -/
def eqLocus (f g : E →ₗ.[R] F) : Submodule R E where
  Carrier := { x | ∃ (hf : x ∈ f.domain)(hg : x ∈ g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' := fun x y ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ =>
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      erw [f.map_add ⟨x, hfx⟩ ⟨y, hfy⟩, g.map_add ⟨x, hgx⟩ ⟨y, hgy⟩, hx, hy]⟩
  smul_mem' := fun c x ⟨hfx, hgx, hx⟩ =>
    ⟨smul_mem _ c hfx, smul_mem _ c hgx, by
      erw [f.map_smul c ⟨x, hfx⟩, g.map_smul c ⟨x, hgx⟩, hx]⟩

instance : HasInf (E →ₗ.[R] F) :=
  ⟨fun f g => ⟨f.eqLocus g, f.toFun.comp <| of_le fun x hx => hx.fst⟩⟩

instance : HasBot (E →ₗ.[R] F) :=
  ⟨⟨⊥, 0⟩⟩

instance : Inhabited (E →ₗ.[R] F) :=
  ⟨⊥⟩

instance : SemilatticeInf (E →ₗ.[R] F) where
  le := (· ≤ ·)
  le_refl := fun f => ⟨le_reflₓ f.domain, fun x y h => Subtype.eq h ▸ rfl⟩
  le_trans := fun f g h ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
    ⟨le_transₓ fg_le gh_le, fun x z hxz =>
      have hxy : (x : E) = ofLe fg_le x := rfl
      (fg_eq hxy).trans (gh_eq <| hxy.symm.trans hxz)⟩
  le_antisymm := fun f g fg gf => eq_of_le_of_domain_eq fg (le_antisymmₓ fg.1 gf.1)
  inf := (·⊓·)
  le_inf := fun f g h ⟨fg_le, fg_eq⟩ ⟨fh_le, fh_eq⟩ =>
    ⟨fun x hx =>
      ⟨fg_le hx, fh_le hx, by
        refine' (fg_eq _).symm.trans (fh_eq _) <;> [exact ⟨x, hx⟩, rfl, rfl]⟩,
      fun x ⟨y, yg, hy⟩ h => by
      apply fg_eq
      exact h⟩
  inf_le_left := fun f g => ⟨fun x hx => hx.fst, fun x y h => congr_arg f <| Subtype.eq <| h⟩
  inf_le_right := fun f g =>
    ⟨fun x hx => hx.snd.fst, fun ⟨x, xf, xg, hx⟩ y h => hx.trans <| congr_arg g <| Subtype.eq <| h⟩

instance : OrderBot (E →ₗ.[R] F) where
  bot := ⊥
  bot_le := fun f =>
    ⟨bot_le, fun x y h => by
      have hx : x = 0 := Subtype.eq ((mem_bot R).1 x.2)
      have hy : y = 0 := Subtype.eq (h.symm.trans (congr_arg _ hx))
      rw [hx, hy, map_zero, map_zero]⟩

theorem le_of_eq_locus_ge {f g : E →ₗ.[R] F} (H : f.domain ≤ f.eqLocus g) : f ≤ g :=
  suffices f ≤ f⊓g from le_transₓ this inf_le_right
  ⟨H, fun x y hxy => ((inf_le_left : f⊓g ≤ f).2 hxy.symm).symm⟩

theorem domain_mono : StrictMono (@domain R _ E _ _ F _ _) := fun f g hlt =>
  (lt_of_le_of_neₓ hlt.1.1) fun heq => ne_of_ltₓ hlt <| eq_of_le_of_domain_eq (le_of_ltₓ hlt) HEq

private theorem sup_aux (f g : E →ₗ.[R] F) (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    ∃ fg : ↥(f.domain⊔g.domain) →ₗ[R] F, ∀ (x : f.domain) (y : g.domain) (z), (x : E) + y = ↑z → fg z = f x + g y := by
  choose x hx y hy hxy using fun z : f.domain⊔g.domain => mem_sup.1 z.Prop
  set fg := fun z => f ⟨x z, hx z⟩ + g ⟨y z, hy z⟩
  have fg_eq :
    ∀ (x' : f.domain) (y' : g.domain) (z' : f.domain⊔g.domain) (H : (x' : E) + y' = z'), fg z' = f x' + g y' := by
    intro x' y' z' H
    dsimp' [← fg]
    rw [add_commₓ, ← sub_eq_sub_iff_add_eq_add, eq_comm, ← map_sub, ← map_sub]
    apply h
    simp only [eq_sub_iff_add_eq] at hxy
    simp only [← AddSubgroupClass.coe_sub, ← coe_mk, ← coe_mk, ← hxy, sub_add, sub_sub, ← sub_self, ← zero_sub, H]
    apply neg_add_eq_sub
  refine' ⟨{ toFun := fg.. }, fg_eq⟩
  · rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    rw [← add_assocₓ, add_right_commₓ (f _), ← map_add, add_assocₓ, ← map_add]
    apply fg_eq
    simp only [← coe_add, ← coe_mk, add_assocₓ]
    rw [add_right_commₓ (x _), hxy, add_assocₓ, hxy, coe_mk, coe_mk]
    
  · intro c z
    rw [smul_add, ← map_smul, ← map_smul]
    apply fg_eq
    simp only [← coe_smul, ← coe_mk, smul_add, ← hxy, ← RingHom.id_apply]
    

/-- Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agrees
with `f` and `g`. -/
protected noncomputable def sup (f g : E →ₗ.[R] F) (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    E →ₗ.[R] F :=
  ⟨_, Classical.some (sup_aux f g h)⟩

@[simp]
theorem domain_sup (f g : E →ₗ.[R] F) (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    (f.sup g h).domain = f.domain⊔g.domain :=
  rfl

theorem sup_apply {f g : E →ₗ.[R] F} (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) (x y z)
    (hz : (↑x : E) + ↑y = ↑z) : f.sup g H z = f x + g y :=
  Classical.some_spec (sup_aux f g H) x y z hz

protected theorem left_le_sup (f g : E →ₗ.[R] F) (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    f ≤ f.sup g h := by
  refine' ⟨le_sup_left, fun z₁ z₂ hz => _⟩
  rw [← add_zeroₓ (f _), ← g.map_zero]
  refine' (sup_apply h _ _ _ _).symm
  simpa

protected theorem right_le_sup (f g : E →ₗ.[R] F) (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    g ≤ f.sup g h := by
  refine' ⟨le_sup_right, fun z₁ z₂ hz => _⟩
  rw [← zero_addₓ (g _), ← f.map_zero]
  refine' (sup_apply h _ _ _ _).symm
  simpa

protected theorem sup_le {f g h : E →ₗ.[R] F} (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y)
    (fh : f ≤ h) (gh : g ≤ h) : f.sup g H ≤ h :=
  have Hf : f ≤ f.sup g H⊓h := le_inf (f.left_le_sup g H) fh
  have Hg : g ≤ f.sup g H⊓h := le_inf (f.right_le_sup g H) gh
  le_of_eq_locus_ge <| sup_le Hf.1 Hg.1

/-- Hypothesis for `linear_pmap.sup` holds, if `f.domain` is disjoint with `g.domain`. -/
theorem sup_h_of_disjoint (f g : E →ₗ.[R] F) (h : Disjoint f.domain g.domain) (x : f.domain) (y : g.domain)
    (hxy : (x : E) = y) : f x = g y := by
  rw [disjoint_def] at h
  have hy : y = 0 := Subtype.eq (h y (hxy ▸ x.2) y.2)
  have hx : x = 0 := Subtype.eq (hxy.trans <| congr_arg _ hy)
  simp [*]

section Smul

variable {M N : Type _} [Monoidₓ M] [DistribMulAction M F] [SmulCommClass R M F]

variable [Monoidₓ N] [DistribMulAction N F] [SmulCommClass R N F]

instance : HasSmul M (E →ₗ.[R] F) :=
  ⟨fun a f => { domain := f.domain, toFun := a • f.toFun }⟩

theorem smul_apply (a : M) (f : E →ₗ.[R] F) (x : (a • f).domain) : (a • f) x = a • f x :=
  rfl

@[simp]
theorem coe_smul (a : M) (f : E →ₗ.[R] F) : ⇑(a • f) = a • f :=
  rfl

instance [SmulCommClass M N F] : SmulCommClass M N (E →ₗ.[R] F) :=
  ⟨fun a b f =>
    (ext rfl) fun x y hxy => by
      simp_rw [smul_apply, Subtype.eq hxy, smul_comm]⟩

instance [HasSmul M N] [IsScalarTower M N F] : IsScalarTower M N (E →ₗ.[R] F) :=
  ⟨fun a b f =>
    (ext rfl) fun x y hxy => by
      simp_rw [smul_apply, Subtype.eq hxy, smul_assoc]⟩

end Smul

section

variable {K : Type _} [DivisionRing K] [Module K E] [Module K F]

/-- Extend a `linear_pmap` to `f.domain ⊔ K ∙ x`. -/
noncomputable def supSpanSingleton (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) : E →ₗ.[K] F :=
  f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem) <|
    sup_h_of_disjoint _ _ <| by
      simpa [← disjoint_span_singleton]

@[simp]
theorem domain_sup_span_singleton (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    (f.supSpanSingleton x y hx).domain = f.domain⊔K∙x :=
  rfl

@[simp]
theorem sup_span_singleton_apply_mk (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E) (hx' : x' ∈ f.domain)
    (c : K) :
    f.supSpanSingleton x y hx ⟨x' + c • x, mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ =
      f ⟨x', hx'⟩ + c • y :=
  by
  erw [sup_apply _ ⟨x', hx'⟩ ⟨c • x, _⟩, mk_span_singleton'_apply]
  rfl
  exact mem_span_singleton.2 ⟨c, rfl⟩

end

private theorem Sup_aux (c : Set (E →ₗ.[R] F)) (hc : DirectedOn (· ≤ ·) c) :
    ∃ f : ↥(sup (domain '' c)) →ₗ[R] F, (⟨_, f⟩ : E →ₗ.[R] F) ∈ UpperBounds c := by
  cases' c.eq_empty_or_nonempty with ceq cne
  · subst c
    simp
    
  have hdir : DirectedOn (· ≤ ·) (domain '' c) := directed_on_image.2 (hc.mono domain_mono.monotone)
  have P : ∀ x : Sup (domain '' c), { p : c // (x : E) ∈ p.val.domain } := by
    rintro x
    apply Classical.indefiniteDescription
    have := (mem_Sup_of_directed (cne.image _) hdir).1 x.2
    rwa [bex_image_iff, SetCoe.exists'] at this
  set f : Sup (domain '' c) → F := fun x => (P x).val.val ⟨x, (P x).property⟩
  have f_eq : ∀ (p : c) (x : Sup (domain '' c)) (y : p.1.1) (hxy : (x : E) = y), f x = p.1 y := by
    intro p x y hxy
    rcases hc (P x).1.1 (P x).1.2 p.1 p.2 with ⟨q, hqc, hxq, hpq⟩
    refine' (hxq.2 _).trans (hpq.2 _).symm
    exacts[of_le hpq.1 y, hxy, rfl]
  refine' ⟨{ toFun := f.. }, _⟩
  · intro x y
    rcases hc (P x).1.1 (P x).1.2 (P y).1.1 (P y).1.2 with ⟨p, hpc, hpx, hpy⟩
    set x' := of_le hpx.1 ⟨x, (P x).2⟩
    set y' := of_le hpy.1 ⟨y, (P y).2⟩
    rw [f_eq ⟨p, hpc⟩ x x' rfl, f_eq ⟨p, hpc⟩ y y' rfl, f_eq ⟨p, hpc⟩ (x + y) (x' + y') rfl, map_add]
    
  · intro c x
    simp [← f_eq (P x).1 (c • x) (c • ⟨x, (P x).2⟩) rfl, map_smul]
    
  · intro p hpc
    refine' ⟨le_Sup <| mem_image_of_mem domain hpc, fun x y hxy => Eq.symm _⟩
    exact f_eq ⟨p, hpc⟩ _ _ hxy.symm
    

/-- Glue a collection of partially defined linear maps to a linear map defined on `Sup`
of these submodules. -/
protected noncomputable def supₓ (c : Set (E →ₗ.[R] F)) (hc : DirectedOn (· ≤ ·) c) : E →ₗ.[R] F :=
  ⟨_, Classical.some <| Sup_aux c hc⟩

protected theorem le_Sup {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {f : E →ₗ.[R] F} (hf : f ∈ c) :
    f ≤ LinearPmap.supₓ c hc :=
  Classical.some_spec (Sup_aux c hc) hf

protected theorem Sup_le {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {g : E →ₗ.[R] F}
    (hg : ∀, ∀ f ∈ c, ∀, f ≤ g) : LinearPmap.supₓ c hc ≤ g :=
  le_of_eq_locus_ge <|
    Sup_le fun _ ⟨f, hf, Eq⟩ =>
      Eq ▸
        have : f ≤ LinearPmap.supₓ c hc⊓g := le_inf (LinearPmap.le_Sup _ hf) (hg f hf)
        this.1

protected theorem Sup_apply {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {l : E →ₗ.[R] F} (hl : l ∈ c)
    (x : l.domain) : (LinearPmap.supₓ c hc) ⟨x, (LinearPmap.le_Sup hc hl).1 x.2⟩ = l x := by
  symm
  apply (Classical.some_spec (Sup_aux c hc) hl).2
  rfl

end LinearPmap

namespace LinearMap

/-- Restrict a linear map to a submodule, reinterpreting the result as a `linear_pmap`. -/
def toPmap (f : E →ₗ[R] F) (p : Submodule R E) : E →ₗ.[R] F :=
  ⟨p, f.comp p.Subtype⟩

@[simp]
theorem to_pmap_apply (f : E →ₗ[R] F) (p : Submodule R E) (x : p) : f.toPmap p x = f x :=
  rfl

/-- Compose a linear map with a `linear_pmap` -/
def compPmap (g : F →ₗ[R] G) (f : E →ₗ.[R] F) : E →ₗ.[R] G where
  domain := f.domain
  toFun := g.comp f.toFun

@[simp]
theorem comp_pmap_apply (g : F →ₗ[R] G) (f : E →ₗ.[R] F) (x) : g.compPmap f x = g (f x) :=
  rfl

end LinearMap

namespace LinearPmap

/-- Restrict codomain of a `linear_pmap` -/
def codRestrict (f : E →ₗ.[R] F) (p : Submodule R F) (H : ∀ x, f x ∈ p) : E →ₗ.[R] p where
  domain := f.domain
  toFun := f.toFun.codRestrict p H

/-- Compose two `linear_pmap`s -/
def comp (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) (H : ∀ x : f.domain, f x ∈ g.domain) : E →ₗ.[R] G :=
  g.toFun.compPmap <| f.codRestrict _ H

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
def coprod (f : E →ₗ.[R] G) (g : F →ₗ.[R] G) : E × F →ₗ.[R] G where
  domain := f.domain.Prod g.domain
  toFun :=
    (f.comp (LinearPmap.fst f.domain g.domain) fun x => x.2.1).toFun +
      (g.comp (LinearPmap.snd f.domain g.domain) fun x => x.2.2).toFun

@[simp]
theorem coprod_apply (f : E →ₗ.[R] G) (g : F →ₗ.[R] G) (x) :
    f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩ + g ⟨(x : E × F).2, x.2.2⟩ :=
  rfl

/-! ### Graph -/


section Graph

/-- The graph of a `linear_pmap` viewed as a submodule on `E × F`. -/
def graph (f : E →ₗ.[R] F) : Submodule R (E × F) :=
  f.toFun.graph.map (f.domain.Subtype.prod_map LinearMap.id)

theorem mem_graph_iff' (f : E →ₗ.[R] F) {x : E × F} : x ∈ f.graph ↔ ∃ y : f.domain, (↑y, f y) = x := by
  simp [← graph]

@[simp]
theorem mem_graph_iff (f : E →ₗ.[R] F) {x : E × F} : x ∈ f.graph ↔ ∃ y : f.domain, (↑y : E) = x.1 ∧ f y = x.2 := by
  cases x
  simp_rw [mem_graph_iff', Prod.mk.inj_iff]

/-- The tuple `(x, f x)` is contained in the graph of `f`. -/
theorem mem_graph (f : E →ₗ.[R] F) (x : domain f) : ((x : E), f x) ∈ f.graph := by
  simp

variable {M : Type _} [Monoidₓ M] [DistribMulAction M F] [SmulCommClass R M F] (y : M)

/-- The graph of `z • f` as a pushforward. -/
theorem smul_graph (f : E →ₗ.[R] F) (z : M) : (z • f).graph = f.graph.map (LinearMap.id.prod_map (z • LinearMap.id)) :=
  by
  ext x
  cases x
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPmap.smul_apply] at h
    rw [Submodule.mem_map]
    simp only [← mem_graph_iff, ← LinearMap.prod_map_apply, ← LinearMap.id_coe, ← id.def, ← LinearMap.smul_apply, ←
      Prod.mk.inj_iff, ← Prod.exists, ← exists_exists_and_eq_and]
    use x_fst, y
    simp [← hy, ← h]
    
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [← LinearMap.prod_map_apply, ← LinearMap.id_coe, ← id.def, ← LinearMap.smul_apply, ← Prod.mk.inj_iff] at h
  rw [mem_graph_iff] at hx'⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [← hy, ← hx']

/-- The graph of `-f` as a pushforward. -/
theorem neg_graph (f : E →ₗ.[R] F) : (-f).graph = f.graph.map (LinearMap.id.prod_map (-LinearMap.id)) := by
  ext
  cases x
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPmap.neg_apply] at h
    rw [Submodule.mem_map]
    simp only [← mem_graph_iff, ← LinearMap.prod_map_apply, ← LinearMap.id_coe, ← id.def, ← LinearMap.neg_apply, ←
      Prod.mk.inj_iff, ← Prod.exists, ← exists_exists_and_eq_and]
    use x_fst, y
    simp [← hy, ← h]
    
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [← LinearMap.prod_map_apply, ← LinearMap.id_coe, ← id.def, ← LinearMap.neg_apply, ← Prod.mk.inj_iff] at h
  rw [mem_graph_iff] at hx'⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [← hy, ← hx']

theorem mem_graph_snd_inj (f : E →ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') ∈ f.graph) (hy : (y, y') ∈ f.graph)
    (hxy : x = y) : x' = y' := by
  rw [mem_graph_iff] at hx hy
  rcases hx with ⟨x'', hx1, hx2⟩
  rcases hy with ⟨y'', hy1, hy2⟩
  simp only at hx1 hx2 hy1 hy2
  rw [← hx1, ← hy1, SetLike.coe_eq_coe] at hxy
  rw [← hx2, ← hy2, hxy]

theorem mem_graph_snd_inj' (f : E →ₗ.[R] F) {x y : E × F} (hx : x ∈ f.graph) (hy : y ∈ f.graph) (hxy : x.1 = y.1) :
    x.2 = y.2 := by
  cases x
  cases y
  exact f.mem_graph_snd_inj hx hy hxy

/-- The property that `f 0 = 0` in terms of the graph. -/
theorem graph_fst_eq_zero_snd (f : E →ₗ.[R] F) {x : E} {x' : F} (h : (x, x') ∈ f.graph) (hx : x = 0) : x' = 0 :=
  f.mem_graph_snd_inj h f.graph.zero_mem hx

theorem mem_domain_iff {f : E →ₗ.[R] F} {x : E} : x ∈ f.domain ↔ ∃ y : F, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · use f ⟨x, h⟩
    exact f.mem_graph ⟨x, h⟩
    
  cases' h with y h
  rw [mem_graph_iff] at h
  cases' h with x' h
  simp only at h
  rw [← h.1]
  simp

theorem image_iff {f : E →ₗ.[R] F} {x : E} {y : F} (hx : x ∈ f.domain) : y = f ⟨x, hx⟩ ↔ (x, y) ∈ f.graph := by
  rw [mem_graph_iff]
  constructor <;> intro h
  · use ⟨x, hx⟩
    simp [← h]
    
  rcases h with ⟨⟨x', hx'⟩, ⟨h1, h2⟩⟩
  simp only [← Submodule.coe_mk] at h1 h2
  simp only [h2, ← h1]

theorem mem_range_iff {f : E →ₗ.[R] F} {y : F} : y ∈ Set.Range f ↔ ∃ x : E, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · rw [Set.mem_range] at h
    rcases h with ⟨⟨x, hx⟩, h⟩
    use x
    rw [← h]
    exact f.mem_graph ⟨x, hx⟩
    
  cases' h with x h
  rw [mem_graph_iff] at h
  cases' h with x h
  rw [Set.mem_range]
  use x
  simp only at h
  rw [h.2]

theorem mem_domain_iff_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) {x : E} : x ∈ f.domain ↔ x ∈ g.domain :=
  by
  simp_rw [mem_domain_iff, h]

theorem le_of_le_graph {f g : E →ₗ.[R] F} (h : f.graph ≤ g.graph) : f ≤ g := by
  constructor
  · intro x hx
    rw [mem_domain_iff] at hx⊢
    cases' hx with y hx
    use y
    exact h hx
    
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [image_iff]
  refine' h _
  simp only [← Submodule.coe_mk] at hxy
  rw [hxy] at hx
  rw [← image_iff hx]
  simp [← hxy]

theorem eq_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) : f = g := by
  ext
  exact mem_domain_iff_of_eq_graph h
  exact (le_of_le_graph h.le).2

end Graph

end LinearPmap

namespace Submodule

section SubmoduleToLinearPmap

theorem exists_unique_from_graph {g : Submodule R (E × F)}
    (hg : ∀ {x : E × F} (hx : x ∈ g) (hx' : x.fst = 0), x.snd = 0) {a : E} (ha : a ∈ g.map (LinearMap.fst R E F)) :
    ∃! b : F, (a, b) ∈ g := by
  refine' exists_unique_of_exists_of_unique _ _
  · convert ha
    simp
    
  intro y₁ y₂ hy₁ hy₂
  have hy : ((0 : E), y₁ - y₂) ∈ g := by
    convert g.sub_mem hy₁ hy₂
    exact (sub_self _).symm
  exact
    sub_eq_zero.mp
      (hg hy
        (by
          simp ))

/-- Auxiliary definition to unfold the existential quantifier. -/
noncomputable def valFromGraph {g : Submodule R (E × F)} (hg : ∀ (x : E × F) (hx : x ∈ g) (hx' : x.fst = 0), x.snd = 0)
    {a : E} (ha : a ∈ g.map (LinearMap.fst R E F)) : F :=
  (exists_of_exists_unique (exists_unique_from_graph hg ha)).some

theorem val_from_graph_mem {g : Submodule R (E × F)} (hg : ∀ (x : E × F) (hx : x ∈ g) (hx' : x.fst = 0), x.snd = 0)
    {a : E} (ha : a ∈ g.map (LinearMap.fst R E F)) : (a, valFromGraph hg ha) ∈ g :=
  (exists_of_exists_unique (exists_unique_from_graph hg ha)).some_spec

/-- Define a `linear_pmap` from its graph. -/
noncomputable def toLinearPmap (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (hx : x ∈ g) (hx' : x.fst = 0), x.snd = 0) : E →ₗ.[R] F where
  domain := g.map (LinearMap.fst R E F)
  toFun :=
    { toFun := fun x => valFromGraph hg x.2,
      map_add' := fun v w => by
        have hadd := (g.map (LinearMap.fst R E F)).add_mem v.2 w.2
        have hvw := val_from_graph_mem hg hadd
        have hvw' := g.add_mem (val_from_graph_mem hg v.2) (val_from_graph_mem hg w.2)
        rw [Prod.mk_add_mk] at hvw'
        exact (exists_unique_from_graph hg hadd).unique hvw hvw',
      map_smul' := fun a v => by
        have hsmul := (g.map (LinearMap.fst R E F)).smul_mem a v.2
        have hav := val_from_graph_mem hg hsmul
        have hav' := g.smul_mem a (val_from_graph_mem hg v.2)
        rw [Prod.smul_mk] at hav'
        exact (exists_unique_from_graph hg hsmul).unique hav hav' }

theorem mem_graph_to_linear_pmap (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (hx : x ∈ g) (hx' : x.fst = 0), x.snd = 0) (x : g.map (LinearMap.fst R E F)) :
    (x.val, g.toLinearPmap hg x) ∈ g :=
  val_from_graph_mem hg x.2

@[simp]
theorem to_linear_pmap_graph_eq (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (hx : x ∈ g) (hx' : x.fst = 0), x.snd = 0) : (g.toLinearPmap hg).graph = g := by
  ext
  constructor <;> intro hx
  · rw [LinearPmap.mem_graph_iff] at hx
    rcases hx with ⟨y, hx1, hx2⟩
    convert g.mem_graph_to_linear_pmap hg y
    rw [Subtype.val_eq_coe]
    exact Prod.extₓ hx1.symm hx2.symm
    
  rw [LinearPmap.mem_graph_iff]
  cases x
  have hx_fst : x_fst ∈ g.map (LinearMap.fst R E F) := by
    simp only [← mem_map, ← LinearMap.fst_apply, ← Prod.exists, ← exists_and_distrib_right, ← exists_eq_right]
    exact ⟨x_snd, hx⟩
  refine' ⟨⟨x_fst, hx_fst⟩, Subtype.coe_mk x_fst hx_fst, _⟩
  exact (exists_unique_from_graph hg hx_fst).unique (val_from_graph_mem hg hx_fst) hx

end SubmoduleToLinearPmap

end Submodule

