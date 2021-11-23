import Mathbin.LinearAlgebra.Basic 
import Mathbin.LinearAlgebra.Prod

/-!
# Partially defined linear maps

A `linear_pmap R E F` is a linear map from a submodule of `E` to `F`. We define
a `semilattice_inf_bot` instance on this this, and define three operations:

* `mk_span_singleton` defines a partial linear map defined on the span of a singleton.
* `sup` takes two partial linear maps `f`, `g` that agree on the intersection of their
  domains, and returns the unique partial linear map on `f.domain ⊔ g.domain` that
  extends both `f` and `g`.
* `Sup` takes a `directed_on (≤)` set of partial linear maps, and returns the unique
  partial linear map on the `Sup` of their domains that extends all these maps.

Partially defined maps are currently used in `mathlib` to prove Hahn-Banach theorem
and its variations. Namely, `linear_pmap.Sup` implies that every chain of `linear_pmap`s
is bounded above.

Another possible use (not yet in `mathlib`) would be the theory of unbounded linear operators.
-/


open Set

universe u v w

/-- A `linear_pmap R E F` is a linear map from a submodule of `E` to `F`. -/
structure
  LinearPmap(R :
    Type u)[Ringₓ R](E : Type v)[AddCommGroupₓ E][Module R E](F : Type w)[AddCommGroupₓ F][Module R F] where
  
  domain : Submodule R E 
  toFun : domain →ₗ[R] F

variable{R :
    Type
      _}[Ringₓ
      R]{E :
    Type
      _}[AddCommGroupₓ E][Module R E]{F : Type _}[AddCommGroupₓ F][Module R F]{G : Type _}[AddCommGroupₓ G][Module R G]

namespace LinearPmap

open Submodule

instance  : CoeFun (LinearPmap R E F) fun f : LinearPmap R E F => f.domain → F :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem to_fun_eq_coe (f : LinearPmap R E F) (x : f.domain) : f.to_fun x = f x :=
  rfl

@[simp]
theorem map_zero (f : LinearPmap R E F) : f 0 = 0 :=
  f.to_fun.map_zero

theorem map_add (f : LinearPmap R E F) (x y : f.domain) : f (x+y) = f x+f y :=
  f.to_fun.map_add x y

theorem map_neg (f : LinearPmap R E F) (x : f.domain) : f (-x) = -f x :=
  f.to_fun.map_neg x

theorem map_sub (f : LinearPmap R E F) (x y : f.domain) : f (x - y) = f x - f y :=
  f.to_fun.map_sub x y

theorem map_smul (f : LinearPmap R E F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
  f.to_fun.map_smul c x

@[simp]
theorem mk_apply (p : Submodule R E) (f : p →ₗ[R] F) (x : p) : mk p f x = f x :=
  rfl

/-- The unique `linear_pmap` on `R ∙ x` that sends `x` to `y`. This version works for modules
over rings, and requires a proof of `∀ c, c • x = 0 → c • y = 0`. -/
noncomputable def mk_span_singleton' (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) : LinearPmap R E F :=
  { domain := R∙x,
    toFun :=
      have H : ∀ c₁ c₂ : R, c₁ • x = c₂ • x → c₁ • y = c₂ • y :=
        by 
          intro c₁ c₂ h 
          rw [←sub_eq_zero, ←sub_smul] at h⊢
          exact H _ h
      { toFun := fun z => Classical.some (mem_span_singleton.1 z.prop) • y,
        map_add' :=
          fun y z =>
            by 
              rw [←add_smul]
              apply H 
              simp only [add_smul, sub_smul, Classical.some_spec (mem_span_singleton.1 _)]
              apply coe_add,
        map_smul' :=
          fun c z =>
            by 
              rw [smul_smul]
              apply H 
              simp only [mul_smul, Classical.some_spec (mem_span_singleton.1 _)]
              apply coe_smul } }

@[simp]
theorem domain_mk_span_singleton (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
  (mk_span_singleton' x y H).domain = R∙x :=
  rfl

@[simp]
theorem mk_span_singleton_apply (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) (c : R) h :
  mk_span_singleton' x y H ⟨c • x, h⟩ = c • y :=
  by 
    dsimp [mk_span_singleton']
    rw [←sub_eq_zero, ←sub_smul]
    apply H 
    simp only [sub_smul, one_smul, sub_eq_zero]
    apply Classical.some_spec (mem_span_singleton.1 h)

/-- The unique `linear_pmap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings. -/
@[reducible]
noncomputable def mk_span_singleton {K E F : Type _} [DivisionRing K] [AddCommGroupₓ E] [Module K E] [AddCommGroupₓ F]
  [Module K F] (x : E) (y : F) (hx : x ≠ 0) : LinearPmap K E F :=
  mk_span_singleton' x y$
    fun c hc =>
      (smul_eq_zero.1 hc).elim
        (fun hc =>
          by 
            rw [hc, zero_smul])
        fun hx' => absurd hx' hx

/-- Projection to the first coordinate as a `linear_pmap` -/
protected def fst (p : Submodule R E) (p' : Submodule R F) : LinearPmap R (E × F) E :=
  { domain := p.prod p', toFun := (LinearMap.fst R E F).comp (p.prod p').Subtype }

@[simp]
theorem fst_apply (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') : LinearPmap.fst p p' x = (x : E × F).1 :=
  rfl

/-- Projection to the second coordinate as a `linear_pmap` -/
protected def snd (p : Submodule R E) (p' : Submodule R F) : LinearPmap R (E × F) F :=
  { domain := p.prod p', toFun := (LinearMap.snd R E F).comp (p.prod p').Subtype }

@[simp]
theorem snd_apply (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') : LinearPmap.snd p p' x = (x : E × F).2 :=
  rfl

instance  : Neg (LinearPmap R E F) :=
  ⟨fun f => ⟨f.domain, -f.to_fun⟩⟩

@[simp]
theorem neg_apply (f : LinearPmap R E F) x : (-f) x = -f x :=
  rfl

instance  : LE (LinearPmap R E F) :=
  ⟨fun f g => f.domain ≤ g.domain ∧ ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ h : (x : E) = y, f x = g y⟩

-- error in LinearAlgebra.LinearPmap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_le_of_domain_eq
{f g : linear_pmap R E F}
(hle : «expr ≤ »(f, g))
(heq : «expr = »(f.domain, g.domain)) : «expr = »(f, g) :=
begin
  rcases [expr f, "with", "⟨", ident f_dom, ",", ident f, "⟩"],
  rcases [expr g, "with", "⟨", ident g_dom, ",", ident g, "⟩"],
  change [expr «expr = »(f_dom, g_dom)] [] ["at", ident heq],
  subst [expr g_dom],
  have [] [":", expr «expr = »(f, g)] [],
  from [expr linear_map.ext (λ x, hle.2 rfl)],
  subst [expr g]
end

/-- Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule. -/
def eq_locus (f g : LinearPmap R E F) : Submodule R E :=
  { Carrier := { x | ∃ (hf : x ∈ f.domain)(hg : x ∈ g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ },
    zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩,
    add_mem' :=
      fun x y ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ =>
        ⟨add_mem _ hfx hfy, add_mem _ hgx hgy,
          by 
            erw [f.map_add ⟨x, hfx⟩ ⟨y, hfy⟩, g.map_add ⟨x, hgx⟩ ⟨y, hgy⟩, hx, hy]⟩,
    smul_mem' :=
      fun c x ⟨hfx, hgx, hx⟩ =>
        ⟨smul_mem _ c hfx, smul_mem _ c hgx,
          by 
            erw [f.map_smul c ⟨x, hfx⟩, g.map_smul c ⟨x, hgx⟩, hx]⟩ }

instance  : HasInf (LinearPmap R E F) :=
  ⟨fun f g => ⟨f.eq_locus g, f.to_fun.comp$ of_le$ fun x hx => hx.fst⟩⟩

instance  : HasBot (LinearPmap R E F) :=
  ⟨⟨⊥, 0⟩⟩

instance  : Inhabited (LinearPmap R E F) :=
  ⟨⊥⟩

instance  : OrderBot (LinearPmap R E F) :=
  { bot := ⊥,
    bot_le :=
      fun f =>
        ⟨bot_le,
          fun x y h =>
            have hx : x = 0 := Subtype.eq ((mem_bot R).1 x.2)
            have hy : y = 0 := Subtype.eq (h.symm.trans (congr_argₓ _ hx))
            by 
              rw [hx, hy, map_zero, map_zero]⟩ }

instance  : SemilatticeInfBot (LinearPmap R E F) :=
  { LinearPmap.orderBot with le := · ≤ ·, le_refl := fun f => ⟨le_reflₓ f.domain, fun x y h => Subtype.eq h ▸ rfl⟩,
    le_trans :=
      fun f g h ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
        ⟨le_transₓ fg_le gh_le,
          fun x z hxz =>
            have hxy : (x : E) = of_le fg_le x := rfl
            (fg_eq hxy).trans (gh_eq$ hxy.symm.trans hxz)⟩,
    le_antisymm := fun f g fg gf => eq_of_le_of_domain_eq fg (le_antisymmₓ fg.1 gf.1), inf := ·⊓·,
    le_inf :=
      fun f g h ⟨fg_le, fg_eq⟩ ⟨fh_le, fh_eq⟩ =>
        ⟨fun x hx =>
            ⟨fg_le hx, fh_le hx,
              by 
                refine' (fg_eq _).symm.trans (fh_eq _) <;> [exact ⟨x, hx⟩, rfl, rfl]⟩,
          fun x ⟨y, yg, hy⟩ h =>
            by 
              apply fg_eq 
              exact h⟩,
    inf_le_left :=
      fun f g =>
        ⟨fun x hx => hx.fst,
          fun x y h =>
            congr_argₓ f$
              Subtype.eq$
                by 
                  exact h⟩,
    inf_le_right :=
      fun f g =>
        ⟨fun x hx => hx.snd.fst,
          fun ⟨x, xf, xg, hx⟩ y h =>
            hx.trans$
              congr_argₓ g$
                Subtype.eq$
                  by 
                    exact h⟩ }

theorem le_of_eq_locus_ge {f g : LinearPmap R E F} (H : f.domain ≤ f.eq_locus g) : f ≤ g :=
  suffices f ≤ f⊓g from le_transₓ this inf_le_right
  ⟨H, fun x y hxy => ((inf_le_left : f⊓g ≤ f).2 hxy.symm).symm⟩

theorem domain_mono : StrictMono (@domain R _ E _ _ F _ _) :=
  fun f g hlt => lt_of_le_of_neₓ hlt.1.1$ fun heq => ne_of_ltₓ hlt$ eq_of_le_of_domain_eq (le_of_ltₓ hlt) HEq

-- error in LinearAlgebra.LinearPmap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem sup_aux
(f g : linear_pmap R E F)
(h : ∀
 (x : f.domain)
 (y : g.domain), «expr = »((x : E), y) → «expr = »(f x, g y)) : «expr∃ , »((fg : «expr →ₗ[ ] »(«expr↥ »(«expr ⊔ »(f.domain, g.domain)), R, F)), ∀
 (x : f.domain)
 (y : g.domain)
 (z), «expr = »(«expr + »((x : E), y), «expr↑ »(z)) → «expr = »(fg z, «expr + »(f x, g y))) :=
begin
  choose [] [ident x] [ident hx, ident y, ident hy, ident hxy] ["using", expr λ
   z : «expr ⊔ »(f.domain, g.domain), mem_sup.1 z.prop],
  set [] [ident fg] [] [":="] [expr λ z, «expr + »(f ⟨x z, hx z⟩, g ⟨y z, hy z⟩)] [],
  have [ident fg_eq] [":", expr ∀
   (x' : f.domain)
   (y' : g.domain)
   (z' : «expr ⊔ »(f.domain, g.domain))
   (H : «expr = »(«expr + »((x' : E), y'), z')), «expr = »(fg z', «expr + »(f x', g y'))] [],
  { intros [ident x', ident y', ident z', ident H],
    dsimp [] ["[", expr fg, "]"] [] [],
    rw ["[", expr add_comm, ",", "<-", expr sub_eq_sub_iff_add_eq_add, ",", expr eq_comm, ",", "<-", expr map_sub, ",", "<-", expr map_sub, "]"] [],
    apply [expr h],
    simp [] [] ["only"] ["[", "<-", expr eq_sub_iff_add_eq, "]"] [] ["at", ident hxy],
    simp [] [] ["only"] ["[", expr coe_sub, ",", expr coe_mk, ",", expr coe_mk, ",", expr hxy, ",", "<-", expr sub_add, ",", "<-", expr sub_sub, ",", expr sub_self, ",", expr zero_sub, ",", "<-", expr H, "]"] [] [],
    apply [expr neg_add_eq_sub] },
  refine [expr ⟨{ to_fun := fg, .. }, fg_eq⟩],
  { rintros ["⟨", ident z₁, ",", ident hz₁, "⟩", "⟨", ident z₂, ",", ident hz₂, "⟩"],
    rw ["[", "<-", expr add_assoc, ",", expr add_right_comm (f _), ",", "<-", expr map_add, ",", expr add_assoc, ",", "<-", expr map_add, "]"] [],
    apply [expr fg_eq],
    simp [] [] ["only"] ["[", expr coe_add, ",", expr coe_mk, ",", "<-", expr add_assoc, "]"] [] [],
    rw ["[", expr add_right_comm (x _), ",", expr hxy, ",", expr add_assoc, ",", expr hxy, ",", expr coe_mk, ",", expr coe_mk, "]"] [] },
  { intros [ident c, ident z],
    rw ["[", expr smul_add, ",", "<-", expr map_smul, ",", "<-", expr map_smul, "]"] [],
    apply [expr fg_eq],
    simp [] [] ["only"] ["[", expr coe_smul, ",", expr coe_mk, ",", "<-", expr smul_add, ",", expr hxy, ",", expr ring_hom.id_apply, "]"] [] [] }
end

/-- Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agrees
with `f` and `g`. -/
protected noncomputable def sup (f g : LinearPmap R E F) (h : ∀ x : f.domain y : g.domain, (x : E) = y → f x = g y) :
  LinearPmap R E F :=
  ⟨_, Classical.some (sup_aux f g h)⟩

@[simp]
theorem domain_sup (f g : LinearPmap R E F) (h : ∀ x : f.domain y : g.domain, (x : E) = y → f x = g y) :
  (f.sup g h).domain = f.domain⊔g.domain :=
  rfl

theorem sup_apply {f g : LinearPmap R E F} (H : ∀ x : f.domain y : g.domain, (x : E) = y → f x = g y) x y z
  (hz : ((«expr↑ » x : E)+«expr↑ » y) = «expr↑ » z) : f.sup g H z = f x+g y :=
  Classical.some_spec (sup_aux f g H) x y z hz

protected theorem left_le_sup (f g : LinearPmap R E F) (h : ∀ x : f.domain y : g.domain, (x : E) = y → f x = g y) :
  f ≤ f.sup g h :=
  by 
    refine' ⟨le_sup_left, fun z₁ z₂ hz => _⟩
    rw [←add_zeroₓ (f _), ←g.map_zero]
    refine' (sup_apply h _ _ _ _).symm 
    simpa

protected theorem right_le_sup (f g : LinearPmap R E F) (h : ∀ x : f.domain y : g.domain, (x : E) = y → f x = g y) :
  g ≤ f.sup g h :=
  by 
    refine' ⟨le_sup_right, fun z₁ z₂ hz => _⟩
    rw [←zero_addₓ (g _), ←f.map_zero]
    refine' (sup_apply h _ _ _ _).symm 
    simpa

protected theorem sup_le {f g h : LinearPmap R E F} (H : ∀ x : f.domain y : g.domain, (x : E) = y → f x = g y)
  (fh : f ≤ h) (gh : g ≤ h) : f.sup g H ≤ h :=
  have Hf : f ≤ f.sup g H⊓h := le_inf (f.left_le_sup g H) fh 
  have Hg : g ≤ f.sup g H⊓h := le_inf (f.right_le_sup g H) gh 
  le_of_eq_locus_ge$ sup_le Hf.1 Hg.1

-- error in LinearAlgebra.LinearPmap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Hypothesis for `linear_pmap.sup` holds, if `f.domain` is disjoint with `g.domain`. -/
theorem sup_h_of_disjoint
(f g : linear_pmap R E F)
(h : disjoint f.domain g.domain)
(x : f.domain)
(y : g.domain)
(hxy : «expr = »((x : E), y)) : «expr = »(f x, g y) :=
begin
  rw ["[", expr disjoint_def, "]"] ["at", ident h],
  have [ident hy] [":", expr «expr = »(y, 0)] [],
  from [expr subtype.eq (h y «expr ▸ »(hxy, x.2) y.2)],
  have [ident hx] [":", expr «expr = »(x, 0)] [],
  from [expr subtype.eq «expr $ »(hxy.trans, congr_arg _ hy)],
  simp [] [] [] ["[", "*", "]"] [] []
end

section 

variable{K : Type _}[DivisionRing K][Module K E][Module K F]

/-- Extend a `linear_pmap` to `f.domain ⊔ K ∙ x`. -/
noncomputable def sup_span_singleton (f : LinearPmap K E F) (x : E) (y : F) (hx : x ∉ f.domain) : LinearPmap K E F :=
  f.sup (mk_span_singleton x y fun h₀ => hx$ h₀.symm ▸ f.domain.zero_mem)$
    sup_h_of_disjoint _ _$
      by 
        simpa [disjoint_span_singleton]

@[simp]
theorem domain_sup_span_singleton (f : LinearPmap K E F) (x : E) (y : F) (hx : x ∉ f.domain) :
  (f.sup_span_singleton x y hx).domain = f.domain⊔K∙x :=
  rfl

@[simp]
theorem sup_span_singleton_apply_mk (f : LinearPmap K E F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E)
  (hx' : x' ∈ f.domain) (c : K) :
  f.sup_span_singleton x y hx ⟨x'+c • x, mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ =
    f ⟨x', hx'⟩+c • y :=
  by 
    erw [sup_apply _ ⟨x', hx'⟩ ⟨c • x, _⟩, mk_span_singleton_apply]
    rfl 
    exact mem_span_singleton.2 ⟨c, rfl⟩

end 

-- error in LinearAlgebra.LinearPmap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem Sup_aux
(c : set (linear_pmap R E F))
(hc : directed_on ((«expr ≤ »)) c) : «expr∃ , »((f : «expr →ₗ[ ] »(«expr↥ »(Sup «expr '' »(domain, c)), R, F)), «expr ∈ »((⟨_, f⟩ : linear_pmap R E F), upper_bounds c)) :=
begin
  cases [expr c.eq_empty_or_nonempty] ["with", ident ceq, ident cne],
  { subst [expr c],
    simp [] [] [] [] [] [] },
  have [ident hdir] [":", expr directed_on ((«expr ≤ »)) «expr '' »(domain, c)] [],
  from [expr directed_on_image.2 (hc.mono domain_mono.monotone)],
  have [ident P] [":", expr ∀ x : Sup «expr '' »(domain, c), {p : c // «expr ∈ »((x : E), p.val.domain)}] [],
  { rintros [ident x],
    apply [expr classical.indefinite_description],
    have [] [] [":=", expr (mem_Sup_of_directed (cne.image _) hdir).1 x.2],
    rwa ["[", expr bex_image_iff, ",", expr set_coe.exists', "]"] ["at", ident this] },
  set [] [ident f] [":", expr Sup «expr '' »(domain, c) → F] [":="] [expr λ x, (P x).val.val ⟨x, (P x).property⟩] [],
  have [ident f_eq] [":", expr ∀
   (p : c)
   (x : Sup «expr '' »(domain, c))
   (y : p.1.1)
   (hxy : «expr = »((x : E), y)), «expr = »(f x, p.1 y)] [],
  { intros [ident p, ident x, ident y, ident hxy],
    rcases [expr hc (P x).1.1 (P x).1.2 p.1 p.2, "with", "⟨", ident q, ",", ident hqc, ",", ident hxq, ",", ident hpq, "⟩"],
    refine [expr (hxq.2 _).trans (hpq.2 _).symm],
    exacts ["[", expr of_le hpq.1 y, ",", expr hxy, ",", expr rfl, "]"] },
  refine [expr ⟨{ to_fun := f, .. }, _⟩],
  { intros [ident x, ident y],
    rcases [expr hc (P x).1.1 (P x).1.2 (P y).1.1 (P y).1.2, "with", "⟨", ident p, ",", ident hpc, ",", ident hpx, ",", ident hpy, "⟩"],
    set [] [ident x'] [] [":="] [expr of_le hpx.1 ⟨x, (P x).2⟩] [],
    set [] [ident y'] [] [":="] [expr of_le hpy.1 ⟨y, (P y).2⟩] [],
    rw ["[", expr f_eq ⟨p, hpc⟩ x x' rfl, ",", expr f_eq ⟨p, hpc⟩ y y' rfl, ",", expr f_eq ⟨p, hpc⟩ «expr + »(x, y) «expr + »(x', y') rfl, ",", expr map_add, "]"] [] },
  { intros [ident c, ident x],
    simp [] [] [] ["[", expr f_eq (P x).1 «expr • »(c, x) «expr • »(c, ⟨x, (P x).2⟩) rfl, ",", "<-", expr map_smul, "]"] [] [] },
  { intros [ident p, ident hpc],
    refine [expr ⟨«expr $ »(le_Sup, mem_image_of_mem domain hpc), λ x y hxy, eq.symm _⟩],
    exact [expr f_eq ⟨p, hpc⟩ _ _ hxy.symm] }
end

/-- Glue a collection of partially defined linear maps to a linear map defined on `Sup`
of these submodules. -/
protected noncomputable def Sup (c : Set (LinearPmap R E F)) (hc : DirectedOn (· ≤ ·) c) : LinearPmap R E F :=
  ⟨_, Classical.some$ Sup_aux c hc⟩

protected theorem le_Sup {c : Set (LinearPmap R E F)} (hc : DirectedOn (· ≤ ·) c) {f : LinearPmap R E F} (hf : f ∈ c) :
  f ≤ LinearPmap.supₓ c hc :=
  Classical.some_spec (Sup_aux c hc) hf

protected theorem Sup_le {c : Set (LinearPmap R E F)} (hc : DirectedOn (· ≤ ·) c) {g : LinearPmap R E F}
  (hg : ∀ f _ : f ∈ c, f ≤ g) : LinearPmap.supₓ c hc ≤ g :=
  le_of_eq_locus_ge$
    Sup_le$
      fun _ ⟨f, hf, Eq⟩ =>
        Eq ▸
          have  : f ≤ LinearPmap.supₓ c hc⊓g := le_inf (LinearPmap.le_Sup _ hf) (hg f hf)
          this.1

end LinearPmap

namespace LinearMap

/-- Restrict a linear map to a submodule, reinterpreting the result as a `linear_pmap`. -/
def to_pmap (f : E →ₗ[R] F) (p : Submodule R E) : LinearPmap R E F :=
  ⟨p, f.comp p.subtype⟩

@[simp]
theorem to_pmap_apply (f : E →ₗ[R] F) (p : Submodule R E) (x : p) : f.to_pmap p x = f x :=
  rfl

/-- Compose a linear map with a `linear_pmap` -/
def comp_pmap (g : F →ₗ[R] G) (f : LinearPmap R E F) : LinearPmap R E G :=
  { domain := f.domain, toFun := g.comp f.to_fun }

@[simp]
theorem comp_pmap_apply (g : F →ₗ[R] G) (f : LinearPmap R E F) x : g.comp_pmap f x = g (f x) :=
  rfl

end LinearMap

namespace LinearPmap

/-- Restrict codomain of a `linear_pmap` -/
def cod_restrict (f : LinearPmap R E F) (p : Submodule R F) (H : ∀ x, f x ∈ p) : LinearPmap R E p :=
  { domain := f.domain, toFun := f.to_fun.cod_restrict p H }

/-- Compose two `linear_pmap`s -/
def comp (g : LinearPmap R F G) (f : LinearPmap R E F) (H : ∀ x : f.domain, f x ∈ g.domain) : LinearPmap R E G :=
  g.to_fun.comp_pmap$ f.cod_restrict _ H

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
def coprod (f : LinearPmap R E G) (g : LinearPmap R F G) : LinearPmap R (E × F) G :=
  { domain := f.domain.prod g.domain,
    toFun :=
      (f.comp (LinearPmap.fst f.domain g.domain)
            fun x => x.2.1).toFun+(g.comp (LinearPmap.snd f.domain g.domain) fun x => x.2.2).toFun }

@[simp]
theorem coprod_apply (f : LinearPmap R E G) (g : LinearPmap R F G) x :
  f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩+g ⟨(x : E × F).2, x.2.2⟩ :=
  rfl

end LinearPmap

