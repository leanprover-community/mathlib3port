import Mathbin.Topology.UnitInterval 
import Mathbin.Topology.Algebra.Ordered.ProjIcc 
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Path connectedness

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `path (x y : X)` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `path.map` is the image of a path under a continuous map.
* `joined (x y : X)` means there is a path between `x` and `y`.
* `joined.some_path (h : joined x y)` selects some path between two points `x` and `y`.
* `path_component (x : X)` is the set of points joined to `x`.
* `path_connected_space X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : set X`.

* `joined_in F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `joined_in.some_path (h : joined_in F x y)` selects a path from `x` to `y` inside `F`.
* `path_component_in F (x : X)` is the set of points joined to `x` in `F`.
* `is_path_connected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.
* `loc_path_connected_space X` is a predicate class asserting that `X` is locally path-connected:
  each point has a basis of path-connected neighborhoods (we do *not* ask these to be open).

## Main theorems

* `joined` and `joined_in F` are transitive relations.

One can link the absolute and relative version in two directions, using `(univ : set X)` or the
subtype `↥F`.

* `path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X)`
* `is_path_connected_iff_path_connected_space : is_path_connected F ↔ path_connected_space ↥F`

For locally path connected spaces, we have
* `path_connected_space_iff_connected_space : path_connected_space X ↔ connected_space X`
* `is_connected_iff_is_path_connected (U_op : is_open U) : is_path_connected U ↔ is_connected U`

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `set.Icc_extend` that will extend any continuous map `γ : I → X` into a continuous map
`Icc_extend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `path.extend` that turns `γ : path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/


noncomputable theory

open_locale Classical TopologicalSpace Filter UnitInterval

open Filter Set Function UnitInterval

variable{X Y : Type _}[TopologicalSpace X][TopologicalSpace Y]{x y z : X}{ι : Type _}

/-! ### Paths -/


/-- Continuous path connecting two points `x` and `y` in a topological space -/
@[nolint has_inhabited_instance]
structure Path(x y : X) extends C(I, X) where 
  source' : to_fun 0 = x 
  target' : to_fun 1 = y

instance  : CoeFun (Path x y) fun _ => I → X :=
  ⟨fun p => p.to_fun⟩

@[ext]
protected theorem Path.ext : ∀ {γ₁ γ₂ : Path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂
| ⟨⟨x, h11⟩, h12, h13⟩, ⟨⟨x, h21⟩, h22, h23⟩, rfl => rfl

namespace Path

@[simp]
theorem coe_mk (f : I → X) h₁ h₂ h₃ : «expr⇑ » (mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl

variable(γ : Path x y)

@[continuity]
protected theorem Continuous : Continuous γ :=
  γ.continuous_to_fun

@[simp]
protected theorem source : γ 0 = x :=
  γ.source'

@[simp]
protected theorem target : γ 1 = y :=
  γ.target'

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X :=
  γ

initialize_simps_projections Path (to_continuous_map_to_fun → simps.apply, -toContinuousMap)

@[simp]
theorem coe_to_continuous_map : «expr⇑ » γ.to_continuous_map = γ :=
  rfl

/-- Any function `φ : Π (a : α), path (x a) (y a)` can be seen as a function `α × I → X`. -/
instance has_uncurry_path {X α : Type _} [TopologicalSpace X] {x y : α → X} :
  has_uncurry (∀ a : α, Path (x a) (y a)) (α × I) X :=
  ⟨fun φ p => φ p.1 p.2⟩

/-- The constant path from a point to itself -/
@[refl, simps]
def refl (x : X) : Path x x :=
  { toFun := fun t => x, continuous_to_fun := continuous_const, source' := rfl, target' := rfl }

@[simp]
theorem refl_range {a : X} : range (Path.refl a) = {a} :=
  by 
    simp [Path.refl, CoeFun.coe, coeFn]

/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps]
def symm (γ : Path x y) : Path y x :=
  { toFun := γ ∘ σ,
    continuous_to_fun :=
      by 
        continuity,
    source' :=
      by 
        simpa [-Path.target] using γ.target,
    target' :=
      by 
        simpa [-Path.source] using γ.source }

@[simp]
theorem symm_symm {γ : Path x y} : γ.symm.symm = γ :=
  by 
    ext 
    simp 

@[simp]
theorem refl_symm {a : X} : (Path.refl a).symm = Path.refl a :=
  by 
    ext 
    rfl

@[simp]
theorem symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ :=
  by 
    ext x 
    simp only [mem_range, Path.symm, CoeFun.coe, coeFn, UnitInterval.symm, SetCoe.exists, comp_app, Subtype.coe_mk,
      Subtype.val_eq_coe]
    split  <;> rintro ⟨y, hy, hxy⟩ <;> refine' ⟨1 - y, mem_iff_one_sub_mem.mp hy, _⟩ <;> convert hxy 
    simp 

/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
def extend : ℝ → X :=
  Icc_extend zero_le_one γ

/-- See Note [continuity lemma statement]. -/
theorem _root_.continuous.path_extend {γ : Y → Path x y} {f : Y → ℝ} (hγ : Continuous («expr↿ » γ))
  (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.Icc_extend hγ hf

/-- A useful special case of `continuous.path_extend`. -/
@[continuity]
theorem continuous_extend : Continuous γ.extend :=
  γ.continuous.Icc_extend'

theorem _root_.filter.tendsto.path_extend {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {l r : Y → X} {y : Y}
  {l₁ : Filter ℝ} {l₂ : Filter X} {γ : ∀ y, Path (l y) (r y)}
  (hγ : tendsto («expr↿ » γ) (𝓝 y ×ᶠ l₁.map (proj_Icc 0 1 zero_le_one)) l₂) :
  tendsto («expr↿ » fun x => (γ x).extend) (𝓝 y ×ᶠ l₁) l₂ :=
  Filter.Tendsto.Icc_extend _ hγ

theorem _root_.continuous_at.path_extend {g : Y → ℝ} {l r : Y → X} (γ : ∀ y, Path (l y) (r y)) {y : Y}
  (hγ : ContinuousAt («expr↿ » γ) (y, proj_Icc 0 1 zero_le_one (g y))) (hg : ContinuousAt g y) :
  ContinuousAt (fun i => (γ i).extend (g i)) y :=
  hγ.Icc_extend (fun x => γ x) hg

@[simp]
theorem extend_extends {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ} (ht : t ∈ (Icc 0 1 : Set ℝ)) :
  γ.extend t = γ ⟨t, ht⟩ :=
  Icc_extend_of_mem _ γ ht

theorem extend_zero : γ.extend 0 = x :=
  by 
    simp 

theorem extend_one : γ.extend 1 = y :=
  by 
    simp 

@[simp]
theorem extend_extends' {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) (t : (Icc 0 1 : Set ℝ)) :
  γ.extend t = γ t :=
  Icc_extend_coe _ γ t

@[simp]
theorem extend_range {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) : range γ.extend = range γ :=
  Icc_extend_range _ γ

theorem extend_of_le_zero {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ} (ht : t ≤ 0) :
  γ.extend t = a :=
  (Icc_extend_of_le_left _ _ ht).trans γ.source

theorem extend_of_one_le {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ} (ht : 1 ≤ t) :
  γ.extend t = b :=
  (Icc_extend_of_right_le _ _ ht).trans γ.target

@[simp]
theorem refl_extend {X : Type _} [TopologicalSpace X] {a : X} : (Path.refl a).extend = fun _ => a :=
  rfl

/-- The path obtained from a map defined on `ℝ` by restriction to the unit interval. -/
def of_line {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y :=
  { toFun := f ∘ coeₓ, continuous_to_fun := hf.comp_continuous continuous_subtype_coe Subtype.prop, source' := h₀,
    target' := h₁ }

theorem of_line_mem {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
  ∀ t, of_line hf h₀ h₁ t ∈ f '' I :=
  fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩

attribute [local simp] Iic_def

/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
def trans (γ : Path x y) (γ' : Path y z) : Path x z :=
  { toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2*t) else γ'.extend ((2*t) - 1)) ∘ coeₓ,
    continuous_to_fun :=
      by 
        refine'
          (Continuous.if_le _ _ continuous_id continuous_const
                (by 
                  normNum)).comp
            continuous_subtype_coe 
        exacts[γ.continuous_extend.comp (continuous_const.mul continuous_id),
          γ'.continuous_extend.comp ((continuous_const.mul continuous_id).sub continuous_const)],
    source' :=
      by 
        normNum,
    target' :=
      by 
        normNum }

theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
  (γ.trans γ') t =
    if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2*t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩ else
      γ' ⟨(2*t) - 1, two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by 
    splitIfs <;> rw [extend_extends]

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem trans_symm (γ : path x y) (γ' : path y z) : «expr = »((γ.trans γ').symm, γ'.symm.trans γ.symm) :=
begin
  ext [] [ident t] [],
  simp [] [] ["only"] ["[", expr trans_apply, ",", expr one_div, ",", expr symm_apply, ",", expr not_le, ",", expr comp_app, "]"] [] [],
  split_ifs [] ["with", ident h, ident h₁, ident h₂, ident h₃, ident h₄]; rw ["[", expr coe_symm_eq, "]"] ["at", ident h],
  { have [ident ht] [":", expr «expr = »((t : exprℝ()), «expr / »(1, 2))] [],
    { linarith [] [] ["[", expr unit_interval.nonneg t, ",", expr unit_interval.le_one t, "]"] },
    norm_num ["[", expr ht, "]"] [] },
  { refine [expr congr_arg _ (subtype.ext _)],
    norm_num ["[", expr sub_sub_assoc_swap, ",", expr mul_sub, "]"] [] },
  { refine [expr congr_arg _ (subtype.ext _)],
    have [ident h] [":", expr «expr = »(«expr - »(«expr - »(2, «expr * »(2, (t : exprℝ()))), 1), «expr - »(1, «expr * »(2, t)))] [],
    by linarith [] [] [],
    norm_num ["[", expr mul_sub, ",", expr h, "]"] [] },
  { exfalso,
    linarith [] [] ["[", expr unit_interval.nonneg t, ",", expr unit_interval.le_one t, "]"] }
end

@[simp]
theorem refl_trans_refl {X : Type _} [TopologicalSpace X] {a : X} : (Path.refl a).trans (Path.refl a) = Path.refl a :=
  by 
    ext 
    simp only [Path.trans, if_t_t, one_div, Path.refl_extend]
    rfl

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem trans_range
{X : Type*}
[topological_space X]
{a b c : X}
(γ₁ : path a b)
(γ₂ : path b c) : «expr = »(range (γ₁.trans γ₂), «expr ∪ »(range γ₁, range γ₂)) :=
begin
  rw [expr path.trans] [],
  apply [expr eq_of_subset_of_subset],
  { rintros [ident x, "⟨", "⟨", ident t, ",", ident ht0, ",", ident ht1, "⟩", ",", ident hxt, "⟩"],
    by_cases [expr h, ":", expr «expr ≤ »(t, «expr / »(1, 2))],
    { left,
      use ["[", expr «expr * »(2, t), ",", expr ⟨by linarith [] [] [], by linarith [] [] []⟩, "]"],
      rw ["<-", expr γ₁.extend_extends] [],
      unfold_coes ["at", ident hxt],
      simp [] [] ["only"] ["[", expr h, ",", expr comp_app, ",", expr if_true, "]"] [] ["at", ident hxt],
      exact [expr hxt] },
    { right,
      use ["[", expr «expr - »(«expr * »(2, t), 1), ",", expr ⟨by linarith [] [] [], by linarith [] [] []⟩, "]"],
      rw ["<-", expr γ₂.extend_extends] [],
      unfold_coes ["at", ident hxt],
      simp [] [] ["only"] ["[", expr h, ",", expr comp_app, ",", expr if_false, "]"] [] ["at", ident hxt],
      exact [expr hxt] } },
  { rintros [ident x, "(", "⟨", "⟨", ident t, ",", ident ht0, ",", ident ht1, "⟩", ",", ident hxt, "⟩", "|", "⟨", "⟨", ident t, ",", ident ht0, ",", ident ht1, "⟩", ",", ident hxt, "⟩", ")"],
    { use [expr ⟨«expr / »(t, 2), ⟨by linarith [] [] [], by linarith [] [] []⟩⟩],
      unfold_coes [],
      have [] [":", expr «expr ≤ »(«expr / »(t, 2), «expr / »(1, 2))] [":=", expr by linarith [] [] []],
      simp [] [] ["only"] ["[", expr this, ",", expr comp_app, ",", expr if_true, "]"] [] [],
      ring_nf [] [] [],
      rwa [expr γ₁.extend_extends] [] },
    { by_cases [expr h, ":", expr «expr = »(t, 0)],
      { use [expr ⟨«expr / »(1, 2), ⟨by linarith [] [] [], by linarith [] [] []⟩⟩],
        unfold_coes [],
        simp [] [] ["only"] ["[", expr h, ",", expr comp_app, ",", expr if_true, ",", expr le_refl, ",", expr mul_one_div_cancel (@two_ne_zero exprℝ() _ _), "]"] [] [],
        rw [expr γ₁.extend_one] [],
        rwa ["[", "<-", expr γ₂.extend_extends, ",", expr h, ",", expr γ₂.extend_zero, "]"] ["at", ident hxt] },
      { use [expr ⟨«expr / »(«expr + »(t, 1), 2), ⟨by linarith [] [] [], by linarith [] [] []⟩⟩],
        unfold_coes [],
        change [expr «expr ≠ »(t, 0)] [] ["at", ident h],
        have [ident ht0] [] [":=", expr lt_of_le_of_ne ht0 h.symm],
        have [] [":", expr «expr¬ »(«expr ≤ »(«expr / »(«expr + »(t, 1), 2), «expr / »(1, 2)))] [":=", expr by { rw [expr not_le] [],
           linarith [] [] [] }],
        simp [] [] ["only"] ["[", expr comp_app, ",", expr if_false, ",", expr this, "]"] [] [],
        ring_nf [] [] [],
        rwa [expr γ₂.extend_extends] [] } } }
end

/-- Image of a path from `x` to `y` by a continuous map -/
def map (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) : Path (f x) (f y) :=
  { toFun := f ∘ γ,
    continuous_to_fun :=
      by 
        continuity,
    source' :=
      by 
        simp ,
    target' :=
      by 
        simp  }

@[simp]
theorem map_coe (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
  (γ.map h : I → Y) = (f ∘ γ) :=
  by 
    ext t 
    rfl

@[simp]
theorem map_symm (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
  (γ.map h).symm = γ.symm.map h :=
  rfl

@[simp]
theorem map_trans (γ : Path x y) (γ' : Path y z) {Y : Type _} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
  (γ.trans γ').map h = (γ.map h).trans (γ'.map h) :=
  by 
    ext t 
    rw [trans_apply, map_coe, comp_app, trans_apply]
    splitIfs <;> rfl

@[simp]
theorem map_id (γ : Path x y) : γ.map continuous_id = γ :=
  by 
    ext 
    rfl

@[simp]
theorem map_map (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {Z : Type _} [TopologicalSpace Z] {f : X → Y}
  (hf : Continuous f) {g : Y → Z} (hg : Continuous g) : (γ.map hf).map hg = γ.map (hg.comp hf) :=
  by 
    ext 
    rfl

/-- Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y' :=
  { toFun := γ, continuous_to_fun := γ.continuous,
    source' :=
      by 
        simp [hx],
    target' :=
      by 
        simp [hy] }

@[simp]
theorem symm_cast {X : Type _} [TopologicalSpace X] {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
  (γ.cast ha hb).symm = γ.symm.cast hb ha :=
  rfl

@[simp]
theorem trans_cast {X : Type _} [TopologicalSpace X] {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂) (γ' : Path b₂ c₂)
  (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) : (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc :=
  rfl

@[simp]
theorem cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx hy : I → X) = γ :=
  rfl

@[continuity]
theorem symm_continuous_family {X ι : Type _} [TopologicalSpace X] [TopologicalSpace ι] {a b : ι → X}
  (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous («expr↿ » γ)) : Continuous («expr↿ » fun t => (γ t).symm) :=
  h.comp (continuous_id.prod_map continuous_symm)

@[continuity]
theorem continuous_uncurry_extend_of_continuous_family {X ι : Type _} [TopologicalSpace X] [TopologicalSpace ι]
  {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous («expr↿ » γ)) :
  Continuous («expr↿ » fun t => (γ t).extend) :=
  h.comp (continuous_id.prod_map continuous_proj_Icc)

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[continuity #[]]
theorem trans_continuous_family
{X ι : Type*}
[topological_space X]
[topological_space ι]
{a b c : ι → X}
(γ₁ : ∀ t : ι, path (a t) (b t))
(h₁ : continuous «expr↿ »(γ₁))
(γ₂ : ∀ t : ι, path (b t) (c t))
(h₂ : continuous «expr↿ »(γ₂)) : continuous «expr↿ »(λ t, (γ₁ t).trans (γ₂ t)) :=
begin
  have [ident h₁'] [] [":=", expr path.continuous_uncurry_extend_of_continuous_family γ₁ h₁],
  have [ident h₂'] [] [":=", expr path.continuous_uncurry_extend_of_continuous_family γ₂ h₂],
  simp [] [] ["only"] ["[", expr has_uncurry.uncurry, ",", expr has_coe_to_fun.coe, ",", expr coe_fn, ",", expr path.trans, ",", expr («expr ∘ »), "]"] [] [],
  refine [expr continuous.if_le _ _ (continuous_subtype_coe.comp continuous_snd) continuous_const _],
  { change [expr continuous «expr ∘ »(λ
      p : «expr × »(ι, exprℝ()), (γ₁ p.1).extend p.2, prod.map id (λ x, «expr * »(2, x) : exprI() → exprℝ()))] [] [],
    exact [expr h₁'.comp «expr $ »(continuous_id.prod_map, continuous_const.mul continuous_subtype_coe)] },
  { change [expr continuous «expr ∘ »(λ
      p : «expr × »(ι, exprℝ()), (γ₂ p.1).extend p.2, prod.map id (λ
      x, «expr - »(«expr * »(2, x), 1) : exprI() → exprℝ()))] [] [],
    exact [expr h₂'.comp «expr $ »(continuous_id.prod_map, (continuous_const.mul continuous_subtype_coe).sub continuous_const)] },
  { rintros [ident st, ident hst],
    simp [] [] [] ["[", expr hst, ",", expr mul_inv_cancel (@two_ne_zero exprℝ() _ _), "]"] [] [] }
end

/-! #### Truncating a path -/


-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `γ.truncate t₀ t₁` is the path which follows the path `γ` on the
  time interval `[t₀, t₁]` and stays still otherwise. -/
def truncate
{X : Type*}
[topological_space X]
{a b : X}
(γ : path a b)
(t₀ t₁ : exprℝ()) : path «expr $ »(γ.extend, min t₀ t₁) (γ.extend t₁) :=
{ to_fun := λ s, γ.extend (min (max s t₀) t₁),
  continuous_to_fun := γ.continuous_extend.comp ((continuous_subtype_coe.max continuous_const).min continuous_const),
  source' := begin
    simp [] [] ["only"] ["[", expr min_def, ",", expr max_def, "]"] [] [],
    norm_cast [],
    split_ifs [] ["with", ident h₁, ident h₂, ident h₃, ident h₄],
    { simp [] [] [] ["[", expr γ.extend_of_le_zero h₁, "]"] [] [] },
    { congr,
      linarith [] [] [] },
    { have [ident h₄] [":", expr «expr ≤ »(t₁, 0)] [":=", expr le_of_lt (by simpa [] [] [] [] [] ["using", expr h₂])],
      simp [] [] [] ["[", expr γ.extend_of_le_zero h₄, ",", expr γ.extend_of_le_zero h₁, "]"] [] [] },
    all_goals { refl }
  end,
  target' := begin
    simp [] [] ["only"] ["[", expr min_def, ",", expr max_def, "]"] [] [],
    norm_cast [],
    split_ifs [] ["with", ident h₁, ident h₂, ident h₃],
    { simp [] [] [] ["[", expr γ.extend_of_one_le h₂, "]"] [] [] },
    { refl },
    { have [ident h₄] [":", expr «expr ≤ »(1, t₀)] [":=", expr le_of_lt (by simpa [] [] [] [] [] ["using", expr h₁])],
      simp [] [] [] ["[", expr γ.extend_of_one_le h₄, ",", expr γ.extend_of_one_le (h₄.trans h₃), "]"] [] [] },
    { refl }
  end }

/-- `γ.truncate_of_le t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
  casted as a path from `γ.extend t₀` to `γ.extend t₁`. -/
def truncate_of_le {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) :
  Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast
    (by 
      rw [min_eq_leftₓ h])
    rfl

theorem truncate_range {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} :
  range (γ.truncate t₀ t₁) ⊆ range γ :=
  by 
    rw [←γ.extend_range]
    simp only [range_subset_iff, SetCoe.exists, SetCoe.forall]
    intro x hx 
    simp only [CoeFun.coe, coeFn, Path.truncate, mem_range_self]

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we
  mean the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
@[continuity]
theorem truncate_continuous_family {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
  Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : ℝ × ℝ × I → X) :=
  γ.continuous_extend.comp
    (((continuous_subtype_coe.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))

@[continuity]
theorem truncate_const_continuous_family {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) (t : ℝ) :
  Continuous («expr↿ » (γ.truncate t)) :=
  have key : Continuous (fun x => (t, x) : ℝ × I → ℝ × ℝ × I) := continuous_const.prod_mk continuous_id 
  by 
    convert γ.truncate_continuous_family.comp key

@[simp]
theorem truncate_self {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) (t : ℝ) :
  γ.truncate t t =
    (Path.refl$ γ.extend t).cast
      (by 
        rw [min_selfₓ])
      rfl :=
  by 
    ext x 
    rw [cast_coe]
    simp only [truncate, CoeFun.coe, coeFn, refl, min_def, max_def]
    splitIfs with h₁ h₂ <;> congr 
    exact le_antisymmₓ ‹_› ‹_›

@[simp]
theorem truncate_zero_zero {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
  γ.truncate 0 0 =
    (Path.refl a).cast
      (by 
        rw [min_selfₓ, γ.extend_zero])
      γ.extend_zero :=
  by 
    convert γ.truncate_self 0 <;> exact γ.extend_zero.symm

@[simp]
theorem truncate_one_one {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
  γ.truncate 1 1 =
    (Path.refl b).cast
      (by 
        rw [min_selfₓ, γ.extend_one])
      γ.extend_one :=
  by 
    convert γ.truncate_self 1 <;> exact γ.extend_one.symm

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem truncate_zero_one
{X : Type*}
[topological_space X]
{a b : X}
(γ : path a b) : «expr = »(γ.truncate 0 1, γ.cast (by simp [] [] [] ["[", expr zero_le_one, ",", expr extend_zero, "]"] [] []) (by simp [] [] [] [] [] [])) :=
begin
  ext [] [ident x] [],
  rw [expr cast_coe] [],
  have [] [":", expr «expr ∈ »(«expr↑ »(x), (Icc 0 1 : set exprℝ()))] [":=", expr x.2],
  rw ["[", expr truncate, ",", expr coe_mk, ",", expr max_eq_left this.1, ",", expr min_eq_left this.2, ",", expr extend_extends', "]"] []
end

/-! #### Reparametrising a path -/


/--
Given a path `γ` and a function `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
path defined by `γ ∘ f`.
-/
def reparam (γ : Path x y) (f : I → I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) : Path x y :=
  { toFun := γ ∘ f,
    continuous_to_fun :=
      by 
        continuity,
    source' :=
      by 
        simp [hf₀],
    target' :=
      by 
        simp [hf₁] }

@[simp]
theorem coe_to_fun (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  «expr⇑ » (γ.reparam f hfcont hf₀ hf₁) = (γ ∘ f) :=
  rfl

@[simp]
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ :=
  by 
    ext 
    rfl

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem range_reparam
(γ : path x y)
{f : exprI() → exprI()}
(hfcont : continuous f)
(hf₀ : «expr = »(f 0, 0))
(hf₁ : «expr = »(f 1, 1)) : «expr = »(range «expr⇑ »(γ.reparam f hfcont hf₀ hf₁), range γ) :=
begin
  change [expr «expr = »(range «expr ∘ »(γ, f), range γ)] [] [],
  have [] [":", expr «expr = »(range f, univ)] [],
  { rw [expr range_iff_surjective] [],
    intro [ident t],
    have [ident h₁] [":", expr continuous (Icc_extend (@zero_le_one exprℝ() _) f)] [],
    { continuity [] [] },
    have [] [] [":=", expr intermediate_value_Icc (@zero_le_one exprℝ() _) h₁.continuous_on],
    { rw ["[", expr Icc_extend_left, ",", expr Icc_extend_right, "]"] ["at", ident this],
      change [expr «expr ⊆ »(Icc (f 0) (f 1), _)] [] ["at", ident this],
      rw ["[", expr hf₀, ",", expr hf₁, "]"] ["at", ident this],
      rcases [expr this t.2, "with", "⟨", ident w, ",", ident hw₁, ",", ident hw₂, "⟩"],
      rw [expr Icc_extend_of_mem _ _ hw₁] ["at", ident hw₂],
      use ["[", expr ⟨w, hw₁⟩, ",", expr hw₂, "]"] } },
  rw ["[", expr range_comp, ",", expr this, ",", expr image_univ, "]"] []
end

theorem refl_reparam {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  (refl x).reparam f hfcont hf₀ hf₁ = refl x :=
  by 
    ext 
    simp 

end Path

/-! ### Being joined by a path -/


/-- The relation "being joined by a path". This is an equivalence relation. -/
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)

@[refl]
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩

/-- When two points are joined, choose some path from `x` to `y`. -/
def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h

@[symm]
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.some_path.symm⟩

@[trans]
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.some_path.trans hyz.some_path⟩

variable(X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def pathSetoid : Setoidₓ X :=
  { R := Joined, iseqv := mk_equivalence _ Joined.refl (fun x y => Joined.symm) fun x y z => Joined.trans }

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def ZerothHomotopy :=
  Quotientₓ (pathSetoid X)

instance  : Inhabited (ZerothHomotopy ℝ) :=
  ⟨@Quotientₓ.mk ℝ (pathSetoid ℝ) 0⟩

variable{X}

/-! ### Being joined by a path inside a set -/


/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F

variable{F : Set X}

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem joined_in.mem (h : joined_in F x y) : «expr ∧ »(«expr ∈ »(x, F), «expr ∈ »(y, F)) :=
begin
  rcases [expr h, "with", "⟨", ident γ, ",", ident γ_in, "⟩"],
  have [] [":", expr «expr ∧ »(«expr ∈ »(γ 0, F), «expr ∈ »(γ 1, F))] [],
  by { split; apply [expr γ_in] },
  simpa [] [] [] [] [] ["using", expr this]
end

theorem JoinedIn.source_mem (h : JoinedIn F x y) : x ∈ F :=
  h.mem.1

theorem JoinedIn.target_mem (h : JoinedIn F x y) : y ∈ F :=
  h.mem.2

/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.some h

theorem JoinedIn.some_path_mem (h : JoinedIn F x y) (t : I) : h.some_path t ∈ F :=
  Classical.some_spec h t

/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
theorem JoinedIn.joined_subtype (h : JoinedIn F x y) : Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{ toFun := fun t => ⟨h.some_path t, h.some_path_mem t⟩,
      continuous_to_fun :=
        by 
          continuity,
      source' :=
        by 
          simp ,
      target' :=
        by 
          simp  }⟩

theorem JoinedIn.of_line {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) (hF : f '' I ⊆ F) :
  JoinedIn F x y :=
  ⟨Path.ofLine hf h₀ h₁, fun t => hF$ Path.of_line_mem hf h₀ h₁ t⟩

theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.some_path⟩

theorem joined_in_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) : JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype,
    fun h =>
      ⟨h.some_path.map continuous_subtype_coe,
        by 
          simp ⟩⟩

@[simp]
theorem joined_in_univ : JoinedIn univ x y ↔ Joined x y :=
  by 
    simp [JoinedIn, Joined, exists_true_iff_nonempty]

theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
  ⟨h.some_path, fun t => hUV (h.some_path_mem t)⟩

theorem JoinedIn.refl (h : x ∈ F) : JoinedIn F x x :=
  ⟨Path.refl x, fun t => h⟩

@[symm]
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x :=
  by 
    cases' h.mem with hx hy 
    simp_all [joined_in_iff_joined]
    exact h.symm

theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z :=
  by 
    cases' hxy.mem with hx hy 
    cases' hyz.mem with hx hy 
    simp_all [joined_in_iff_joined]
    exact hxy.trans hyz

/-! ### Path component -/


/-- The path component of `x` is the set of points that can be joined to `x`. -/
def PathComponent (x : X) :=
  { y | Joined x y }

@[simp]
theorem mem_path_component_self (x : X) : x ∈ PathComponent x :=
  Joined.refl x

@[simp]
theorem PathComponent.nonempty (x : X) : (PathComponent x).Nonempty :=
  ⟨x, mem_path_component_self x⟩

theorem mem_path_component_of_mem (h : x ∈ PathComponent y) : y ∈ PathComponent x :=
  Joined.symm h

theorem path_component_symm : x ∈ PathComponent y ↔ y ∈ PathComponent x :=
  ⟨fun h => mem_path_component_of_mem h, fun h => mem_path_component_of_mem h⟩

theorem path_component_congr (h : x ∈ PathComponent y) : PathComponent x = PathComponent y :=
  by 
    ext z 
    split 
    ·
      intro h' 
      rw [path_component_symm]
      exact (h.trans h').symm
    ·
      intro h' 
      rw [path_component_symm] at h'⊢
      exact h'.trans h

theorem path_component_subset_component (x : X) : PathComponent x ⊆ ConnectedComponent x :=
  fun y h =>
    (is_connected_range h.some_path.continuous).subset_connected_component
      ⟨0,
        by 
          simp ⟩
      ⟨1,
        by 
          simp ⟩

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def PathComponentIn (x : X) (F : Set X) :=
  { y | JoinedIn F x y }

@[simp]
theorem path_component_in_univ (x : X) : PathComponentIn x univ = PathComponent x :=
  by 
    simp [PathComponentIn, PathComponent, JoinedIn, Joined, exists_true_iff_nonempty]

theorem Joined.mem_path_component (hyz : Joined y z) (hxy : y ∈ PathComponent x) : z ∈ PathComponent x :=
  hxy.trans hyz

/-! ### Path connected sets -/


/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def IsPathConnected (F : Set X) : Prop :=
  ∃ (x : _)(_ : x ∈ F), ∀ {y}, y ∈ F → JoinedIn F x y

theorem is_path_connected_iff_eq : IsPathConnected F ↔ ∃ (x : _)(_ : x ∈ F), PathComponentIn x F = F :=
  by 
    split  <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
    ·
      ext y 
      exact ⟨fun hy => hy.mem.2, h⟩
    ·
      intro y y_in 
      rwa [←h] at y_in

theorem IsPathConnected.joined_in (h : IsPathConnected F) : ∀ x y _ : x ∈ F _ : y ∈ F, JoinedIn F x y :=
  fun x y x_in y_in =>
    let ⟨b, b_in, hb⟩ := h
    (hb x_in).symm.trans (hb y_in)

theorem is_path_connected_iff : IsPathConnected F ↔ F.nonempty ∧ ∀ x y _ : x ∈ F _ : y ∈ F, JoinedIn F x y :=
  ⟨fun h =>
      ⟨let ⟨b, b_in, hb⟩ := h
        ⟨b, b_in⟩,
        h.joined_in⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, fun x x_in => h b x b_in x_in⟩⟩

theorem IsPathConnected.image {Y : Type _} [TopologicalSpace Y] (hF : IsPathConnected F) {f : X → Y}
  (hf : Continuous f) : IsPathConnected (f '' F) :=
  by 
    rcases hF with ⟨x, x_in, hx⟩
    use f x, mem_image_of_mem f x_in 
    rintro _ ⟨y, y_in, rfl⟩
    exact ⟨(hx y_in).somePath.map hf, fun t => ⟨_, (hx y_in).some_path_mem t, rfl⟩⟩

theorem IsPathConnected.mem_path_component (h : IsPathConnected F) (x_in : x ∈ F) (y_in : y ∈ F) :
  y ∈ PathComponent x :=
  (h.joined_in x y x_in y_in).Joined

theorem IsPathConnected.subset_path_component (h : IsPathConnected F) (x_in : x ∈ F) : F ⊆ PathComponent x :=
  fun y y_in => h.mem_path_component x_in y_in

theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V) (hUV : (U ∩ V).Nonempty) :
  IsPathConnected (U ∪ V) :=
  by 
    rcases hUV with ⟨x, xU, xV⟩
    use x, Or.inl xU 
    rintro y (yU | yV)
    ·
      exact (hU.joined_in x y xU yU).mono (subset_union_left U V)
    ·
      exact (hV.joined_in x y xV yV).mono (subset_union_right U V)

/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W ⊆ U) :
  IsPathConnected ((coeₓ : U → X) ⁻¹' W) :=
  by 
    rcases hW with ⟨x, x_in, hx⟩
    use ⟨x, hWU x_in⟩,
      by 
        simp [x_in]
    rintro ⟨y, hyU⟩ hyW 
    exact
      ⟨(hx hyW).joined_subtype.somePath.map (continuous_inclusion hWU),
        by 
          simp ⟩

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_path_connected.exists_path_through_family
{X : Type*}
[topological_space X]
{n : exprℕ()}
{s : set X}
(h : is_path_connected s)
(p : fin «expr + »(n, 1) → X)
(hp : ∀
 i, «expr ∈ »(p i, s)) : «expr∃ , »((γ : path (p 0) (p n)), «expr ∧ »(«expr ⊆ »(range γ, s), ∀
  i, «expr ∈ »(p i, range γ))) :=
begin
  let [ident p'] [":", expr exprℕ() → X] [":=", expr λ
   k, if h : «expr < »(k, «expr + »(n, 1)) then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩],
  obtain ["⟨", ident γ, ",", ident hγ, "⟩", ":", expr «expr∃ , »((γ : path (p' 0) (p' n)), «expr ∧ »(∀
     i «expr ≤ » n, «expr ∈ »(p' i, range γ), «expr ⊆ »(range γ, s)))],
  { have [ident hp'] [":", expr ∀ i «expr ≤ » n, «expr ∈ »(p' i, s)] [],
    { intros [ident i, ident hi],
      simp [] [] [] ["[", expr p', ",", expr nat.lt_succ_of_le hi, ",", expr hp, "]"] [] [] },
    clear_value [ident p'],
    clear [ident hp, ident p],
    induction [expr n] [] ["with", ident n, ident hn] [],
    { use [expr path.refl (p' 0)],
      { split,
        { rintros [ident i, ident hi],
          rw [expr nat.le_zero_iff.mp hi] [],
          exact [expr ⟨0, rfl⟩] },
        { rw [expr range_subset_iff] [],
          rintros [ident x],
          exact [expr hp' 0 (le_refl _)] } } },
    { rcases [expr hn (λ i hi, «expr $ »(hp' i, nat.le_succ_of_le hi)), "with", "⟨", ident γ₀, ",", ident hγ₀, "⟩"],
      rcases [expr h.joined_in (p' n) «expr $ »(p', «expr + »(n, 1)) (hp' n n.le_succ) «expr $ »(hp' «expr + »(n, 1), le_refl _), "with", "⟨", ident γ₁, ",", ident hγ₁, "⟩"],
      let [ident γ] [":", expr path (p' 0) «expr $ »(p', «expr + »(n, 1))] [":=", expr γ₀.trans γ₁],
      use [expr γ],
      have [ident range_eq] [":", expr «expr = »(range γ, «expr ∪ »(range γ₀, range γ₁))] [":=", expr γ₀.trans_range γ₁],
      split,
      { rintros [ident i, ident hi],
        by_cases [expr hi', ":", expr «expr ≤ »(i, n)],
        { rw [expr range_eq] [],
          left,
          exact [expr hγ₀.1 i hi'] },
        { rw ["[", expr not_le, ",", "<-", expr nat.succ_le_iff, "]"] ["at", ident hi'],
          have [] [":", expr «expr = »(i, n.succ)] [":=", expr by linarith [] [] []],
          rw [expr this] [],
          use [expr 1],
          exact [expr γ.target] } },
      { rw [expr range_eq] [],
        apply [expr union_subset hγ₀.2],
        rw [expr range_subset_iff] [],
        exact [expr hγ₁] } } },
  have [ident hpp'] [":", expr ∀ k «expr < » «expr + »(n, 1), «expr = »(p k, p' k)] [],
  { intros [ident k, ident hk],
    simp [] [] ["only"] ["[", expr p', ",", expr hk, ",", expr dif_pos, "]"] [] [],
    congr,
    ext [] [] [],
    rw [expr fin.coe_coe_of_lt hk] [],
    norm_cast [] },
  use [expr γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self)],
  simp [] [] ["only"] ["[", expr γ.cast_coe, "]"] [] [],
  refine [expr and.intro hγ.2 _],
  rintros ["⟨", ident i, ",", ident hi, "⟩"],
  convert [] [expr hγ.1 i (nat.le_of_lt_succ hi)] [],
  rw ["<-", expr hpp' i hi] [],
  congr,
  ext [] [] [],
  rw [expr fin.coe_coe_of_lt hi] [],
  norm_cast []
end

theorem IsPathConnected.exists_path_through_family' {X : Type _} [TopologicalSpace X] {n : ℕ} {s : Set X}
  (h : IsPathConnected s) (p : Finₓ (n+1) → X) (hp : ∀ i, p i ∈ s) :
  ∃ (γ : Path (p 0) (p n))(t : Finₓ (n+1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i :=
  by 
    rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
    rcases hγ with ⟨h₁, h₂⟩
    simp only [range, mem_set_of_eq] at h₂ 
    rw [range_subset_iff] at h₁ 
    choose! t ht using h₂ 
    exact ⟨γ, t, h₁, ht⟩

/-! ### Path connected spaces -/


/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
class PathConnectedSpace(X : Type _)[TopologicalSpace X] : Prop where 
  Nonempty : Nonempty X 
  Joined : ∀ x y : X, Joined x y

attribute [instance] PathConnectedSpace.nonempty

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem path_connected_space_iff_zeroth_homotopy : «expr ↔ »(path_connected_space X, «expr ∧ »(nonempty (zeroth_homotopy X), subsingleton (zeroth_homotopy X))) :=
begin
  letI [] [] [":=", expr path_setoid X],
  split,
  { introI [ident h],
    refine [expr ⟨(nonempty_quotient_iff _).mpr h.1, ⟨_⟩⟩],
    rintros ["⟨", ident x, "⟩", "⟨", ident y, "⟩"],
    exact [expr quotient.sound (path_connected_space.joined x y)] },
  { unfold [ident zeroth_homotopy] [],
    rintros ["⟨", ident h, ",", ident h', "⟩"],
    resetI,
    exact [expr ⟨(nonempty_quotient_iff _).mp h, λ
      x y, «expr $ »(quotient.exact, subsingleton.elim «expr⟦ ⟧»(x) «expr⟦ ⟧»(y))⟩] }
end

namespace PathConnectedSpace

variable[PathConnectedSpace X]

/-- Use path-connectedness to build a path between two points. -/
def some_path (x y : X) : Path x y :=
  Nonempty.some (Joined x y)

end PathConnectedSpace

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_path_connected_iff_path_connected_space : «expr ↔ »(is_path_connected F, path_connected_space F) :=
begin
  rw [expr is_path_connected_iff] [],
  split,
  { rintro ["⟨", "⟨", ident x, ",", ident x_in, "⟩", ",", ident h, "⟩"],
    refine [expr ⟨⟨⟨x, x_in⟩⟩, _⟩],
    rintros ["⟨", ident y, ",", ident y_in, "⟩", "⟨", ident z, ",", ident z_in, "⟩"],
    have [ident H] [] [":=", expr h y z y_in z_in],
    rwa [expr joined_in_iff_joined y_in z_in] ["at", ident H] },
  { rintros ["⟨", "⟨", ident x, ",", ident x_in, "⟩", ",", ident H, "⟩"],
    refine [expr ⟨⟨x, x_in⟩, λ y z y_in z_in, _⟩],
    rw [expr joined_in_iff_joined y_in z_in] [],
    apply [expr H] }
end

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem path_connected_space_iff_univ : «expr ↔ »(path_connected_space X, is_path_connected (univ : set X)) :=
begin
  split,
  { introI [ident h],
    inhabit [expr X] [],
    refine [expr ⟨default X, mem_univ _, _⟩],
    simpa [] [] [] [] [] ["using", expr path_connected_space.joined (default X)] },
  { intro [ident h],
    have [ident h'] [] [":=", expr h.joined_in],
    cases [expr h] ["with", ident x, ident h],
    exact [expr ⟨⟨x⟩, by simpa [] [] [] [] [] ["using", expr h']⟩] }
end

theorem path_connected_space_iff_eq : PathConnectedSpace X ↔ ∃ x : X, PathComponent x = univ :=
  by 
    simp [path_connected_space_iff_univ, is_path_connected_iff_eq]

instance (priority := 100)PathConnectedSpace.connected_space [PathConnectedSpace X] : ConnectedSpace X :=
  by 
    rw [connected_space_iff_connected_component]
    rcases is_path_connected_iff_eq.mp (path_connected_space_iff_univ.mp ‹_›) with ⟨x, x_in, hx⟩
    use x 
    rw [←univ_subset_iff]
    exact
      (by 
          simpa using hx :
        PathComponent x = univ) ▸
        path_component_subset_component x

namespace PathConnectedSpace

variable[PathConnectedSpace X]

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_path_through_family
{n : exprℕ()}
(p : fin «expr + »(n, 1) → X) : «expr∃ , »((γ : path (p 0) (p n)), ∀ i, «expr ∈ »(p i, range γ)) :=
begin
  have [] [":", expr is_path_connected (univ : set X)] [":=", expr path_connected_space_iff_univ.mp (by apply_instance)],
  rcases [expr this.exists_path_through_family p (λ i, true.intro), "with", "⟨", ident γ, ",", "-", ",", ident h, "⟩"],
  exact [expr ⟨γ, h⟩]
end

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_path_through_family'
{n : exprℕ()}
(p : fin «expr + »(n, 1) → X) : «expr∃ , »((γ : path (p 0) (p n))
 (t : fin «expr + »(n, 1) → exprI()), ∀ i, «expr = »(γ (t i), p i)) :=
begin
  have [] [":", expr is_path_connected (univ : set X)] [":=", expr path_connected_space_iff_univ.mp (by apply_instance)],
  rcases [expr this.exists_path_through_family' p (λ
    i, true.intro), "with", "⟨", ident γ, ",", ident t, ",", "-", ",", ident h, "⟩"],
  exact [expr ⟨γ, t, h⟩]
end

end PathConnectedSpace

/-! ### Locally path connected spaces -/


/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class LocPathConnectedSpace(X : Type _)[TopologicalSpace X] : Prop where 
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id

export LocPathConnectedSpace(path_connected_basis)

theorem loc_path_connected_of_bases {p : ι → Prop} {s : X → ι → Set X} (h : ∀ x, (𝓝 x).HasBasis p (s x))
  (h' : ∀ x i, p i → IsPathConnected (s x i)) : LocPathConnectedSpace X :=
  by 
    constructor 
    intro x 
    apply (h x).to_has_basis
    ·
      intro i pi 
      exact
        ⟨s x i, ⟨(h x).mem_of_mem pi, h' x i pi⟩,
          by 
            rfl⟩
    ·
      rintro U ⟨U_in, hU⟩
      rcases(h x).mem_iff.mp U_in with ⟨i, pi, hi⟩
      tauto

theorem path_connected_space_iff_connected_space [LocPathConnectedSpace X] : PathConnectedSpace X ↔ ConnectedSpace X :=
  by 
    split 
    ·
      intro h 
      infer_instance
    ·
      intro hX 
      inhabit X 
      let x₀ := default X 
      rw [path_connected_space_iff_eq]
      use x₀ 
      refine'
        eq_univ_of_nonempty_clopen
          (by 
            simp )
          ⟨_, _⟩
      ·
        rw [is_open_iff_mem_nhds]
        intro y y_in 
        rcases(path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
        apply mem_of_superset U_in 
        rw [←path_component_congr y_in]
        exact hU.subset_path_component (mem_of_mem_nhds U_in)
      ·
        rw [is_closed_iff_nhds]
        intro y H 
        rcases(path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
        rcases H U U_in with ⟨z, hz, hz'⟩
        exact (hU.joined_in z y hz$ mem_of_mem_nhds U_in).Joined.mem_path_component hz'

theorem path_connected_subset_basis [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
  (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s ∧ s ⊆ U) id :=
  (path_connected_basis x).has_basis_self_subset (IsOpen.mem_nhds h hx)

theorem loc_path_connected_of_is_open [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U) : LocPathConnectedSpace U :=
  ⟨by 
      rintro ⟨x, x_in⟩
      rw [nhds_subtype_eq_comap]
      constructor 
      intro V 
      rw [(has_basis.comap (coeₓ : U → X) (path_connected_subset_basis h x_in)).mem_iff]
      split 
      ·
        rintro ⟨W, ⟨W_in, hW, hWU⟩, hWV⟩
        exact ⟨coeₓ ⁻¹' W, ⟨⟨preimage_mem_comap W_in, hW.preimage_coe hWU⟩, hWV⟩⟩
      ·
        rintro ⟨W, ⟨W_in, hW⟩, hWV⟩
        refine'
          ⟨coeₓ '' W,
            ⟨Filter.image_coe_mem_of_mem_comap (IsOpen.mem_nhds h x_in) W_in, hW.image continuous_subtype_coe,
              Subtype.coe_image_subset U W⟩,
            _⟩
        rintro x ⟨y, ⟨y_in, hy⟩⟩
        rw [←Subtype.coe_injective hy]
        tauto⟩

-- error in Topology.PathConnected: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open.is_connected_iff_is_path_connected
[loc_path_connected_space X]
{U : set X}
(U_op : is_open U) : «expr ↔ »(is_path_connected U, is_connected U) :=
begin
  rw ["[", expr is_connected_iff_connected_space, ",", expr is_path_connected_iff_path_connected_space, "]"] [],
  haveI [] [] [":=", expr loc_path_connected_of_is_open U_op],
  exact [expr path_connected_space_iff_connected_space]
end

