import Mathbin.Analysis.NormedSpace.Basic 
import Mathbin.Analysis.SpecificLimits 
import Mathbin.Topology.Sequences

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory of `semi_normed_group_hom` and we specialize to `normed_group_hom` when needed.
-/


noncomputable theory

open_locale Nnreal BigOperators

/-- A morphism of seminormed abelian groups is a bounded group homomorphism. -/
structure NormedGroupHom(V W : Type _)[SemiNormedGroup V][SemiNormedGroup W] where 
  toFun : V → W 
  map_add' : ∀ v₁ v₂, to_fun (v₁+v₂) = to_fun v₁+to_fun v₂ 
  bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C*∥v∥

namespace AddMonoidHom

variable{V W : Type _}[SemiNormedGroup V][SemiNormedGroup W]{f g : NormedGroupHom V W}

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_group_hom'` for a version that uses `ℝ≥0` for the bound. -/
def mk_normed_group_hom (f : V →+ W) (C : ℝ) (h : ∀ v, ∥f v∥ ≤ C*∥v∥) : NormedGroupHom V W :=
  { f with bound' := ⟨C, h⟩ }

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_group_hom` for a version that uses `ℝ` for the bound. -/
def mk_normed_group_hom' (f : V →+ W) (C :  ℝ≥0 ) (hC : ∀ x, nnnorm (f x) ≤ C*nnnorm x) : NormedGroupHom V W :=
  { f with bound' := ⟨C, hC⟩ }

end AddMonoidHom

theorem exists_pos_bound_of_bound {V W : Type _} [SemiNormedGroup V] [SemiNormedGroup W] {f : V → W} (M : ℝ)
  (h : ∀ x, ∥f x∥ ≤ M*∥x∥) : ∃ N, 0 < N ∧ ∀ x, ∥f x∥ ≤ N*∥x∥ :=
  ⟨max M 1, lt_of_lt_of_leₓ zero_lt_one (le_max_rightₓ _ _),
    fun x =>
      calc ∥f x∥ ≤ M*∥x∥ := h x 
        _ ≤ max M 1*∥x∥ := mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (norm_nonneg _)
        ⟩

namespace NormedGroupHom

variable{V V₁ V₂ V₃ : Type _}

variable[SemiNormedGroup V][SemiNormedGroup V₁][SemiNormedGroup V₂][SemiNormedGroup V₃]

variable{f g : NormedGroupHom V₁ V₂}

instance  : CoeFun (NormedGroupHom V₁ V₂) fun _ => V₁ → V₂ :=
  ⟨NormedGroupHom.toFun⟩

initialize_simps_projections NormedGroupHom (toFun → apply)

theorem coe_inj (H : (f : V₁ → V₂) = g) : f = g :=
  by 
    cases f <;> cases g <;> congr <;> exact funext H

theorem coe_injective : @Function.Injective (NormedGroupHom V₁ V₂) (V₁ → V₂) coeFn :=
  by 
    apply coe_inj

theorem coe_inj_iff : f = g ↔ (f : V₁ → V₂) = g :=
  ⟨congr_argₓ _, coe_inj⟩

@[ext]
theorem ext (H : ∀ x, f x = g x) : f = g :=
  coe_inj$ funext H

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  ⟨by 
      rintro rfl x <;> rfl,
    ext⟩

variable(f g)

@[simp]
theorem to_fun_eq_coe : f.to_fun = f :=
  rfl

@[simp]
theorem coe_mk f h₁ h₂ h₃ : «expr⇑ » (⟨f, h₁, h₂, h₃⟩ : NormedGroupHom V₁ V₂) = f :=
  rfl

@[simp]
theorem coe_mk_normed_group_hom (f : V₁ →+ V₂) C hC : «expr⇑ » (f.mk_normed_group_hom C hC) = f :=
  rfl

@[simp]
theorem coe_mk_normed_group_hom' (f : V₁ →+ V₂) C hC : «expr⇑ » (f.mk_normed_group_hom' C hC) = f :=
  rfl

/-- The group homomorphism underlying a bounded group homomorphism. -/
def to_add_monoid_hom (f : NormedGroupHom V₁ V₂) : V₁ →+ V₂ :=
  AddMonoidHom.mk' f f.map_add'

@[simp]
theorem coe_to_add_monoid_hom : «expr⇑ » f.to_add_monoid_hom = f :=
  rfl

theorem to_add_monoid_hom_injective : Function.Injective (@NormedGroupHom.toAddMonoidHom V₁ V₂ _ _) :=
  fun f g h =>
    coe_inj$
      show «expr⇑ » f.to_add_monoid_hom = g by 
        rw [h]
        rfl

@[simp]
theorem mk_to_add_monoid_hom f h₁ h₂ : (⟨f, h₁, h₂⟩ : NormedGroupHom V₁ V₂).toAddMonoidHom = AddMonoidHom.mk' f h₁ :=
  rfl

@[simp]
theorem map_zero : f 0 = 0 :=
  f.to_add_monoid_hom.map_zero

@[simp]
theorem map_add x y : f (x+y) = f x+f y :=
  f.to_add_monoid_hom.map_add _ _

@[simp]
theorem map_sum {ι : Type _} (v : ι → V₁) (s : Finset ι) : f (∑i in s, v i) = ∑i in s, f (v i) :=
  f.to_add_monoid_hom.map_sum _ _

@[simp]
theorem map_sub x y : f (x - y) = f x - f y :=
  f.to_add_monoid_hom.map_sub _ _

@[simp]
theorem map_neg x : f (-x) = -f x :=
  f.to_add_monoid_hom.map_neg _

theorem bound : ∃ C, 0 < C ∧ ∀ x, ∥f x∥ ≤ C*∥x∥ :=
  let ⟨C, hC⟩ := f.bound' 
  exists_pos_bound_of_bound _ hC

theorem antilipschitz_of_norm_ge {K :  ℝ≥0 } (h : ∀ x, ∥x∥ ≤ K*∥f x∥) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist$
    fun x y =>
      by 
        simpa only [dist_eq_norm, f.map_sub] using h (x - y)

/-- A normed group hom is surjective on the subgroup `K` with constant `C` if every element
`x` of `K` has a preimage whose norm is bounded above by `C*∥x∥`. This is a more
abstract version of `f` having a right inverse defined on `K` with operator norm
at most `C`. -/
def surjective_on_with (f : NormedGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : ℝ) : Prop :=
  ∀ h _ : h ∈ K, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥

theorem surjective_on_with.mono {f : NormedGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : ℝ}
  (h : f.surjective_on_with K C) (H : C ≤ C') : f.surjective_on_with K C' :=
  by 
    intro k k_in 
    rcases h k k_in with ⟨g, rfl, hg⟩
    use g, rfl 
    byCases' Hg : ∥f g∥ = 0
    ·
      simpa [Hg] using hg
    ·
      exact hg.trans ((mul_le_mul_right$ (Ne.symm Hg).le_iff_lt.mp (norm_nonneg _)).mpr H)

theorem surjective_on_with.exists_pos {f : NormedGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
  (h : f.surjective_on_with K C) : ∃ (C' : _)(_ : C' > 0), f.surjective_on_with K C' :=
  by 
    refine' ⟨|C|+1, _, _⟩
    ·
      linarith [abs_nonneg C]
    ·
      apply h.mono 
      linarith [le_abs_self C]

theorem surjective_on_with.surj_on {f : NormedGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
  (h : f.surjective_on_with K C) : Set.SurjOn f Set.Univ K :=
  fun x hx => (h x hx).imp$ fun a ⟨ha, _⟩ => ⟨Set.mem_univ _, ha⟩

/-! ### The operator norm -/


/-- The operator norm of a seminormed group homomorphism is the inf of all its bounds. -/
def op_norm (f : NormedGroupHom V₁ V₂) :=
  Inf { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ }

instance has_op_norm : HasNorm (NormedGroupHom V₁ V₂) :=
  ⟨op_norm⟩

theorem norm_def : ∥f∥ = Inf { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ } :=
  rfl

theorem bounds_nonempty {f : NormedGroupHom V₁ V₂} : ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_ltₓ hMp, hMb⟩

theorem bounds_bdd_below {f : NormedGroupHom V₁ V₂} : BddBelow { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem op_norm_nonneg : 0 ≤ ∥f∥ :=
  le_cInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

-- error in Analysis.Normed.Group.Hom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm (x : V₁) : «expr ≤ »(«expr∥ ∥»(f x), «expr * »(«expr∥ ∥»(f), «expr∥ ∥»(x))) :=
begin
  obtain ["⟨", ident C, ",", ident Cpos, ",", ident hC, "⟩", ":=", expr f.bound],
  replace [ident hC] [] [":=", expr hC x],
  by_cases [expr h, ":", expr «expr = »(«expr∥ ∥»(x), 0)],
  { rwa ["[", expr h, ",", expr mul_zero, "]"] ["at", "⊢", ident hC] },
  have [ident hlt] [":", expr «expr < »(0, «expr∥ ∥»(x))] [":=", expr lt_of_le_of_ne (norm_nonneg x) (ne.symm h)],
  exact [expr (div_le_iff hlt).mp (le_cInf bounds_nonempty (λ
     (c)
     ⟨_, hc⟩, «expr $ »((div_le_iff hlt).mpr, by { apply [expr hc] })))]
end

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥*c :=
  le_transₓ (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

theorem le_of_op_norm_le {c : ℝ} (h : ∥f∥ ≤ c) (x : V₁) : ∥f x∥ ≤ c*∥x∥ :=
  (f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : LipschitzWith ⟨∥f∥, op_norm_nonneg f⟩ f :=
  LipschitzWith.of_dist_le_mul$
    fun x y =>
      by 
        rw [dist_eq_norm, dist_eq_norm, ←map_sub]
        apply le_op_norm

protected theorem UniformContinuous (f : NormedGroupHom V₁ V₂) : UniformContinuous f :=
  f.lipschitz.uniform_continuous

@[continuity]
protected theorem Continuous (f : NormedGroupHom V₁ V₂) : Continuous f :=
  f.uniform_continuous.continuous

theorem ratio_le_op_norm (x : V₁) : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem op_norm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M*∥x∥) : ∥f∥ ≤ M :=
  cInf_le bounds_bdd_below ⟨hMp, hM⟩

theorem op_norm_eq_of_bounds {M : ℝ} (M_nonneg : 0 ≤ M) (h_above : ∀ x, ∥f x∥ ≤ M*∥x∥)
  (h_below : ∀ N _ : N ≥ 0, (∀ x, ∥f x∥ ≤ N*∥x∥) → M ≤ N) : ∥f∥ = M :=
  le_antisymmₓ (f.op_norm_le_bound M_nonneg h_above)
    ((le_cInf_iff NormedGroupHom.bounds_bdd_below ⟨M, M_nonneg, h_above⟩).mpr$
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

theorem op_norm_le_of_lipschitz {f : NormedGroupHom V₁ V₂} {K :  ℝ≥0 } (hf : LipschitzWith K f) : ∥f∥ ≤ K :=
  f.op_norm_le_bound K.2$
    fun x =>
      by 
        simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

/-- If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`mk_normed_group_hom`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem mk_normed_group_hom_norm_le (f : V₁ →+ V₂) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) :
  ∥f.mk_normed_group_hom C h∥ ≤ C :=
  op_norm_le_bound _ hC h

/-- If a bounded group homomorphism map is constructed from a group homomorphism
via the constructor `mk_normed_group_hom`, then its norm is bounded by the bound
given to the constructor or zero if this bound is negative. -/
theorem mk_normed_group_hom_norm_le' (f : V₁ →+ V₂) {C : ℝ} (h : ∀ x, ∥f x∥ ≤ C*∥x∥) :
  ∥f.mk_normed_group_hom C h∥ ≤ max C 0 :=
  op_norm_le_bound _ (le_max_rightₓ _ _)$
    fun x => (h x).trans$ mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (norm_nonneg x)

alias mk_normed_group_hom_norm_le ← AddMonoidHom.mk_normed_group_hom_norm_le

alias mk_normed_group_hom_norm_le' ← AddMonoidHom.mk_normed_group_hom_norm_le'

/-! ### Addition of normed group homs -/


/-- Addition of normed group homs. -/
instance  : Add (NormedGroupHom V₁ V₂) :=
  ⟨fun f g =>
      (f.to_add_monoid_hom+g.to_add_monoid_hom).mkNormedGroupHom (∥f∥+∥g∥)$
        fun v =>
          calc ∥f v+g v∥ ≤ ∥f v∥+∥g v∥ := norm_add_le _ _ 
            _ ≤ (∥f∥*∥v∥)+∥g∥*∥v∥ := add_le_add (le_op_norm f v) (le_op_norm g v)
            _ = (∥f∥+∥g∥)*∥v∥ :=
            by 
              rw [add_mulₓ]
            ⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f+g∥ ≤ ∥f∥+∥g∥ :=
  mk_normed_group_hom_norm_le _ (add_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

/--
Terms containing `@has_add.add (has_coe_to_fun.F ...) pi.has_add`
seem to cause leanchecker to [crash due to an out-of-memory
condition](https://github.com/leanprover-community/lean/issues/543).
As a workaround, we add a type annotation: `(f + g : V₁ → V₂)`
-/
library_note "addition on function coercions"

@[simp]
theorem coe_add (f g : NormedGroupHom V₁ V₂) : «expr⇑ » (f+g) = (f+g : V₁ → V₂) :=
  rfl

@[simp]
theorem add_apply (f g : NormedGroupHom V₁ V₂) (v : V₁) : (f+g : NormedGroupHom V₁ V₂) v = f v+g v :=
  rfl

/-! ### The zero normed group hom -/


instance  : HasZero (NormedGroupHom V₁ V₂) :=
  ⟨(0 : V₁ →+ V₂).mkNormedGroupHom 0
      (by 
        simp )⟩

instance  : Inhabited (NormedGroupHom V₁ V₂) :=
  ⟨0⟩

/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ∥(0 : NormedGroupHom V₁ V₂)∥ = 0 :=
  le_antisymmₓ
    (cInf_le bounds_bdd_below
      ⟨ge_of_eq rfl,
        fun _ =>
          le_of_eqₓ
            (by 
              rw [zero_mul]
              exact norm_zero)⟩)
    (op_norm_nonneg _)

/-- For normed groups, an operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff {V₁ V₂ : Type _} [NormedGroup V₁] [NormedGroup V₂] {f : NormedGroupHom V₁ V₂} :
  ∥f∥ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ext
        fun x =>
          norm_le_zero_iff.1
            (calc _ ≤ ∥f∥*∥x∥ := le_op_norm _ _ 
              _ = _ :=
              by 
                rw [hn, zero_mul]
              ))
    fun hf =>
      by 
        rw [hf, op_norm_zero]

@[simp]
theorem coe_zero : «expr⇑ » (0 : NormedGroupHom V₁ V₂) = (0 : V₁ → V₂) :=
  rfl

@[simp]
theorem zero_apply (v : V₁) : (0 : NormedGroupHom V₁ V₂) v = 0 :=
  rfl

variable{f g}

/-! ### The identity normed group hom -/


variable(V)

/-- The identity as a continuous normed group hom. -/
@[simps]
def id : NormedGroupHom V V :=
  (AddMonoidHom.id V).mkNormedGroupHom 1
    (by 
      simp [le_reflₓ])

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the norm of every
element vanishes, where it is `0`. (Since we are working with seminorms this can happen even if the
space is non-trivial.) It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ∥(id V : NormedGroupHom V V)∥ ≤ 1 :=
  op_norm_le_bound _ zero_le_one
    fun x =>
      by 
        simp 

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : V, ∥x∥ ≠ 0) : ∥id V∥ = 1 :=
  le_antisymmₓ (norm_id_le V)$
    let ⟨x, hx⟩ := h 
    have  := (id V).ratio_le_op_norm x 
    by 
      rwa [id_apply, div_self hx] at this

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
theorem norm_id {V : Type _} [NormedGroup V] [Nontrivial V] : ∥id V∥ = 1 :=
  by 
    refine' norm_id_of_nontrivial_seminorm V _ 
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact ⟨x, ne_of_gtₓ (norm_pos_iff.2 hx)⟩

theorem coe_id : (NormedGroupHom.id V : V → V) = (_root_.id : V → V) :=
  rfl

/-! ### The negation of a normed group hom -/


/-- Opposite of a normed group hom. -/
instance  : Neg (NormedGroupHom V₁ V₂) :=
  ⟨fun f =>
      (-f.to_add_monoid_hom).mkNormedGroupHom ∥f∥
        fun v =>
          by 
            simp [le_op_norm f v]⟩

@[simp]
theorem coe_neg (f : NormedGroupHom V₁ V₂) : «expr⇑ » (-f) = (-f : V₁ → V₂) :=
  rfl

@[simp]
theorem neg_apply (f : NormedGroupHom V₁ V₂) (v : V₁) : (-f : NormedGroupHom V₁ V₂) v = -f v :=
  rfl

theorem op_norm_neg (f : NormedGroupHom V₁ V₂) : ∥-f∥ = ∥f∥ :=
  by 
    simp only [norm_def, coe_neg, norm_neg, Pi.neg_apply]

/-! ### Subtraction of normed group homs -/


/-- Subtraction of normed group homs. -/
instance  : Sub (NormedGroupHom V₁ V₂) :=
  ⟨fun f g =>
      { f.to_add_monoid_hom - g.to_add_monoid_hom with
        bound' :=
          by 
            simp only [AddMonoidHom.sub_apply, AddMonoidHom.to_fun_eq_coe, sub_eq_add_neg]
            exact (f+-g).bound' }⟩

@[simp]
theorem coe_sub (f g : NormedGroupHom V₁ V₂) : «expr⇑ » (f - g) = (f - g : V₁ → V₂) :=
  rfl

@[simp]
theorem sub_apply (f g : NormedGroupHom V₁ V₂) (v : V₁) : (f - g : NormedGroupHom V₁ V₂) v = f v - g v :=
  rfl

/-! ### Normed group structure on normed group homs -/


/-- Homs between two given normed groups form a commutative additive group. -/
instance  : AddCommGroupₓ (NormedGroupHom V₁ V₂) :=
  coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) fun _ _ => rfl

/-- Normed group homomorphisms themselves form a seminormed group with respect to
    the operator norm. -/
instance to_semi_normed_group : SemiNormedGroup (NormedGroupHom V₁ V₂) :=
  SemiNormedGroup.ofCore _ ⟨op_norm_zero, op_norm_add_le, op_norm_neg⟩

/-- Normed group homomorphisms themselves form a normed group with respect to
    the operator norm. -/
instance to_normed_group {V₁ V₂ : Type _} [NormedGroup V₁] [NormedGroup V₂] : NormedGroup (NormedGroupHom V₁ V₂) :=
  NormedGroup.ofCore _ ⟨fun f => op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

/-- Coercion of a `normed_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn` -/
@[simps]
def coe_fn_add_hom : NormedGroupHom V₁ V₂ →+ V₁ → V₂ :=
  { toFun := coeFn, map_zero' := coe_zero, map_add' := coe_add }

@[simp]
theorem coe_sum {ι : Type _} (s : Finset ι) (f : ι → NormedGroupHom V₁ V₂) : «expr⇑ » (∑i in s, f i) = ∑i in s, f i :=
  (coe_fn_add_hom : _ →+ V₁ → V₂).map_sum f s

theorem sum_apply {ι : Type _} (s : Finset ι) (f : ι → NormedGroupHom V₁ V₂) (v : V₁) :
  (∑i in s, f i) v = ∑i in s, f i v :=
  by 
    simp only [coe_sum, Finset.sum_apply]

/-! ### Composition of normed group homs -/


/-- The composition of continuous normed group homs. -/
@[simps]
protected def comp (g : NormedGroupHom V₂ V₃) (f : NormedGroupHom V₁ V₂) : NormedGroupHom V₁ V₃ :=
  (g.to_add_monoid_hom.comp f.to_add_monoid_hom).mkNormedGroupHom (∥g∥*∥f∥)$
    fun v =>
      calc ∥g (f v)∥ ≤ ∥g∥*∥f v∥ := le_op_norm _ _ 
        _ ≤ ∥g∥*∥f∥*∥v∥ := mul_le_mul_of_nonneg_left (le_op_norm _ _) (op_norm_nonneg _)
        _ = (∥g∥*∥f∥)*∥v∥ :=
        by 
          rw [mul_assocₓ]
        

theorem norm_comp_le (g : NormedGroupHom V₂ V₃) (f : NormedGroupHom V₁ V₂) : ∥g.comp f∥ ≤ ∥g∥*∥f∥ :=
  mk_normed_group_hom_norm_le _ (mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

theorem norm_comp_le_of_le {g : NormedGroupHom V₂ V₃} {C₁ C₂ : ℝ} (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
  ∥g.comp f∥ ≤ C₂*C₁ :=
  le_transₓ (norm_comp_le g f)$ mul_le_mul hg hf (norm_nonneg _) (le_transₓ (norm_nonneg _) hg)

theorem norm_comp_le_of_le' {g : NormedGroupHom V₂ V₃} (C₁ C₂ C₃ : ℝ) (h : C₃ = C₂*C₁) (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
  ∥g.comp f∥ ≤ C₃ :=
  by 
    rw [h]
    exact norm_comp_le_of_le hg hf

/-- Composition of normed groups hom as an additive group morphism. -/
def comp_hom : NormedGroupHom V₂ V₃ →+ NormedGroupHom V₁ V₂ →+ NormedGroupHom V₁ V₃ :=
  AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by 
          intros 
          ext 
          exact g.map_add _ _))
    (by 
      intros 
      ext 
      simp only [comp_apply, Pi.add_apply, Function.comp_app, AddMonoidHom.add_apply, AddMonoidHom.mk'_apply, coe_add])

@[simp]
theorem comp_zero (f : NormedGroupHom V₂ V₃) : f.comp (0 : NormedGroupHom V₁ V₂) = 0 :=
  by 
    ext 
    exact f.map_zero

@[simp]
theorem zero_comp (f : NormedGroupHom V₁ V₂) : (0 : NormedGroupHom V₂ V₃).comp f = 0 :=
  by 
    ext 
    rfl

theorem comp_assoc {V₄ : Type _} [SemiNormedGroup V₄] (h : NormedGroupHom V₃ V₄) (g : NormedGroupHom V₂ V₃)
  (f : NormedGroupHom V₁ V₂) : (h.comp g).comp f = h.comp (g.comp f) :=
  by 
    ext 
    rfl

theorem coe_comp (f : NormedGroupHom V₁ V₂) (g : NormedGroupHom V₂ V₃) :
  (g.comp f : V₁ → V₃) = ((g : V₂ → V₃) ∘ (f : V₁ → V₂)) :=
  rfl

end NormedGroupHom

namespace NormedGroupHom

variable{V W V₁ V₂ V₃ : Type _}

variable[SemiNormedGroup V][SemiNormedGroup W][SemiNormedGroup V₁][SemiNormedGroup V₂][SemiNormedGroup V₃]

/-- The inclusion of an `add_subgroup`, as bounded group homomorphism. -/
@[simps]
def incl (s : AddSubgroup V) : NormedGroupHom s V :=
  { toFun := (coeₓ : s → V), map_add' := fun v w => AddSubgroup.coe_add _ _ _,
    bound' :=
      ⟨1,
        fun v =>
          by 
            rw [one_mulₓ]
            rfl⟩ }

theorem norm_incl {V' : AddSubgroup V} (x : V') : ∥incl _ x∥ = ∥x∥ :=
  rfl

/-!### Kernel -/


section Kernels

variable(f : NormedGroupHom V₁ V₂)(g : NormedGroupHom V₂ V₃)

/-- The kernel of a bounded group homomorphism. Naturally endowed with a
`semi_normed_group` instance. -/
def ker : AddSubgroup V₁ :=
  f.to_add_monoid_hom.ker

theorem mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 :=
  by 
    erw [f.to_add_monoid_hom.mem_ker]
    rfl

/-- Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
    the corestriction of `f` to the kernel of `g`. -/
@[simps]
def ker.lift (h : g.comp f = 0) : NormedGroupHom V₁ g.ker :=
  { toFun :=
      fun v =>
        ⟨f v,
          by 
            erw [g.mem_ker]
            show (g.comp f) v = 0
            rw [h]
            rfl⟩,
    map_add' :=
      fun v w =>
        by 
          simp only [map_add]
          rfl,
    bound' := f.bound' }

@[simp]
theorem ker.incl_comp_lift (h : g.comp f = 0) : (incl g.ker).comp (ker.lift f g h) = f :=
  by 
    ext 
    rfl

@[simp]
theorem ker_zero : (0 : NormedGroupHom V₁ V₂).ker = ⊤ :=
  by 
    ext 
    simp [mem_ker]

theorem coe_ker : (f.ker : Set V₁) = (f : V₁ → V₂) ⁻¹' {0} :=
  rfl

theorem is_closed_ker {V₂ : Type _} [NormedGroup V₂] (f : NormedGroupHom V₁ V₂) : IsClosed (f.ker : Set V₁) :=
  f.coe_ker ▸ IsClosed.preimage f.continuous (T1Space.t1 0)

end Kernels

/-! ### Range -/


section Range

variable(f : NormedGroupHom V₁ V₂)(g : NormedGroupHom V₂ V₃)

/-- The image of a bounded group homomorphism. Naturally endowed with a
`semi_normed_group` instance. -/
def range : AddSubgroup V₂ :=
  f.to_add_monoid_hom.range

theorem mem_range (v : V₂) : v ∈ f.range ↔ ∃ w, f w = v :=
  by 
    rw [range, AddMonoidHom.mem_range]
    rfl

@[simp]
theorem mem_range_self (v : V₁) : f v ∈ f.range :=
  ⟨v, rfl⟩

theorem comp_range : (g.comp f).range = AddSubgroup.map g.to_add_monoid_hom f.range :=
  by 
    erw [AddMonoidHom.map_range]
    rfl

theorem incl_range (s : AddSubgroup V₁) : (incl s).range = s :=
  by 
    ext x 
    exact
      ⟨fun ⟨y, hy⟩ =>
          by 
            rw [←hy] <;> simp ,
        fun hx =>
          ⟨⟨x, hx⟩,
            by 
              simp ⟩⟩

@[simp]
theorem range_comp_incl_top : (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range :=
  by 
    simpa [comp_range, incl_range, ←AddMonoidHom.range_eq_map]

end Range

variable{f : NormedGroupHom V W}

/-- A `normed_group_hom` is *norm-nonincreasing* if `∥f v∥ ≤ ∥v∥` for all `v`. -/
def norm_noninc (f : NormedGroupHom V W) : Prop :=
  ∀ v, ∥f v∥ ≤ ∥v∥

namespace NormNoninc

theorem norm_noninc_iff_norm_le_one : f.norm_noninc ↔ ∥f∥ ≤ 1 :=
  by 
    refine' ⟨fun h => _, fun h => fun v => _⟩
    ·
      refine' op_norm_le_bound _ zero_le_one fun v => _ 
      simpa [one_mulₓ] using h v
    ·
      simpa using le_of_op_norm_le f h v

theorem zero : (0 : NormedGroupHom V₁ V₂).NormNoninc :=
  fun v =>
    by 
      simp 

theorem id : (id V).NormNoninc :=
  fun v => le_rfl

theorem comp {g : NormedGroupHom V₂ V₃} {f : NormedGroupHom V₁ V₂} (hg : g.norm_noninc) (hf : f.norm_noninc) :
  (g.comp f).NormNoninc :=
  fun v => (hg (f v)).trans (hf v)

@[simp]
theorem neg_iff {f : NormedGroupHom V₁ V₂} : (-f).NormNoninc ↔ f.norm_noninc :=
  ⟨fun h x =>
      by 
        simpa using h x,
    fun h x => (norm_neg (f x)).le.trans (h x)⟩

end NormNoninc

section Isometry

theorem isometry_iff_norm (f : NormedGroupHom V W) : Isometry f ↔ ∀ v, ∥f v∥ = ∥v∥ :=
  AddMonoidHom.isometry_iff_norm f.to_add_monoid_hom

theorem isometry_of_norm (f : NormedGroupHom V W) (hf : ∀ v, ∥f v∥ = ∥v∥) : Isometry f :=
  f.isometry_iff_norm.mpr hf

theorem norm_eq_of_isometry {f : NormedGroupHom V W} (hf : Isometry f) (v : V) : ∥f v∥ = ∥v∥ :=
  f.isometry_iff_norm.mp hf v

theorem isometry_id : @Isometry V V _ _ (id V) :=
  isometry_id

theorem isometry_comp {g : NormedGroupHom V₂ V₃} {f : NormedGroupHom V₁ V₂} (hg : Isometry g) (hf : Isometry f) :
  Isometry (g.comp f) :=
  hg.comp hf

theorem norm_noninc_of_isometry (hf : Isometry f) : f.norm_noninc :=
  fun v => le_of_eqₓ$ norm_eq_of_isometry hf v

end Isometry

variable{W₁ W₂ W₃ : Type _}[SemiNormedGroup W₁][SemiNormedGroup W₂][SemiNormedGroup W₃]

variable(f)(g : NormedGroupHom V W)

variable{f₁ g₁ : NormedGroupHom V₁ W₁}

variable{f₂ g₂ : NormedGroupHom V₂ W₂}

variable{f₃ g₃ : NormedGroupHom V₃ W₃}

/-- The equalizer of two morphisms `f g : normed_group_hom V W`. -/
def equalizer :=
  (f - g).ker

namespace Equalizer

/-- The inclusion of `f.equalizer g` as a `normed_group_hom`. -/
def ι : NormedGroupHom (f.equalizer g) V :=
  incl _

theorem comp_ι_eq : f.comp (ι f g) = g.comp (ι f g) :=
  by 
    ext 
    rw [comp_apply, comp_apply, ←sub_eq_zero, ←NormedGroupHom.sub_apply]
    exact x.2

variable{f g}

/-- If `φ : normed_group_hom V₁ V` is such that `f.comp φ = g.comp φ`, the induced morphism
`normed_group_hom V₁ (f.equalizer g)`. -/
@[simps]
def lift (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) : NormedGroupHom V₁ (f.equalizer g) :=
  { toFun :=
      fun v =>
        ⟨φ v,
          show (f - g) (φ v) = 0 by 
            rw [NormedGroupHom.sub_apply, sub_eq_zero, ←comp_apply, h, comp_apply]⟩,
    map_add' :=
      fun v₁ v₂ =>
        by 
          ext 
          simp only [map_add, AddSubgroup.coe_add, Subtype.coe_mk],
    bound' :=
      by 
        obtain ⟨C, C_pos, hC⟩ := φ.bound 
        exact ⟨C, hC⟩ }

@[simp]
theorem ι_comp_lift (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) : (ι _ _).comp (lift φ h) = φ :=
  by 
    ext 
    rfl

/-- The lifting property of the equalizer as an equivalence. -/
@[simps]
def lift_equiv : { φ : NormedGroupHom V₁ V // f.comp φ = g.comp φ } ≃ NormedGroupHom V₁ (f.equalizer g) :=
  { toFun := fun φ => lift φ φ.prop,
    invFun :=
      fun ψ =>
        ⟨(ι f g).comp ψ,
          by 
            rw [←comp_assoc, ←comp_assoc, comp_ι_eq]⟩,
    left_inv :=
      fun φ =>
        by 
          simp ,
    right_inv :=
      fun ψ =>
        by 
          ext 
          rfl }

/-- Given `φ : normed_group_hom V₁ V₂` and `ψ : normed_group_hom W₁ W₂` such that
`ψ.comp f₁ = f₂.comp φ` and `ψ.comp g₁ = g₂.comp φ`, the induced morphism
`normed_group_hom (f₁.equalizer g₁) (f₂.equalizer g₂)`. -/
def map (φ : NormedGroupHom V₁ V₂) (ψ : NormedGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
  (hg : ψ.comp g₁ = g₂.comp φ) : NormedGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
  lift (φ.comp$ ι _ _)$
    by 
      simp only [←comp_assoc, ←hf, ←hg]
      simp only [comp_assoc, comp_ι_eq]

variable{φ : NormedGroupHom V₁ V₂}{ψ : NormedGroupHom W₁ W₂}

variable{φ' : NormedGroupHom V₂ V₃}{ψ' : NormedGroupHom W₂ W₃}

@[simp]
theorem ι_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
  (ι f₂ g₂).comp (map φ ψ hf hg) = φ.comp (ι _ _) :=
  ι_comp_lift _ _

@[simp]
theorem map_id : map (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁) :=
  by 
    ext 
    rfl

theorem comm_sq₂ (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ') :
  (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ) :=
  by 
    rw [comp_assoc, hf, ←comp_assoc, hf', comp_assoc]

theorem map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ')
  (hg' : ψ'.comp g₂ = g₃.comp φ') :
  (map φ' ψ' hf' hg').comp (map φ ψ hf hg) = map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
  by 
    ext 
    rfl

theorem ι_norm_noninc : (ι f g).NormNoninc :=
  fun v => le_rfl

/-- The lifting of a norm nonincreasing morphism is norm nonincreasing. -/
theorem lift_norm_noninc (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.norm_noninc) :
  (lift φ h).NormNoninc :=
  hφ

/-- If `φ` satisfies `∥φ∥ ≤ C`, then the same is true for the lifted morphism. -/
theorem norm_lift_le (φ : NormedGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : ℝ) (hφ : ∥φ∥ ≤ C) : ∥lift φ h∥ ≤ C :=
  hφ

theorem map_norm_noninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (hφ : φ.norm_noninc) :
  (map φ ψ hf hg).NormNoninc :=
  lift_norm_noninc _ _$ hφ.comp ι_norm_noninc

theorem norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C : ℝ) (hφ : ∥φ.comp (ι f₁ g₁)∥ ≤ C) :
  ∥map φ ψ hf hg∥ ≤ C :=
  norm_lift_le _ _ _ hφ

end Equalizer

end NormedGroupHom

section ControlledClosure

open Filter Finset

open_locale TopologicalSpace

variable{G : Type _}[NormedGroup G][CompleteSpace G]

variable{H : Type _}[NormedGroup H]

-- error in Analysis.Normed.Group.Hom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given `f : normed_group_hom G H` for some complete `G` and a subgroup `K` of `H`, if every
element `x` of `K` has a preimage under `f` whose norm is at most `C*∥x∥` then the same holds for
elements of the (topological) closure of `K` with constant `C+ε` instead of `C`, for any
positive `ε`.
-/
theorem controlled_closure_of_complete
{f : normed_group_hom G H}
{K : add_subgroup H}
{C ε : exprℝ()}
(hC : «expr < »(0, C))
(hε : «expr < »(0, ε))
(hyp : f.surjective_on_with K C) : f.surjective_on_with K.topological_closure «expr + »(C, ε) :=
begin
  rintros ["(", ident h, ":", expr H, ")", "(", ident h_in, ":", expr «expr ∈ »(h, K.topological_closure), ")"],
  by_cases [expr hyp_h, ":", expr «expr = »(h, 0)],
  { rw [expr hyp_h] [],
    use [expr 0],
    simp [] [] [] [] [] [] },
  set [] [ident b] [":", expr exprℕ() → exprℝ()] [":="] [expr λ
   i, «expr / »(«expr * »(«expr ^ »(«expr / »(1, 2), i), «expr / »(«expr * »(ε, «expr∥ ∥»(h)), 2)), C)] [],
  have [ident b_pos] [":", expr ∀ i, «expr < »(0, b i)] [],
  { intro [ident i],
    field_simp [] ["[", expr b, ",", expr hC, "]"] [] [],
    exact [expr div_pos (mul_pos hε (norm_pos_iff.mpr hyp_h)) (mul_pos (by norm_num [] [] : «expr < »((0 : exprℝ()), «expr * »(«expr ^ »(2, i), 2))) hC)] },
  obtain ["⟨", ident v, ":", expr exprℕ() → H, ",", ident lim_v, ":", expr tendsto (λ
    n : exprℕ(), «expr∑ in , »((k), range «expr + »(n, 1), v k)) at_top (expr𝓝() h), ",", ident v_in, ":", expr ∀
   n, «expr ∈ »(v n, K), ",", ident hv₀, ":", expr «expr < »(«expr∥ ∥»(«expr - »(v 0, h)), b 0), ",", ident hv, ":", expr ∀
   n «expr > » 0, «expr < »(«expr∥ ∥»(v n), b n), "⟩", ":=", expr controlled_sum_of_mem_closure h_in b_pos],
  have [] [":", expr ∀
   n, «expr∃ , »((m' : G), «expr ∧ »(«expr = »(f m', v n), «expr ≤ »(«expr∥ ∥»(m'), «expr * »(C, «expr∥ ∥»(v n)))))] [":=", expr λ
   n : exprℕ(), hyp (v n) (v_in n)],
  choose [] [ident u] [ident hu, ident hnorm_u] ["using", expr this],
  set [] [ident s] [":", expr exprℕ() → G] [":="] [expr λ n, «expr∑ in , »((k), range «expr + »(n, 1), u k)] [],
  have [] [":", expr cauchy_seq s] [],
  { apply [expr normed_group.cauchy_series_of_le_geometric'' (by norm_num [] []) one_half_lt_one],
    rintro [ident n, "(", ident hn, ":", expr «expr ≥ »(n, 1), ")"],
    calc
      «expr ≤ »(«expr∥ ∥»(u n), «expr * »(C, «expr∥ ∥»(v n))) : hnorm_u n
      «expr ≤ »(..., «expr * »(C, b n)) : mul_le_mul_of_nonneg_left «expr $ »(hv _, nat.succ_le_iff.mp hn).le hC.le
      «expr = »(..., «expr * »(«expr ^ »(«expr / »(1, 2), n), «expr / »(«expr * »(ε, «expr∥ ∥»(h)), 2))) : by simp [] [] [] ["[", expr b, ",", expr mul_div_cancel' _ hC.ne.symm, "]"] [] []
      «expr = »(..., «expr * »(«expr / »(«expr * »(ε, «expr∥ ∥»(h)), 2), «expr ^ »(«expr / »(1, 2), n))) : mul_comm _ _ },
  obtain ["⟨", ident g, ":", expr G, ",", ident hg, "⟩", ":=", expr cauchy_seq_tendsto_of_complete this],
  refine [expr ⟨g, _, _⟩],
  { have [] [":", expr «expr = »(«expr ∘ »(f, s), λ n, «expr∑ in , »((k), range «expr + »(n, 1), v k))] [],
    { ext [] [ident n] [],
      simp [] [] [] ["[", expr f.map_sum, ",", expr hu, "]"] [] [] },
    rw ["<-", expr this] ["at", ident lim_v],
    exact [expr tendsto_nhds_unique ((f.continuous.tendsto g).comp hg) lim_v] },
  { suffices [] [":", expr ∀ n, «expr ≤ »(«expr∥ ∥»(s n), «expr * »(«expr + »(C, ε), «expr∥ ∥»(h)))],
    from [expr le_of_tendsto' (continuous_norm.continuous_at.tendsto.comp hg) this],
    intros [ident n],
    have [ident hnorm₀] [":", expr «expr ≤ »(«expr∥ ∥»(u 0), «expr + »(«expr * »(C, b 0), «expr * »(C, «expr∥ ∥»(h))))] [],
    { have [] [] [":=", expr calc
         «expr ≤ »(«expr∥ ∥»(v 0), «expr + »(«expr∥ ∥»(h), «expr∥ ∥»(«expr - »(v 0, h)))) : norm_le_insert' _ _
         «expr ≤ »(..., «expr + »(«expr∥ ∥»(h), b 0)) : by apply [expr add_le_add_left hv₀.le]],
      calc
        «expr ≤ »(«expr∥ ∥»(u 0), «expr * »(C, «expr∥ ∥»(v 0))) : hnorm_u 0
        «expr ≤ »(..., «expr * »(C, «expr + »(«expr∥ ∥»(h), b 0))) : mul_le_mul_of_nonneg_left this hC.le
        «expr = »(..., «expr + »(«expr * »(C, b 0), «expr * »(C, «expr∥ ∥»(h)))) : by rw ["[", expr add_comm, ",", expr mul_add, "]"] [] },
    have [] [":", expr «expr ≤ »(«expr∑ in , »((k), range «expr + »(n, 1), «expr * »(C, b k)), «expr * »(ε, «expr∥ ∥»(h)))] [":=", expr calc
       «expr = »(«expr∑ in , »((k), range «expr + »(n, 1), «expr * »(C, b k)), «expr * »(«expr∑ in , »((k), range «expr + »(n, 1), «expr ^ »(«expr / »(1, 2), k)), «expr / »(«expr * »(ε, «expr∥ ∥»(h)), 2))) : by simp [] [] ["only"] ["[", expr b, ",", expr mul_div_cancel' _ hC.ne.symm, ",", "<-", expr sum_mul, "]"] [] []
       «expr ≤ »(..., «expr * »(2, «expr / »(«expr * »(ε, «expr∥ ∥»(h)), 2))) : mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by nlinarith [] [] ["[", expr hε, ",", expr norm_nonneg h, "]"])
       «expr = »(..., «expr * »(ε, «expr∥ ∥»(h))) : mul_div_cancel' _ two_ne_zero],
    calc
      «expr ≤ »(«expr∥ ∥»(s n), «expr∑ in , »((k), range «expr + »(n, 1), «expr∥ ∥»(u k))) : norm_sum_le _ _
      «expr = »(..., «expr + »(«expr∑ in , »((k), range n, «expr∥ ∥»(u «expr + »(k, 1))), «expr∥ ∥»(u 0))) : sum_range_succ' _ _
      «expr ≤ »(..., «expr + »(«expr∑ in , »((k), range n, «expr * »(C, «expr∥ ∥»(v «expr + »(k, 1)))), «expr∥ ∥»(u 0))) : add_le_add_right (sum_le_sum (λ
        _ _, hnorm_u _)) _
      «expr ≤ »(..., «expr + »(«expr∑ in , »((k), range n, «expr * »(C, b «expr + »(k, 1))), «expr + »(«expr * »(C, b 0), «expr * »(C, «expr∥ ∥»(h))))) : add_le_add (sum_le_sum (λ
        k _, mul_le_mul_of_nonneg_left (hv _ k.succ_pos).le hC.le)) hnorm₀
      «expr = »(..., «expr + »(«expr∑ in , »((k), range «expr + »(n, 1), «expr * »(C, b k)), «expr * »(C, «expr∥ ∥»(h)))) : by rw ["[", "<-", expr add_assoc, ",", expr sum_range_succ', "]"] []
      «expr ≤ »(..., «expr * »(«expr + »(C, ε), «expr∥ ∥»(h))) : by { rw ["[", expr add_comm, ",", expr add_mul, "]"] [],
        apply [expr add_le_add_left this] } }
end

/-- Given `f : normed_group_hom G H` for some complete `G`, if every element `x` of the image of
an isometric immersion `j : normed_group_hom K H` has a preimage under `f` whose norm is at most
`C*∥x∥` then the same holds for elements of the (topological) closure of this image with constant
`C+ε` instead of `C`, for any positive `ε`.
This is useful in particular if `j` is the inclusion of a normed group into its completion
(in this case the closure is the full target group).
-/
theorem controlled_closure_range_of_complete {f : NormedGroupHom G H} {K : Type _} [SemiNormedGroup K]
  {j : NormedGroupHom K H} (hj : ∀ x, ∥j x∥ = ∥x∥) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
  (hyp : ∀ k, ∃ g, f g = j k ∧ ∥g∥ ≤ C*∥k∥) : f.surjective_on_with j.range.topological_closure (C+ε) :=
  by 
    replace hyp : ∀ h _ : h ∈ j.range, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥
    ·
      intro h h_in 
      rcases(j.mem_range _).mp h_in with ⟨k, rfl⟩
      rw [hj]
      exact hyp k 
    exact controlled_closure_of_complete hC hε hyp

end ControlledClosure

