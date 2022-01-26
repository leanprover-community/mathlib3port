import Mathbin.Analysis.Calculus.Inverse
import Mathbin.Analysis.NormedSpace.Complemented

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`implicit_function_data` that holds arguments for the most general version of the implicit function
theorem, see `implicit_function_data.implicit_function`
and `implicit_function_data.to_implicit_function`. This version allows a user to choose
a specific implicit function but provides only a little convenience over the inverse function
theorem.

Then we define `implicit_function_of_complemented`: implicit function defined by `f (g z y) = z`,
where `f : E → F` is a function strictly differentiable at `a` such that its derivative `f'`
is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finite dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `has_strict_fderiv_at`
and `f'.range = ⊤`. This version is named `implicit_function`.

## TODO

* Add a version for a function `f : E × F → G` such that $$\frac{\partial f}{\partial y}$$ is
  invertible.
* Add a version for `f : 𝕜 × 𝕜 → 𝕜` proving `has_strict_deriv_at` and `deriv φ = ...`.
* Prove that in a real vector space the implicit function has the same smoothness as the original
  one.
* If the original function is differentiable in a neighborhood, then the implicit function is
  differentiable in a neighborhood as well. Current setup only proves differentiability at one
  point for the implicit function constructed in this file (as opposed to an unspecified implicit
  function). One of the ways to overcome this difficulty is to use uniqueness of the implicit
  function in the general version of the theorem. Another way is to prove that *any* implicit
  function satisfying some predicate is strictly differentiable.

## Tags

implicit function, inverse function
-/


noncomputable section

open_locale TopologicalSpace

open Filter

open continuous_linear_map (fst snd subtype_val smulRight ker_prod)

open continuous_linear_equiv (ofBijective)

/-!
### General version

Consider two functions `f : E → F` and `g : E → G` and a point `a` such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`.

Note that the map `x ↦ (f x, g x)` has a bijective derivative, hence it is a local homeomorphism
between `E` and `F × G`. We use this fact to define a function `φ : F → G → E`
(see `implicit_function_data.implicit_function`) such that for `(y, z)` close enough to `(f a, g a)`
we have `f (φ y z) = y` and `g (φ y z) = z`.

We also prove a formula for $$\frac{\partial\varphi}{\partial z}.$$

Though this statement is almost symmetric with respect to `F`, `G`, we interpret it in the following
way. Consider a family of surfaces `{x | f x = y}`, `y ∈ 𝓝 (f a)`. Each of these surfaces is
parametrized by `φ y`.

There are many ways to choose a (differentiable) function `φ` such that `f (φ y z) = y` but the
extra condition `g (φ y z) = z` allows a user to select one of these functions. If we imagine
that the level surfaces `f = const` form a local horizontal foliation, then the choice of
`g` fixes a transverse foliation `g = const`, and `φ` is the inverse function of the projection
of `{x | f x = y}` along this transverse foliation.

This version of the theorem is used to prove the other versions and can be used if a user
needs to have a complete control over the choice of the implicit function.
-/


/-- Data for the general version of the implicit function theorem. It holds two functions
`f : E → F` and `g : E → G` (named `left_fun` and `right_fun`) and a point `a` (named `pt`)
such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`. -/
@[nolint has_inhabited_instance]
structure ImplicitFunctionData (𝕜 : Type _) [NondiscreteNormedField 𝕜] (E : Type _) [NormedGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] (F : Type _) [NormedGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type _) [NormedGroup G]
  [NormedSpace 𝕜 G] [CompleteSpace G] where
  leftFun : E → F
  leftDeriv : E →L[𝕜] F
  rightFun : E → G
  rightDeriv : E →L[𝕜] G
  pt : E
  left_has_deriv : HasStrictFderivAt left_fun left_deriv pt
  right_has_deriv : HasStrictFderivAt right_fun right_deriv pt
  left_range : left_deriv.range = ⊤
  right_range : right_deriv.range = ⊤
  is_compl_ker : IsCompl left_deriv.ker right_deriv.ker

namespace ImplicitFunctionData

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]
  [CompleteSpace G] (φ : ImplicitFunctionData 𝕜 E F G)

/-- The function given by `x ↦ (left_fun x, right_fun x)`. -/
def prod_fun (x : E) : F × G :=
  (φ.left_fun x, φ.right_fun x)

@[simp]
theorem prod_fun_apply (x : E) : φ.prod_fun x = (φ.left_fun x, φ.right_fun x) :=
  rfl

protected theorem HasStrictFderivAt :
    HasStrictFderivAt φ.prod_fun
      (φ.left_deriv.equiv_prod_of_surjective_of_is_compl φ.right_deriv φ.left_range φ.right_range φ.is_compl_ker :
        E →L[𝕜] F × G)
      φ.pt :=
  φ.left_has_deriv.prod φ.right_has_deriv

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `x ↦ (f x, g x)` defines a local homeomorphism between
`E` and `F × G`. In particular, `{x | f x = f a}` is locally homeomorphic to `G`. -/
def to_local_homeomorph : LocalHomeomorph E (F × G) :=
  φ.has_strict_fderiv_at.to_local_homeomorph _

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `implicit_function_of_is_compl_ker` is the unique (germ of a)
map `φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`. -/
def implicit_function : F → G → E :=
  Function.curry <| φ.to_local_homeomorph.symm

@[simp]
theorem to_local_homeomorph_coe : ⇑φ.to_local_homeomorph = φ.prod_fun :=
  rfl

theorem to_local_homeomorph_apply (x : E) : φ.to_local_homeomorph x = (φ.left_fun x, φ.right_fun x) :=
  rfl

theorem pt_mem_to_local_homeomorph_source : φ.pt ∈ φ.to_local_homeomorph.source :=
  φ.has_strict_fderiv_at.mem_to_local_homeomorph_source

theorem map_pt_mem_to_local_homeomorph_target : (φ.left_fun φ.pt, φ.right_fun φ.pt) ∈ φ.to_local_homeomorph.target :=
  φ.to_local_homeomorph.map_source <| φ.pt_mem_to_local_homeomorph_source

theorem prod_map_implicit_function :
    ∀ᶠ p : F × G in 𝓝 (φ.prod_fun φ.pt), φ.prod_fun (φ.implicit_function p.1 p.2) = p :=
  φ.has_strict_fderiv_at.eventually_right_inverse.mono fun ⟨z, y⟩ h => h

theorem left_map_implicit_function :
    ∀ᶠ p : F × G in 𝓝 (φ.prod_fun φ.pt), φ.left_fun (φ.implicit_function p.1 p.2) = p.1 :=
  φ.prod_map_implicit_function.mono fun z => congr_argₓ Prod.fst

theorem right_map_implicit_function :
    ∀ᶠ p : F × G in 𝓝 (φ.prod_fun φ.pt), φ.right_fun (φ.implicit_function p.1 p.2) = p.2 :=
  φ.prod_map_implicit_function.mono fun z => congr_argₓ Prod.snd

theorem implicit_function_apply_image : ∀ᶠ x in 𝓝 φ.pt, φ.implicit_function (φ.left_fun x) (φ.right_fun x) = x :=
  φ.has_strict_fderiv_at.eventually_left_inverse

theorem map_nhds_eq : map φ.left_fun (𝓝 φ.pt) = 𝓝 (φ.left_fun φ.pt) :=
  show map (Prod.fst ∘ φ.prod_fun) (𝓝 φ.pt) = 𝓝 (φ.prod_fun φ.pt).1 by
    rw [← map_map, φ.has_strict_fderiv_at.map_nhds_eq_of_equiv, map_fst_nhds]

theorem implicit_function_has_strict_fderiv_at (g'inv : G →L[𝕜] E)
    (hg'inv : φ.right_deriv.comp g'inv = ContinuousLinearMap.id 𝕜 G) (hg'invf : φ.left_deriv.comp g'inv = 0) :
    HasStrictFderivAt (φ.implicit_function (φ.left_fun φ.pt)) g'inv (φ.right_fun φ.pt) := by
  have := φ.has_strict_fderiv_at.to_local_inverse
  simp only [prod_fun] at this
  convert this.comp (φ.right_fun φ.pt) ((has_strict_fderiv_at_const _ _).Prod (has_strict_fderiv_at_id _))
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.coe_comp', Function.comp_app] at hg'inv hg'invf⊢
  simp [ContinuousLinearEquiv.eq_symm_apply, *]

end ImplicitFunctionData

namespace HasStrictFderivAt

section Complemented

/-!
### Case of a complemented kernel

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` and a point `a : E` such that `f` is strictly differentiable at `a`, its derivative `f'`
is surjective and the kernel of `f'` is a complemented subspace of `E` (i.e., it has a closed
complementary subspace). Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/


variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}

section Defs

variable (f f')

/-- Data used to apply the generic implicit function theorem to the case of a strictly
differentiable map such that its derivative is surjective and has a complemented kernel. -/
@[simp]
def implicit_function_data_of_complemented (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) : ImplicitFunctionData 𝕜 E F f'.ker where
  leftFun := f
  leftDeriv := f'
  rightFun := fun x => Classical.some hker (x - a)
  rightDeriv := Classical.some hker
  pt := a
  left_has_deriv := hf
  right_has_deriv := (Classical.some hker).HasStrictFderivAt.comp a ((has_strict_fderiv_at_id a).sub_const a)
  left_range := hf'
  right_range := LinearMap.range_eq_of_proj (Classical.some_spec hker)
  is_compl_ker := LinearMap.is_compl_of_proj (Classical.some_spec hker)

/-- A local homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
to vertical subspaces. -/
def implicit_to_local_homeomorph_of_complemented (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) : LocalHomeomorph E (F × f'.ker) :=
  (implicit_function_data_of_complemented f f' hf hf' hker).toLocalHomeomorph

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function_of_complemented (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) : F → f'.ker → E :=
  (implicit_function_data_of_complemented f f' hf hf' hker).implicitFunction

end Defs

@[simp]
theorem implicit_to_local_homeomorph_of_complemented_fst (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) (x : E) :
    (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).fst = f x :=
  rfl

theorem implicit_to_local_homeomorph_of_complemented_apply (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) (y : E) :
    hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker y = (f y, Classical.some hker (y - a)) :=
  rfl

@[simp]
theorem implicit_to_local_homeomorph_of_complemented_apply_ker (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) (y : f'.ker) :
    hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker (y + a) = (f (y + a), y) := by
  simp only [implicit_to_local_homeomorph_of_complemented_apply, add_sub_cancel, Classical.some_spec hker]

@[simp]
theorem implicit_to_local_homeomorph_of_complemented_self (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) : hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker a = (f a, 0) :=
  by
  simp [hf.implicit_to_local_homeomorph_of_complemented_apply]

theorem mem_implicit_to_local_homeomorph_of_complemented_source (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) : a ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).Source :=
  mem_to_local_homeomorph_source _

theorem mem_implicit_to_local_homeomorph_of_complemented_target (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) :
    (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).Target := by
  simpa only [implicit_to_local_homeomorph_of_complemented_self] using
    (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).map_source <|
      hf.mem_implicit_to_local_homeomorph_of_complemented_source hf' hker

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicit_function_of_complemented_eq (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) :
    ∀ᶠ p : F × f'.ker in 𝓝 (f a, 0), f (hf.implicit_function_of_complemented f f' hf' hker p.1 p.2) = p.1 :=
  ((hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicit_to_local_homeomorph_of_complemented_target hf' hker).mono
    fun ⟨z, y⟩ h => congr_argₓ Prod.fst h

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
theorem eq_implicit_function_of_complemented (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) :
    ∀ᶠ x in 𝓝 a,
      hf.implicit_function_of_complemented f f' hf' hker (f x)
          (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).snd =
        x :=
  (implicit_function_data_of_complemented f f' hf hf' hker).implicit_function_apply_image

@[simp]
theorem implicit_function_of_complemented_apply_image (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) : hf.implicit_function_of_complemented f f' hf' hker (f a) 0 = a := by
  convert
    (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).left_inv
      (hf.mem_implicit_to_local_homeomorph_of_complemented_source hf' hker)
  exact congr_argₓ Prod.snd (hf.implicit_to_local_homeomorph_of_complemented_self hf' hker).symm

theorem to_implicit_function_of_complemented (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.closed_complemented) :
    HasStrictFderivAt (hf.implicit_function_of_complemented f f' hf' hker (f a)) (subtype_val f'.ker) 0 := by
  convert
        (implicit_function_data_of_complemented f f' hf hf' hker).implicit_function_has_strict_fderiv_at
          (subtype_val f'.ker) _ _ <;>
      [skip, ext, ext] <;>
    simp [Classical.some_spec hker]

end Complemented

/-!
### Finite dimensional case

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` from a Banach normed space to a finite dimensional space.
Take a point `a : E` such that `f` is strictly differentiable at `a` and its derivative `f'`
is surjective. Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

This version deduces that `ker f'` is a complemented subspace from the fact that `F` is a finite
dimensional space, then applies the previous version.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/


section FiniteDimensional

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] [CompleteSpace 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f : E → F) (f' : E →L[𝕜] F)
  {a : E}

/-- Given a map `f : E → F` to a finite dimensional space with a surjective derivative `f'`,
returns a local homeomorphism between `E` and `F × ker f'`. -/
def implicit_to_local_homeomorph (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    LocalHomeomorph E (F × f'.ker) :=
  have := FiniteDimensional.complete 𝕜 F
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' f'.ker_closed_complemented_of_finite_dimensional_range

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) : F → f'.ker → E :=
  Function.curry <| (hf.implicit_to_local_homeomorph f f' hf').symm

variable {f f'}

@[simp]
theorem implicit_to_local_homeomorph_fst (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) (x : E) :
    (hf.implicit_to_local_homeomorph f f' hf' x).fst = f x :=
  rfl

@[simp]
theorem implicit_to_local_homeomorph_apply_ker (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) (y : f'.ker) :
    hf.implicit_to_local_homeomorph f f' hf' (y + a) = (f (y + a), y) := by
  apply implicit_to_local_homeomorph_of_complemented_apply_ker

@[simp]
theorem implicit_to_local_homeomorph_self (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicit_to_local_homeomorph f f' hf' a = (f a, 0) := by
  apply implicit_to_local_homeomorph_of_complemented_self

theorem mem_implicit_to_local_homeomorph_source (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    a ∈ (hf.implicit_to_local_homeomorph f f' hf').Source :=
  mem_to_local_homeomorph_source _

theorem mem_implicit_to_local_homeomorph_target (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph f f' hf').Target := by
  apply mem_implicit_to_local_homeomorph_of_complemented_target

theorem tendsto_implicit_function (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) {α : Type _} {l : Filter α}
    {g₁ : α → F} {g₂ : α → f'.ker} (h₁ : tendsto g₁ l (𝓝 <| f a)) (h₂ : tendsto g₂ l (𝓝 0)) :
    tendsto (fun t => hf.implicit_function f f' hf' (g₁ t) (g₂ t)) l (𝓝 a) := by
  refine'
    ((hf.implicit_to_local_homeomorph f f' hf').tendsto_symm (hf.mem_implicit_to_local_homeomorph_source hf')).comp _
  rw [implicit_to_local_homeomorph_self]
  exact h₁.prod_mk_nhds h₂

alias tendsto_implicit_function ← Filter.Tendsto.implicit_function

/-- `implicit_function` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicit_function_eq (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    ∀ᶠ p : F × f'.ker in 𝓝 (f a, 0), f (hf.implicit_function f f' hf' p.1 p.2) = p.1 := by
  apply map_implicit_function_of_complemented_eq

@[simp]
theorem implicit_function_apply_image (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicit_function f f' hf' (f a) 0 = a := by
  apply implicit_function_of_complemented_apply_image

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
theorem eq_implicit_function (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    ∀ᶠ x in 𝓝 a, hf.implicit_function f f' hf' (f x) (hf.implicit_to_local_homeomorph f f' hf' x).snd = x := by
  apply eq_implicit_function_of_complemented

theorem to_implicit_function (hf : HasStrictFderivAt f f' a) (hf' : f'.range = ⊤) :
    HasStrictFderivAt (hf.implicit_function f f' hf' (f a)) (subtype_val f'.ker) 0 := by
  apply to_implicit_function_of_complemented

end FiniteDimensional

end HasStrictFderivAt

