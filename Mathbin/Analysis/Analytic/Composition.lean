import Mathbin.Analysis.Analytic.Basic 
import Mathbin.Combinatorics.Composition

/-!
# Composition of analytic functions

in this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑' qₙ (z, ..., z)` and `f y = ∑' pₖ (y, ..., y)`. Then

`g (f y) = ∑' qₙ (∑' pₖ (y, ..., y), ..., ∑' pₖ (y, ..., y))
= ∑' qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use compositions of an integer `N`, i.e., its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such a composition `c` and two formal
multilinear series `q` and `p`, let `q.comp_along_composition p c` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `c : composition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `composition N` has cardinality `2^(N-1)` and estimates on
the norm of `qₙ` and `pₖ`, which give summability. We also need to show that it indeed converges to
`g ∘ f`. For this, we note that the composition of partial sums converges to `g ∘ f`, and that it
corresponds to a part of the whole sum, on a subset that increases to the whole space. By
summability of the norms, this implies the overall convergence.

## Main results

* `q.comp p` is the formal composition of the formal multilinear series `q` and `p`.
* `has_fpower_series_at.comp` states that if two functions `g` and `f` admit power series expansions
  `q` and `p`, then `g ∘ f` admits a power series expansion given by `q.comp p`.
* `analytic_at.comp` states that the composition of analytic functions is analytic.
* `formal_multilinear_series.comp_assoc` states that composition is associative on formal
  multilinear series.

## Implementation details

The main technical difficulty is to write down things. In particular, we need to define precisely
`q.comp_along_composition p c` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `composition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, composition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `composition`.

The associativity of composition on formal multilinear series is a nontrivial result: it does not
follow from the associativity of composition of analytic functions, as there is no uniqueness for
the formal multilinear series representing a function (and also, it holds even when the radius of
convergence of the series is `0`). Instead, we give a direct proof, which amounts to reordering
double sums in a careful way. The change of variables is a canonical (combinatorial) bijection
`composition.sigma_equiv_sigma_pi` between `(Σ (a : composition n), composition a.length)` and
`(Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i))`, and is described
in more details below in the paragraph on associativity.
-/


noncomputable theory

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜
      E]{F :
    Type
      _}[NormedGroup
      F][NormedSpace 𝕜 F]{G : Type _}[NormedGroup G][NormedSpace 𝕜 G]{H : Type _}[NormedGroup H][NormedSpace 𝕜 H]

open Filter List

open_locale TopologicalSpace BigOperators Classical Nnreal Ennreal

/-! ### Composing formal multilinear series -/


namespace FormalMultilinearSeries

/-!
In this paragraph, we define the composition of formal multilinear series, by summing over all
possible compositions of `n`.
-/


/-- Given a formal multilinear series `p`, a composition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.apply_composition c v i` for `v : fin n → E` and `i : fin c.length`. -/
def apply_composition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) :
  (Finₓ n → E) → Finₓ c.length → F :=
  fun v i => p (c.blocks_fun i) (v ∘ c.embedding i)

theorem apply_composition_ones (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
  p.apply_composition (Composition.ones n) = fun v i => p 1 fun _ => v (Finₓ.castLe (Composition.length_le _) i) :=
  by 
    funext v i 
    apply p.congr (Composition.ones_blocks_fun _ _)
    intro j hjn hj1 
    obtain rfl : j = 0
    ·
      linarith 
    refine' congr_argₓ v _ 
    rw [Finₓ.ext_iff, Finₓ.coe_cast_le, Composition.ones_embedding, Finₓ.coe_mk]

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem apply_composition_single
(p : formal_multilinear_series 𝕜 E F)
{n : exprℕ()}
(hn : «expr < »(0, n))
(v : fin n → E) : «expr = »(p.apply_composition (composition.single n hn) v, λ j, p n v) :=
begin
  ext [] [ident j] [],
  refine [expr p.congr (by simp [] [] [] [] [] []) (λ i hi1 hi2, _)],
  dsimp [] [] [] [],
  congr' [1] [],
  convert [] [expr composition.single_embedding hn ⟨i, hi2⟩] [],
  cases [expr j] [],
  have [] [":", expr «expr = »(j_val, 0)] [":=", expr le_bot_iff.1 (nat.lt_succ_iff.1 j_property)],
  unfold_coes [],
  congr; try { assumption <|> simp [] [] [] [] [] [] }
end

@[simp]
theorem remove_zero_apply_composition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) :
  p.remove_zero.apply_composition c = p.apply_composition c :=
  by 
    ext v i 
    simp [apply_composition, zero_lt_one.trans_le (c.one_le_blocks_fun i), remove_zero_of_pos]

/-- Technical lemma stating how `p.apply_composition` commutes with updating variables. This
will be the key point to show that functions constructed from `apply_composition` retain
multilinearity. -/
theorem apply_composition_update (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) (j : Finₓ n)
  (v : Finₓ n → E) (z : E) :
  p.apply_composition c (Function.update v j z) =
    Function.update (p.apply_composition c v) (c.index j)
      (p (c.blocks_fun (c.index j)) (Function.update (v ∘ c.embedding (c.index j)) (c.inv_embedding j) z)) :=
  by 
    ext k 
    byCases' h : k = c.index j
    ·
      rw [h]
      let r : Finₓ (c.blocks_fun (c.index j)) → Finₓ n := c.embedding (c.index j)
      simp only [Function.update_same]
      change p (c.blocks_fun (c.index j)) (Function.update v j z ∘ r) = _ 
      let j' := c.inv_embedding j 
      suffices B : (Function.update v j z ∘ r) = Function.update (v ∘ r) j' z
      ·
        rw [B]
      suffices C : (Function.update v (r j') z ∘ r) = Function.update (v ∘ r) j' z
      ·
        ·
          convert C 
          exact (c.embedding_comp_inv j).symm 
      exact Function.update_comp_eq_of_injective _ (c.embedding _).Injective _ _
    ·
      simp only [h, Function.update_eq_self, Function.update_noteq, Ne.def, not_false_iff]
      let r : Finₓ (c.blocks_fun k) → Finₓ n := c.embedding k 
      change p (c.blocks_fun k) (Function.update v j z ∘ r) = p (c.blocks_fun k) (v ∘ r)
      suffices B : (Function.update v j z ∘ r) = (v ∘ r)
      ·
        rw [B]
      apply Function.update_comp_eq_of_not_mem_range 
      rwa [c.mem_range_embedding_iff']

@[simp]
theorem comp_continuous_linear_map_apply_composition {n : ℕ} (p : FormalMultilinearSeries 𝕜 F G) (f : E →L[𝕜] F)
  (c : Composition n) (v : Finₓ n → E) :
  (p.comp_continuous_linear_map f).applyComposition c v = p.apply_composition c (f ∘ v) :=
  by 
    simp [apply_composition]

end FormalMultilinearSeries

namespace ContinuousMultilinearMap

open FormalMultilinearSeries

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a formal multilinear series `p`, a composition `c` of `n` and a continuous multilinear
map `f` in `c.length` variables, one may form a multilinear map in `n` variables by applying
the right coefficient of `p` to each block of the composition, and then applying `f` to the
resulting vector. It is called `f.comp_along_composition_aux p c`.
This function admits a version as a continuous multilinear map, called
`f.comp_along_composition p c` below. -/
def comp_along_composition_aux
{n : exprℕ()}
(p : formal_multilinear_series 𝕜 E F)
(c : composition n)
(f : continuous_multilinear_map 𝕜 (λ i : fin c.length, F) G) : multilinear_map 𝕜 (λ i : fin n, E) G :=
{ to_fun := λ v, f (p.apply_composition c v),
  map_add' := λ
  v
  i
  x
  y, by simp [] [] ["only"] ["[", expr apply_composition_update, ",", expr continuous_multilinear_map.map_add, "]"] [] [],
  map_smul' := λ
  v
  i
  c
  x, by simp [] [] ["only"] ["[", expr apply_composition_update, ",", expr continuous_multilinear_map.map_smul, "]"] [] [] }

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The norm of `f.comp_along_composition_aux p c` is controlled by the product of
the norms of the relevant bits of `f` and `p`. -/
theorem comp_along_composition_aux_bound
{n : exprℕ()}
(p : formal_multilinear_series 𝕜 E F)
(c : composition n)
(f : continuous_multilinear_map 𝕜 (λ i : fin c.length, F) G)
(v : fin n → E) : «expr ≤ »(«expr∥ ∥»(f.comp_along_composition_aux p c v), «expr * »(«expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr∥ ∥»(p (c.blocks_fun i)))), «expr∏ , »((i : fin n), «expr∥ ∥»(v i)))) :=
calc
  «expr = »(«expr∥ ∥»(f.comp_along_composition_aux p c v), «expr∥ ∥»(f (p.apply_composition c v))) : rfl
  «expr ≤ »(..., «expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr∥ ∥»(p.apply_composition c v i)))) : continuous_multilinear_map.le_op_norm _ _
  «expr ≤ »(..., «expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr * »(«expr∥ ∥»(p (c.blocks_fun i)), «expr∏ , »((j : fin (c.blocks_fun i)), «expr∥ ∥»(«expr ∘ »(v, c.embedding i) j)))))) : begin
    apply [expr mul_le_mul_of_nonneg_left _ (norm_nonneg _)],
    refine [expr finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, _)],
    apply [expr continuous_multilinear_map.le_op_norm]
  end
  «expr = »(..., «expr * »(«expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr∥ ∥»(p (c.blocks_fun i)))), «expr∏ , »((i)
     (j : fin (c.blocks_fun i)), «expr∥ ∥»(«expr ∘ »(v, c.embedding i) j)))) : by rw ["[", expr finset.prod_mul_distrib, ",", expr mul_assoc, "]"] []
  «expr = »(..., «expr * »(«expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr∥ ∥»(p (c.blocks_fun i)))), «expr∏ , »((i : fin n), «expr∥ ∥»(v i)))) : by { rw ["[", "<-", expr c.blocks_fin_equiv.prod_comp, ",", "<-", expr finset.univ_sigma_univ, ",", expr finset.prod_sigma, "]"] [],
    congr }

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a formal multilinear series `p`, a composition `c` of `n` and a continuous multilinear
map `f` in `c.length` variables, one may form a continuous multilinear map in `n` variables by
applying the right coefficient of `p` to each block of the composition, and then applying `f` to
the resulting vector. It is called `f.comp_along_composition p c`. It is constructed from the
analogous multilinear function `f.comp_along_composition_aux p c`, together with a norm
control to get the continuity. -/
def comp_along_composition
{n : exprℕ()}
(p : formal_multilinear_series 𝕜 E F)
(c : composition n)
(f : continuous_multilinear_map 𝕜 (λ i : fin c.length, F) G) : continuous_multilinear_map 𝕜 (λ i : fin n, E) G :=
(f.comp_along_composition_aux p c).mk_continuous _ (f.comp_along_composition_aux_bound p c)

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem comp_along_composition_apply
{n : exprℕ()}
(p : formal_multilinear_series 𝕜 E F)
(c : composition n)
(f : continuous_multilinear_map 𝕜 (λ i : fin c.length, F) G)
(v : fin n → E) : «expr = »(f.comp_along_composition p c v, f (p.apply_composition c v)) :=
rfl

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.comp_along_composition p c`. It is constructed from the analogous multilinear
function `q.comp_along_composition_aux p c`, together with a norm control to get
the continuity. -/
def comp_along_composition
{n : exprℕ()}
(q : formal_multilinear_series 𝕜 F G)
(p : formal_multilinear_series 𝕜 E F)
(c : composition n) : continuous_multilinear_map 𝕜 (λ i : fin n, E) G :=
(q c.length).comp_along_composition p c

@[simp]
theorem comp_along_composition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  (c : Composition n) (v : Finₓ n → E) : (q.comp_along_composition p c) v = q c.length (p.apply_composition c v) :=
  rfl

/-- The norm of `q.comp_along_composition p c` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
theorem comp_along_composition_norm {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  (c : Composition n) : ∥q.comp_along_composition p c∥ ≤ ∥q c.length∥*∏i, ∥p (c.blocks_fun i)∥ :=
  MultilinearMap.mk_continuous_norm_le _ (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => norm_nonneg _)) _

theorem comp_along_composition_nnnorm {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
  (c : Composition n) : nnnorm (q.comp_along_composition p c) ≤ nnnorm (q c.length)*∏i, nnnorm (p (c.blocks_fun i)) :=
  by 
    rw [←Nnreal.coe_le_coe]
    pushCast 
    exact q.comp_along_composition_norm p c

/-- Formal composition of two formal multilinear series. The `n`-th coefficient in the composition
is defined to be the sum of `q.comp_along_composition p c` over all compositions of
`n`. In other words, this term (as a multilinear function applied to `v_0, ..., v_{n-1}`) is
`∑'_{k} ∑'_{i₁ + ... + iₖ = n} pₖ (q_{i_1} (...), ..., q_{i_k} (...))`, where one puts all variables
`v_0, ..., v_{n-1}` in increasing order in the dots.

In general, the composition `q ∘ p` only makes sense when the constant coefficient of `p` vanishes.
We give a general formula but which ignores the value of `p 0` instead.
-/
protected def comp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
  FormalMultilinearSeries 𝕜 E G :=
  fun n => ∑c : Composition n, q.comp_along_composition p c

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `0`-th coefficient of `q.comp p` is `q 0`. Since these maps are multilinear maps in zero
variables, but on different spaces, we can not state this directly, so we state it when applied to
arbitrary vectors (which have to be the zero vector). -/
theorem comp_coeff_zero
(q : formal_multilinear_series 𝕜 F G)
(p : formal_multilinear_series 𝕜 E F)
(v : fin 0 → E)
(v' : fin 0 → F) : «expr = »(q.comp p 0 v, q 0 v') :=
begin
  let [ident c] [":", expr composition 0] [":=", expr composition.ones 0],
  dsimp [] ["[", expr formal_multilinear_series.comp, "]"] [] [],
  have [] [":", expr «expr = »({c}, (finset.univ : finset (composition 0)))] [],
  { apply [expr finset.eq_of_subset_of_card_le]; simp [] [] [] ["[", expr finset.card_univ, ",", expr composition_card 0, "]"] [] [] },
  rw ["[", "<-", expr this, ",", expr finset.sum_singleton, ",", expr comp_along_composition_apply, "]"] [],
  symmetry,
  congr' [] []
end

@[simp]
theorem comp_coeff_zero' (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Finₓ 0 → E) :
  (q.comp p) 0 v = q 0 fun i => 0 :=
  q.comp_coeff_zero p v _

/-- The `0`-th coefficient of `q.comp p` is `q 0`. When `p` goes from `E` to `E`, this can be
expressed as a direct equality -/
theorem comp_coeff_zero'' (q : FormalMultilinearSeries 𝕜 E F) (p : FormalMultilinearSeries 𝕜 E E) :
  (q.comp p) 0 = q 0 :=
  by 
    ext v 
    exact q.comp_coeff_zero p _ _

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The first coefficient of a composition of formal multilinear series is the composition of the
first coefficients seen as continuous linear maps. -/
theorem comp_coeff_one
(q : formal_multilinear_series 𝕜 F G)
(p : formal_multilinear_series 𝕜 E F)
(v : fin 1 → E) : «expr = »(q.comp p 1 v, q 1 (λ i, p 1 v)) :=
begin
  have [] [":", expr «expr = »({composition.ones 1}, (finset.univ : finset (composition 1)))] [":=", expr finset.eq_univ_of_card _ (by simp [] [] [] ["[", expr composition_card, "]"] [] [])],
  simp [] [] ["only"] ["[", expr formal_multilinear_series.comp, ",", expr comp_along_composition_apply, ",", "<-", expr this, ",", expr finset.sum_singleton, "]"] [] [],
  refine [expr q.congr (by simp [] [] [] [] [] []) (λ i hi1 hi2, _)],
  simp [] [] ["only"] ["[", expr apply_composition_ones, "]"] [] [],
  exact [expr p.congr rfl (λ j hj1 hj2, by congr)]
end

theorem remove_zero_comp_of_pos (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
  (hn : 0 < n) : q.remove_zero.comp p n = q.comp p n :=
  by 
    ext v 
    simp only [FormalMultilinearSeries.comp, comp_along_composition,
      ContinuousMultilinearMap.comp_along_composition_apply, ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_congr rfl fun c hc => _ 
    rw [remove_zero_of_pos _ (c.length_pos_of_pos hn)]

@[simp]
theorem comp_remove_zero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
  q.comp p.remove_zero = q.comp p :=
  by 
    ext n 
    simp [FormalMultilinearSeries.comp]

/-!
### The identity formal power series

We will now define the identity power series, and show that it is a neutral element for left and
right composition.
-/


section 

variable(𝕜 E)

/-- The identity formal multilinear series, with all coefficients equal to `0` except for `n = 1`
where it is (the continuous multilinear version of) the identity. -/
def id : FormalMultilinearSeries 𝕜 E E
| 0 => 0
| 1 => (continuousMultilinearCurryFin1 𝕜 E E).symm (ContinuousLinearMap.id 𝕜 E)
| _ => 0

/-- The first coefficient of `id 𝕜 E` is the identity. -/
@[simp]
theorem id_apply_one (v : Finₓ 1 → E) : (FormalMultilinearSeries.id 𝕜 E) 1 v = v 0 :=
  rfl

/-- The `n`th coefficient of `id 𝕜 E` is the identity when `n = 1`. We state this in a dependent
way, as it will often appear in this form. -/
theorem id_apply_one' {n : ℕ} (h : n = 1) (v : Finₓ n → E) : (id 𝕜 E) n v = v ⟨0, h.symm ▸ zero_lt_one⟩ :=
  by 
    subst n 
    apply id_apply_one

/-- For `n ≠ 1`, the `n`-th coefficient of `id 𝕜 E` is zero, by definition. -/
@[simp]
theorem id_apply_ne_one {n : ℕ} (h : n ≠ 1) : (FormalMultilinearSeries.id 𝕜 E) n = 0 :=
  by 
    cases n
    ·
      rfl 
    cases n
    ·
      contradiction 
    rfl

end 

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem comp_id (p : formal_multilinear_series 𝕜 E F) : «expr = »(p.comp (id 𝕜 E), p) :=
begin
  ext1 [] [ident n],
  dsimp [] ["[", expr formal_multilinear_series.comp, "]"] [] [],
  rw [expr finset.sum_eq_single (composition.ones n)] [],
  show [expr «expr = »(comp_along_composition p (id 𝕜 E) (composition.ones n), p n)],
  { ext [] [ident v] [],
    rw [expr comp_along_composition_apply] [],
    apply [expr p.congr (composition.ones_length n)],
    intros [],
    rw [expr apply_composition_ones] [],
    refine [expr congr_arg v _],
    rw ["[", expr fin.ext_iff, ",", expr fin.coe_cast_le, ",", expr fin.coe_mk, ",", expr fin.coe_mk, "]"] [] },
  show [expr ∀
   b : composition n, «expr ∈ »(b, finset.univ) → «expr ≠ »(b, composition.ones n) → «expr = »(comp_along_composition p (id 𝕜 E) b, 0)],
  { assume [binders (b _ hb)],
    obtain ["⟨", ident k, ",", ident hk, ",", ident lt_k, "⟩", ":", expr «expr∃ , »((k : exprℕ())
      (H : «expr ∈ »(k, composition.blocks b)), «expr < »(1, k)), ":=", expr composition.ne_ones_iff.1 hb],
    obtain ["⟨", ident i, ",", ident i_lt, ",", ident hi, "⟩", ":", expr «expr∃ , »((i : exprℕ())
      (h : «expr < »(i, b.blocks.length)), «expr = »(b.blocks.nth_le i h, k)), ":=", expr nth_le_of_mem hk],
    let [ident j] [":", expr fin b.length] [":=", expr ⟨i, «expr ▸ »(b.blocks_length, i_lt)⟩],
    have [ident A] [":", expr «expr < »(1, b.blocks_fun j)] [":=", expr by convert [] [expr lt_k] []],
    ext [] [ident v] [],
    rw ["[", expr comp_along_composition_apply, ",", expr continuous_multilinear_map.zero_apply, "]"] [],
    apply [expr continuous_multilinear_map.map_coord_zero _ j],
    dsimp [] ["[", expr apply_composition, "]"] [] [],
    rw [expr id_apply_ne_one _ _ (ne_of_gt A)] [],
    refl },
  { simp [] [] [] [] [] [] }
end

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem id_comp (p : formal_multilinear_series 𝕜 E F) (h : «expr = »(p 0, 0)) : «expr = »((id 𝕜 F).comp p, p) :=
begin
  ext1 [] [ident n],
  by_cases [expr hn, ":", expr «expr = »(n, 0)],
  { rw ["[", expr hn, ",", expr h, "]"] [],
    ext [] [ident v] [],
    rw ["[", expr comp_coeff_zero', ",", expr id_apply_ne_one _ _ zero_ne_one, "]"] [],
    refl },
  { dsimp [] ["[", expr formal_multilinear_series.comp, "]"] [] [],
    have [ident n_pos] [":", expr «expr < »(0, n)] [":=", expr bot_lt_iff_ne_bot.mpr hn],
    rw [expr finset.sum_eq_single (composition.single n n_pos)] [],
    show [expr «expr = »(comp_along_composition (id 𝕜 F) p (composition.single n n_pos), p n)],
    { ext [] [ident v] [],
      rw ["[", expr comp_along_composition_apply, ",", expr id_apply_one' _ _ (composition.single_length n_pos), "]"] [],
      dsimp [] ["[", expr apply_composition, "]"] [] [],
      refine [expr p.congr rfl (λ i him hin, «expr $ »(congr_arg v, _))],
      ext [] [] [],
      simp [] [] [] [] [] [] },
    show [expr ∀
     b : composition n, «expr ∈ »(b, finset.univ) → «expr ≠ »(b, composition.single n n_pos) → «expr = »(comp_along_composition (id 𝕜 F) p b, 0)],
    { assume [binders (b _ hb)],
      have [ident A] [":", expr «expr ≠ »(b.length, 1)] [],
      by simpa [] [] [] ["[", expr composition.eq_single_iff_length, "]"] [] ["using", expr hb],
      ext [] [ident v] [],
      rw ["[", expr comp_along_composition_apply, ",", expr id_apply_ne_one _ _ A, "]"] [],
      refl },
    { simp [] [] [] [] [] [] } }
end

/-! ### Summability properties of the composition of formal power series-/


section 

attribute [-instance] Unique.subsingleton

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If two formal multilinear series have positive radius of convergence, then the terms appearing
in the definition of their composition are also summable (when multiplied by a suitable positive
geometric term). -/
theorem comp_summable_nnreal
(q : formal_multilinear_series 𝕜 F G)
(p : formal_multilinear_series 𝕜 E F)
(hq : «expr < »(0, q.radius))
(hp : «expr < »(0, p.radius)) : «expr∃ , »((r «expr > » (0 : «exprℝ≥0»())), summable (λ
  i : «exprΣ , »((n), composition n), «expr * »(nnnorm (q.comp_along_composition p i.2), «expr ^ »(r, i.1)))) :=
begin
  rcases [expr ennreal.lt_iff_exists_nnreal_btwn.1 (lt_min ennreal.zero_lt_one hq), "with", "⟨", ident rq, ",", ident rq_pos, ",", ident hrq, "⟩"],
  rcases [expr ennreal.lt_iff_exists_nnreal_btwn.1 (lt_min ennreal.zero_lt_one hp), "with", "⟨", ident rp, ",", ident rp_pos, ",", ident hrp, "⟩"],
  simp [] [] ["only"] ["[", expr lt_min_iff, ",", expr ennreal.coe_lt_one_iff, ",", expr ennreal.coe_pos, "]"] [] ["at", ident hrp, ident hrq, ident rp_pos, ident rq_pos],
  obtain ["⟨", ident Cq, ",", ident hCq0, ",", ident hCq, "⟩", ":", expr «expr∃ , »((Cq «expr > » 0), ∀
    n, «expr ≤ »(«expr * »(nnnorm (q n), «expr ^ »(rq, n)), Cq)), ":=", expr q.nnnorm_mul_pow_le_of_lt_radius hrq.2],
  obtain ["⟨", ident Cp, ",", ident hCp1, ",", ident hCp, "⟩", ":", expr «expr∃ , »((Cp «expr ≥ » 1), ∀
    n, «expr ≤ »(«expr * »(nnnorm (p n), «expr ^ »(rp, n)), Cp))],
  { rcases [expr p.nnnorm_mul_pow_le_of_lt_radius hrp.2, "with", "⟨", ident Cp, ",", "-", ",", ident hCp, "⟩"],
    exact [expr ⟨max Cp 1, le_max_right _ _, λ n, (hCp n).trans (le_max_left _ _)⟩] },
  let [ident r0] [":", expr «exprℝ≥0»()] [":=", expr «expr ⁻¹»(«expr * »(4, Cp))],
  have [ident r0_pos] [":", expr «expr < »(0, r0)] [":=", expr nnreal.inv_pos.2 (mul_pos zero_lt_four (zero_lt_one.trans_le hCp1))],
  set [] [ident r] [":", expr «exprℝ≥0»()] [":="] [expr «expr * »(«expr * »(rp, rq), r0)] [],
  have [ident r_pos] [":", expr «expr < »(0, r)] [":=", expr mul_pos (mul_pos rp_pos rq_pos) r0_pos],
  have [ident I] [":", expr ∀
   i : «exprΣ , »((n : exprℕ()), composition n), «expr ≤ »(«expr * »(nnnorm (q.comp_along_composition p i.2), «expr ^ »(r, i.1)), «expr / »(Cq, «expr ^ »(4, i.1)))] [],
  { rintros ["⟨", ident n, ",", ident c, "⟩"],
    have [ident A] [] [],
    calc
      «expr ≤ »(«expr * »(nnnorm (q c.length), «expr ^ »(rq, n)), «expr * »(nnnorm (q c.length), «expr ^ »(rq, c.length))) : mul_le_mul' le_rfl (pow_le_pow_of_le_one rq.2 hrq.1.le c.length_le)
      «expr ≤ »(..., Cq) : hCq _,
    have [ident B] [] [],
    calc
      «expr = »(«expr * »(«expr∏ , »((i), nnnorm (p (c.blocks_fun i))), «expr ^ »(rp, n)), «expr∏ , »((i), «expr * »(nnnorm (p (c.blocks_fun i)), «expr ^ »(rp, c.blocks_fun i)))) : by simp [] [] ["only"] ["[", expr finset.prod_mul_distrib, ",", expr finset.prod_pow_eq_pow_sum, ",", expr c.sum_blocks_fun, "]"] [] []
      «expr ≤ »(..., «expr∏ , »((i : fin c.length), Cp)) : finset.prod_le_prod' (λ i _, hCp _)
      «expr = »(..., «expr ^ »(Cp, c.length)) : by simp [] [] [] [] [] []
      «expr ≤ »(..., «expr ^ »(Cp, n)) : pow_le_pow hCp1 c.length_le,
    calc
      «expr ≤ »(«expr * »(nnnorm (q.comp_along_composition p c), «expr ^ »(r, n)), «expr * »(«expr * »(nnnorm (q c.length), «expr∏ , »((i), nnnorm (p (c.blocks_fun i)))), «expr ^ »(r, n))) : mul_le_mul' (q.comp_along_composition_nnnorm p c) le_rfl
      «expr = »(..., «expr * »(«expr * »(«expr * »(nnnorm (q c.length), «expr ^ »(rq, n)), «expr * »(«expr∏ , »((i), nnnorm (p (c.blocks_fun i))), «expr ^ »(rp, n))), «expr ^ »(r0, n))) : by { simp [] [] ["only"] ["[", expr r, ",", expr mul_pow, "]"] [] [],
        ac_refl }
      «expr ≤ »(..., «expr * »(«expr * »(Cq, «expr ^ »(Cp, n)), «expr ^ »(r0, n))) : mul_le_mul' (mul_le_mul' A B) le_rfl
      «expr = »(..., «expr / »(Cq, «expr ^ »(4, n))) : begin
        simp [] [] ["only"] ["[", expr r0, "]"] [] [],
        field_simp [] ["[", expr mul_pow, ",", expr (zero_lt_one.trans_le hCp1).ne', "]"] [] [],
        ac_refl
      end },
  refine [expr ⟨r, r_pos, nnreal.summable_of_le I _⟩],
  simp_rw [expr div_eq_mul_inv] [],
  refine [expr summable.mul_left _ _],
  have [] [":", expr ∀
   n : exprℕ(), has_sum (λ
    c : composition n, «expr ⁻¹»((«expr ^ »(4, n) : «exprℝ≥0»()))) «expr / »(«expr ^ »(2, «expr - »(n, 1)), «expr ^ »(4, n))] [],
  { intro [ident n],
    convert [] [expr has_sum_fintype (λ c : composition n, «expr ⁻¹»((«expr ^ »(4, n) : «exprℝ≥0»())))] [],
    simp [] [] [] ["[", expr finset.card_univ, ",", expr composition_card, ",", expr div_eq_mul_inv, "]"] [] [] },
  refine [expr nnreal.summable_sigma.2 ⟨λ n, (this n).summable, (nnreal.summable_nat_add_iff 1).1 _⟩],
  convert [] [expr (nnreal.summable_geometric (nnreal.div_lt_one_of_lt one_lt_two)).mul_left «expr / »(1, 4)] [],
  ext1 [] [ident n],
  rw ["[", expr (this _).tsum_eq, ",", expr add_tsub_cancel_right, "]"] [],
  field_simp [] ["[", "<-", expr mul_assoc, ",", expr pow_succ', ",", expr mul_pow, ",", expr show «expr = »((4 : «exprℝ≥0»()), «expr * »(2, 2)), from (two_mul 2).symm, ",", expr mul_right_comm, "]"] [] []
end

end 

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Bounding below the radius of the composition of two formal multilinear series assuming
summability over all compositions. -/
theorem le_comp_radius_of_summable
(q : formal_multilinear_series 𝕜 F G)
(p : formal_multilinear_series 𝕜 E F)
(r : «exprℝ≥0»())
(hr : summable (λ
  i : «exprΣ , »((n), composition n), «expr * »(nnnorm (q.comp_along_composition p i.2), «expr ^ »(r, i.1)))) : «expr ≤ »((r : «exprℝ≥0∞»()), (q.comp p).radius) :=
begin
  refine [expr le_radius_of_bound_nnreal _ «expr∑' , »((i : «exprΣ , »((n), composition n)), «expr * »(nnnorm (comp_along_composition q p i.snd), «expr ^ »(r, i.fst))) (λ
    n, _)],
  calc
    «expr ≤ »(«expr * »(nnnorm (formal_multilinear_series.comp q p n), «expr ^ »(r, n)), «expr∑' , »((c : composition n), «expr * »(nnnorm (comp_along_composition q p c), «expr ^ »(r, n)))) : begin
      rw ["[", expr tsum_fintype, ",", "<-", expr finset.sum_mul, "]"] [],
      exact [expr mul_le_mul' (nnnorm_sum_le _ _) le_rfl]
    end
    «expr ≤ »(..., «expr∑' , »((i : «exprΣ , »((n : exprℕ()), composition n)), «expr * »(nnnorm (comp_along_composition q p i.snd), «expr ^ »(r, i.fst)))) : nnreal.tsum_comp_le_tsum_of_inj hr sigma_mk_injective
end

/-!
### Composing analytic functions

Now, we will prove that the composition of the partial sums of `q` and `p` up to order `N` is
given by a sum over some large subset of `Σ n, composition n` of `q.comp_along_composition p`, to
deduce that the series for `q.comp p` indeed converges to `g ∘ f` when `q` is a power series for
`g` and `p` is a power series for `f`.

This proof is a big reindexing argument of a sum. Since it is a bit involved, we define first
the source of the change of variables (`comp_partial_source`), its target
(`comp_partial_target`) and the change of variables itself (`comp_change_of_variables`) before
giving the main statement in `comp_partial_sum`. -/


-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Source set in the change of variables to compute the composition of partial sums of formal
power series.
See also `comp_partial_sum`. -/
def comp_partial_sum_source (m M N : exprℕ()) : finset «exprΣ , »((n), fin n → exprℕ()) :=
finset.sigma (finset.Ico m M) (λ n : exprℕ(), fintype.pi_finset (λ i : fin n, finset.Ico 1 N) : _)

@[simp]
theorem mem_comp_partial_sum_source_iff (m M N : ℕ) (i : Σn, Finₓ n → ℕ) :
  i ∈ comp_partial_sum_source m M N ↔ (m ≤ i.1 ∧ i.1 < M) ∧ ∀ (a : Finₓ i.1), 1 ≤ i.2 a ∧ i.2 a < N :=
  by 
    simp only [comp_partial_sum_source, Finset.mem_Ico, Fintype.mem_pi_finset, Finset.mem_sigma, iff_selfₓ]

/-- Change of variables appearing to compute the composition of partial sums of formal
power series -/
def comp_change_of_variables (m M N : ℕ) (i : Σn, Finₓ n → ℕ) (hi : i ∈ comp_partial_sum_source m M N) :
  Σn, Composition n :=
  by 
    rcases i with ⟨n, f⟩
    rw [mem_comp_partial_sum_source_iff] at hi 
    refine'
      ⟨∑j, f j, of_fn fun a => f a, fun i hi' => _,
        by 
          simp [sum_of_fn]⟩
    obtain ⟨j, rfl⟩ : ∃ j : Finₓ n, f j = i
    ·
      rwa [mem_of_fn, Set.mem_range] at hi' 
    exact (hi.2 j).1

@[simp]
theorem comp_change_of_variables_length (m M N : ℕ) {i : Σn, Finₓ n → ℕ} (hi : i ∈ comp_partial_sum_source m M N) :
  Composition.length (comp_change_of_variables m M N i hi).2 = i.1 :=
  by 
    rcases i with ⟨k, blocks_fun⟩
    dsimp [comp_change_of_variables]
    simp only [Composition.length, map_of_fn, length_of_fn]

theorem comp_change_of_variables_blocks_fun (m M N : ℕ) {i : Σn, Finₓ n → ℕ} (hi : i ∈ comp_partial_sum_source m M N)
  (j : Finₓ i.1) :
  (comp_change_of_variables m M N i hi).2.blocksFun ⟨j, (comp_change_of_variables_length m M N hi).symm ▸ j.2⟩ =
    i.2 j :=
  by 
    rcases i with ⟨n, f⟩
    dsimp [Composition.blocksFun, Composition.blocks, comp_change_of_variables]
    simp only [map_of_fn, nth_le_of_fn', Function.comp_app]
    apply congr_argₓ 
    exact Finₓ.eta _ _

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a set. -/
def comp_partial_sum_target_set (m M N : ℕ) : Set (Σn, Composition n) :=
  { i | m ≤ i.2.length ∧ i.2.length < M ∧ ∀ (j : Finₓ i.2.length), i.2.blocksFun j < N }

theorem comp_partial_sum_target_subset_image_comp_partial_sum_source (m M N : ℕ) (i : Σn, Composition n)
  (hi : i ∈ comp_partial_sum_target_set m M N) :
  ∃ (j : _)(hj : j ∈ comp_partial_sum_source m M N), i = comp_change_of_variables m M N j hj :=
  by 
    rcases i with ⟨n, c⟩
    refine' ⟨⟨c.length, c.blocks_fun⟩, _, _⟩
    ·
      simp only [comp_partial_sum_target_set, Set.mem_set_of_eq] at hi 
      simp only [mem_comp_partial_sum_source_iff, hi.left, hi.right, true_andₓ, and_trueₓ]
      exact fun a => c.one_le_blocks' _
    ·
      dsimp [comp_change_of_variables]
      rw [Composition.sigma_eq_iff_blocks_eq]
      simp only [Composition.blocksFun, Composition.blocks, Subtype.coe_eta, nth_le_map']
      convLHS => rw [←of_fn_nth_le c.blocks]

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a finset.
See also `comp_partial_sum`. -/
def comp_partial_sum_target (m M N : ℕ) : Finset (Σn, Composition n) :=
  Set.Finite.toFinset$
    ((Finset.finite_to_set _).dependent_image _).Subset$
      comp_partial_sum_target_subset_image_comp_partial_sum_source m M N

@[simp]
theorem mem_comp_partial_sum_target_iff {m M N : ℕ} {a : Σn, Composition n} :
  a ∈ comp_partial_sum_target m M N ↔ m ≤ a.2.length ∧ a.2.length < M ∧ ∀ (j : Finₓ a.2.length), a.2.blocksFun j < N :=
  by 
    simp [comp_partial_sum_target, comp_partial_sum_target_set]

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `comp_change_of_variables m M N` is a bijection between `comp_partial_sum_source m M N`
and `comp_partial_sum_target m M N`, yielding equal sums for functions that correspond to each
other under the bijection. As `comp_change_of_variables m M N` is a dependent function, stating
that it is a bijection is not directly possible, but the consequence on sums can be stated
more easily. -/
theorem comp_change_of_variables_sum
{α : Type*}
[add_comm_monoid α]
(m M N : exprℕ())
(f : «exprΣ , »((n : exprℕ()), fin n → exprℕ()) → α)
(g : «exprΣ , »((n), composition n) → α)
(h : ∀
 (e)
 (he : «expr ∈ »(e, comp_partial_sum_source m M N)), «expr = »(f e, g (comp_change_of_variables m M N e he))) : «expr = »(«expr∑ in , »((e), comp_partial_sum_source m M N, f e), «expr∑ in , »((e), comp_partial_sum_target m M N, g e)) :=
begin
  apply [expr finset.sum_bij (comp_change_of_variables m M N)],
  { rintros ["⟨", ident k, ",", ident blocks_fun, "⟩", ident H],
    rw [expr mem_comp_partial_sum_source_iff] ["at", ident H],
    simp [] [] ["only"] ["[", expr mem_comp_partial_sum_target_iff, ",", expr composition.length, ",", expr composition.blocks, ",", expr H.left, ",", expr map_of_fn, ",", expr length_of_fn, ",", expr true_and, ",", expr comp_change_of_variables, "]"] [] [],
    assume [binders (j)],
    simp [] [] ["only"] ["[", expr composition.blocks_fun, ",", expr (H.right _).right, ",", expr nth_le_of_fn', "]"] [] [] },
  { rintros ["⟨", ident k, ",", ident blocks_fun, "⟩", ident H],
    rw [expr h] [] },
  { rintros ["⟨", ident k, ",", ident blocks_fun, "⟩", "⟨", ident k', ",", ident blocks_fun', "⟩", ident H, ident H', ident heq],
    obtain [ident rfl, ":", expr «expr = »(k, k')],
    { have [] [] [":=", expr (comp_change_of_variables_length m M N H).symm],
      rwa ["[", expr heq, ",", expr comp_change_of_variables_length, "]"] ["at", ident this] },
    congr,
    funext [ident i],
    calc
      «expr = »(blocks_fun i, (comp_change_of_variables m M N _ H).2.blocks_fun _) : (comp_change_of_variables_blocks_fun m M N H i).symm
      «expr = »(..., (comp_change_of_variables m M N _ H').2.blocks_fun _) : begin
        apply [expr composition.blocks_fun_congr]; try { rw [expr heq] [] },
        refl
      end
      «expr = »(..., blocks_fun' i) : comp_change_of_variables_blocks_fun m M N H' i },
  { assume [binders (i hi)],
    apply [expr comp_partial_sum_target_subset_image_comp_partial_sum_source m M N i],
    simpa [] [] [] ["[", expr comp_partial_sum_target, "]"] [] ["using", expr hi] }
end

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The auxiliary set corresponding to the composition of partial sums asymptotically contains
all possible compositions. -/
theorem comp_partial_sum_target_tendsto_at_top : tendsto (λ N, comp_partial_sum_target 0 N N) at_top at_top :=
begin
  apply [expr monotone.tendsto_at_top_finset],
  { assume [binders (m n hmn a ha)],
    have [] [":", expr ∀ i, «expr < »(i, m) → «expr < »(i, n)] [":=", expr λ i hi, lt_of_lt_of_le hi hmn],
    tidy [] },
  { rintros ["⟨", ident n, ",", ident c, "⟩"],
    simp [] [] ["only"] ["[", expr mem_comp_partial_sum_target_iff, "]"] [] [],
    obtain ["⟨", ident n, ",", ident hn, "⟩", ":", expr bdd_above «expr↑ »(finset.univ.image (λ
       i : fin c.length, c.blocks_fun i)), ":=", expr finset.bdd_above _],
    refine [expr ⟨«expr + »(max n c.length, 1), bot_le, lt_of_le_of_lt (le_max_right n c.length) (lt_add_one _), λ
      j, lt_of_le_of_lt (le_trans _ (le_max_left _ _)) (lt_add_one _)⟩],
    apply [expr hn],
    simp [] [] ["only"] ["[", expr finset.mem_image_of_mem, ",", expr finset.mem_coe, ",", expr finset.mem_univ, "]"] [] [] }
end

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Composing the partial sums of two multilinear series coincides with the sum over all
compositions in `comp_partial_sum_target 0 N N`. This is precisely the motivation for the
definition of `comp_partial_sum_target`. -/
theorem comp_partial_sum
(q : formal_multilinear_series 𝕜 F G)
(p : formal_multilinear_series 𝕜 E F)
(N : exprℕ())
(z : E) : «expr = »(q.partial_sum N «expr∑ in , »((i), finset.Ico 1 N, p i (λ
   j, z)), «expr∑ in , »((i), comp_partial_sum_target 0 N N, q.comp_along_composition p i.2 (λ j, z))) :=
begin
  suffices [ident H] [":", expr «expr = »(«expr∑ in , »((n), finset.range N, «expr∑ in , »((r), fintype.pi_finset (λ
       i : fin n, finset.Ico 1 N), q n (λ
       i : fin n, p (r i) (λ
        j, z)))), «expr∑ in , »((i), comp_partial_sum_target 0 N N, q.comp_along_composition p i.2 (λ j, z)))],
  by simpa [] [] ["only"] ["[", expr formal_multilinear_series.partial_sum, ",", expr continuous_multilinear_map.map_sum_finset, "]"] [] ["using", expr H],
  rw ["[", expr finset.range_eq_Ico, ",", expr finset.sum_sigma', "]"] [],
  apply [expr comp_change_of_variables_sum 0 N N],
  rintros ["⟨", ident k, ",", ident blocks_fun, "⟩", ident H],
  apply [expr congr _ (comp_change_of_variables_length 0 N N H).symm],
  intros [],
  rw ["<-", expr comp_change_of_variables_blocks_fun 0 N N H] [],
  refl
end

end FormalMultilinearSeries

open FormalMultilinearSeries

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two functions `g` and `f` have power series `q` and `p` respectively at `f x` and `x`, then
`g ∘ f` admits the power series `q.comp p` at `x`. -/
theorem has_fpower_series_at.comp
{g : F → G}
{f : E → F}
{q : formal_multilinear_series 𝕜 F G}
{p : formal_multilinear_series 𝕜 E F}
{x : E}
(hg : has_fpower_series_at g q (f x))
(hf : has_fpower_series_at f p x) : has_fpower_series_at «expr ∘ »(g, f) (q.comp p) x :=
begin
  rcases [expr hg, "with", "⟨", ident rg, ",", ident Hg, "⟩"],
  rcases [expr hf, "with", "⟨", ident rf, ",", ident Hf, "⟩"],
  rcases [expr q.comp_summable_nnreal p Hg.radius_pos Hf.radius_pos, "with", "⟨", ident r, ",", ident r_pos, ":", expr «expr < »(0, r), ",", ident hr, "⟩"],
  have [] [":", expr continuous_at f x] [":=", expr Hf.analytic_at.continuous_at],
  obtain ["⟨", ident δ, ",", ident δpos, ",", ident hδ, "⟩", ":", expr «expr∃ , »((δ : «exprℝ≥0∞»())
    (H : «expr < »(0, δ)), ∀ {z : E}, «expr ∈ »(z, emetric.ball x δ) → «expr ∈ »(f z, emetric.ball (f x) rg))],
  { have [] [":", expr «expr ∈ »(emetric.ball (f x) rg, expr𝓝() (f x))] [":=", expr emetric.ball_mem_nhds _ Hg.r_pos],
    rcases [expr emetric.mem_nhds_iff.1 (Hf.analytic_at.continuous_at this), "with", "⟨", ident δ, ",", ident δpos, ",", ident Hδ, "⟩"],
    exact [expr ⟨δ, δpos, λ z hz, Hδ hz⟩] },
  let [ident rf'] [] [":=", expr min rf δ],
  have [ident min_pos] [":", expr «expr < »(0, min rf' r)] [],
  by simp [] [] ["only"] ["[", expr r_pos, ",", expr Hf.r_pos, ",", expr δpos, ",", expr lt_min_iff, ",", expr ennreal.coe_pos, ",", expr and_self, "]"] [] [],
  refine [expr ⟨min rf' r, _⟩],
  refine [expr ⟨le_trans (min_le_right rf' r) (formal_multilinear_series.le_comp_radius_of_summable q p r hr), min_pos, λ
    y hy, _⟩],
  have [ident y_mem] [":", expr «expr ∈ »(y, emetric.ball (0 : E) rf)] [":=", expr emetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hy],
  have [ident fy_mem] [":", expr «expr ∈ »(f «expr + »(x, y), emetric.ball (f x) rg)] [],
  { apply [expr hδ],
    have [] [":", expr «expr ∈ »(y, emetric.ball (0 : E) δ)] [":=", expr emetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)) hy],
    simpa [] [] [] ["[", expr edist_eq_coe_nnnorm_sub, ",", expr edist_eq_coe_nnnorm, "]"] [] [] },
  have [ident A] [":", expr tendsto (λ
    n, «expr∑ in , »((a), finset.Ico 1 n, p a (λ b, y))) at_top (expr𝓝() «expr - »(f «expr + »(x, y), f x))] [],
  { have [ident L] [":", expr «expr∀ᶠ in , »((n), at_top, «expr = »(«expr - »(«expr∑ in , »((a), finset.range n, p a (λ
          b, y)), f x), «expr∑ in , »((a), finset.Ico 1 n, p a (λ b, y))))] [],
    { rw [expr eventually_at_top] [],
      refine [expr ⟨1, λ n hn, _⟩],
      symmetry,
      rw ["[", expr eq_sub_iff_add_eq', ",", expr finset.range_eq_Ico, ",", "<-", expr Hf.coeff_zero (λ
        i, y), ",", expr finset.sum_eq_sum_Ico_succ_bot hn, "]"] [] },
    have [] [":", expr tendsto (λ
      n, «expr - »(«expr∑ in , »((a), finset.range n, p a (λ
         b, y)), f x)) at_top (expr𝓝() «expr - »(f «expr + »(x, y), f x))] [":=", expr (Hf.has_sum y_mem).tendsto_sum_nat.sub tendsto_const_nhds],
    exact [expr tendsto.congr' L this] },
  have [ident B] [":", expr tendsto (λ
    n, q.partial_sum n «expr∑ in , »((a), finset.Ico 1 n, p a (λ b, y))) at_top (expr𝓝() (g (f «expr + »(x, y))))] [],
  { have [ident B₁] [":", expr continuous_at (λ z : F, g «expr + »(f x, z)) «expr - »(f «expr + »(x, y), f x)] [],
    { refine [expr continuous_at.comp _ (continuous_const.add continuous_id).continuous_at],
      simp [] [] ["only"] ["[", expr add_sub_cancel'_right, ",", expr id.def, "]"] [] [],
      exact [expr Hg.continuous_on.continuous_at (is_open.mem_nhds emetric.is_open_ball fy_mem)] },
    have [ident B₂] [":", expr «expr ∈ »(«expr - »(f «expr + »(x, y), f x), emetric.ball (0 : F) rg)] [],
    by simpa [] [] [] ["[", expr edist_eq_coe_nnnorm, ",", expr edist_eq_coe_nnnorm_sub, "]"] [] ["using", expr fy_mem],
    rw ["[", "<-", expr emetric.is_open_ball.nhds_within_eq B₂, "]"] ["at", ident A],
    convert [] [expr Hg.tendsto_locally_uniformly_on.tendsto_comp B₁.continuous_within_at B₂ A] [],
    simp [] [] ["only"] ["[", expr add_sub_cancel'_right, "]"] [] [] },
  have [ident C] [":", expr tendsto (λ
    n, «expr∑ in , »((i), comp_partial_sum_target 0 n n, q.comp_along_composition p i.2 (λ
      j, y))) at_top (expr𝓝() (g (f «expr + »(x, y))))] [],
  by simpa [] [] [] ["[", expr comp_partial_sum, "]"] [] ["using", expr B],
  have [ident D] [":", expr has_sum (λ
    i : «exprΣ , »((n), composition n), q.comp_along_composition p i.2 (λ j, y)) (g (f «expr + »(x, y)))] [],
  { have [ident cau] [":", expr cauchy_seq (λ
      s : finset «exprΣ , »((n), composition n), «expr∑ in , »((i), s, q.comp_along_composition p i.2 (λ j, y)))] [],
    { apply [expr cauchy_seq_finset_of_norm_bounded _ (nnreal.summable_coe.2 hr) _],
      simp [] [] ["only"] ["[", expr coe_nnnorm, ",", expr nnreal.coe_mul, ",", expr nnreal.coe_pow, "]"] [] [],
      rintros ["⟨", ident n, ",", ident c, "⟩"],
      calc
        «expr ≤ »(«expr∥ ∥»(comp_along_composition q p c (λ
           j : fin n, y)), «expr * »(«expr∥ ∥»(comp_along_composition q p c), «expr∏ , »((j : fin n), «expr∥ ∥»(y)))) : by apply [expr continuous_multilinear_map.le_op_norm]
        «expr ≤ »(..., «expr * »(«expr∥ ∥»(comp_along_composition q p c), «expr ^ »((r : exprℝ()), n))) : begin
          apply [expr mul_le_mul_of_nonneg_left _ (norm_nonneg _)],
          rw ["[", expr finset.prod_const, ",", expr finset.card_fin, "]"] [],
          apply [expr pow_le_pow_of_le_left (norm_nonneg _)],
          rw ["[", expr emetric.mem_ball, ",", expr edist_eq_coe_nnnorm, "]"] ["at", ident hy],
          have [] [] [":=", expr le_trans (le_of_lt hy) (min_le_right _ _)],
          rwa ["[", expr ennreal.coe_le_coe, ",", "<-", expr nnreal.coe_le_coe, ",", expr coe_nnnorm, "]"] ["at", ident this]
        end },
    exact [expr tendsto_nhds_of_cauchy_seq_of_subseq cau comp_partial_sum_target_tendsto_at_top C] },
  have [ident E] [":", expr has_sum (λ n, q.comp p n (λ j, y)) (g (f «expr + »(x, y)))] [],
  { apply [expr D.sigma],
    assume [binders (n)],
    dsimp [] ["[", expr formal_multilinear_series.comp, "]"] [] [],
    convert [] [expr has_sum_fintype _] [],
    simp [] [] ["only"] ["[", expr continuous_multilinear_map.sum_apply, "]"] [] [],
    refl },
  exact [expr E]
end

/-- If two functions `g` and `f` are analytic respectively at `f x` and `x`, then `g ∘ f` is
analytic at `x`. -/
theorem AnalyticAt.comp {g : F → G} {f : E → F} {x : E} (hg : AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) :
  AnalyticAt 𝕜 (g ∘ f) x :=
  let ⟨q, hq⟩ := hg 
  let ⟨p, hp⟩ := hf
  (hq.comp hp).AnalyticAt

/-!
### Associativity of the composition of formal multilinear series

In this paragraph, we prove the associativity of the composition of formal power series.
By definition,
```
(r.comp q).comp p n v
= ∑_{i₁ + ... + iₖ = n} (r.comp q)ₖ (p_{i₁} (v₀, ..., v_{i₁ -1}), p_{i₂} (...), ..., p_{iₖ}(...))
= ∑_{a : composition n} (r.comp q) a.length (apply_composition p a v)
```
decomposing `r.comp q` in the same way, we get
```
(r.comp q).comp p n v
= ∑_{a : composition n} ∑_{b : composition a.length}
  r b.length (apply_composition q b (apply_composition p a v))
```
On the other hand,
```
r.comp (q.comp p) n v = ∑_{c : composition n} r c.length (apply_composition (q.comp p) c v)
```
Here, `apply_composition (q.comp p) c v` is a vector of length `c.length`, whose `i`-th term is
given by `(q.comp p) (c.blocks_fun i) (v_l, v_{l+1}, ..., v_{m-1})` where `{l, ..., m-1}` is the
`i`-th block in the composition `c`, of length `c.blocks_fun i` by definition. To compute this term,
we expand it as `∑_{dᵢ : composition (c.blocks_fun i)} q dᵢ.length (apply_composition p dᵢ v')`,
where `v' = (v_l, v_{l+1}, ..., v_{m-1})`. Therefore, we get
```
r.comp (q.comp p) n v =
∑_{c : composition n} ∑_{d₀ : composition (c.blocks_fun 0),
  ..., d_{c.length - 1} : composition (c.blocks_fun (c.length - 1))}
  r c.length (λ i, q dᵢ.length (apply_composition p dᵢ v'ᵢ))
```
To show that these terms coincide, we need to explain how to reindex the sums to put them in
bijection (and then the terms we are summing will correspond to each other). Suppose we have a
composition `a` of `n`, and a composition `b` of `a.length`. Then `b` indicates how to group
together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of blocks
can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by saying that
each `dᵢ` is one single block. Conversely, if one starts from `c` and the `dᵢ`s, one can concatenate
the `dᵢ`s to obtain a composition `a` of `n`, and register the lengths of the `dᵢ`s in a composition
`b` of `a.length`.

An example might be enlightening. Suppose `a = [2, 2, 3, 4, 2]`. It is a composition of
length 5 of 13. The content of the blocks may be represented as `0011222333344`.
Now take `b = [2, 3]` as a composition of `a.length = 5`. It says that the first 2 blocks of `a`
should be merged, and the last 3 blocks of `a` should be merged, giving a new composition of `13`
made of two blocks of length `4` and `9`, i.e., `c = [4, 9]`. But one can also remember that
the new first block was initially made of two blocks of size `2`, so `d₀ = [2, 2]`, and the new
second block was initially made of three blocks of size `3`, `4` and `2`, so `d₁ = [3, 4, 2]`.

This equivalence is called `composition.sigma_equiv_sigma_pi n` below.

We start with preliminary results on compositions, of a very specialized nature, then define the
equivalence `composition.sigma_equiv_sigma_pi n`, and we deduce finally the associativity of
composition of formal multilinear series in `formal_multilinear_series.comp_assoc`.
-/


namespace Composition

variable{n : ℕ}

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Rewriting equality in the dependent type `Σ (a : composition n), composition a.length)` in
non-dependent terms with lists, requiring that the blocks coincide. -/
theorem sigma_composition_eq_iff
(i
 j : «exprΣ , »((a : composition n), composition a.length)) : «expr ↔ »(«expr = »(i, j), «expr ∧ »(«expr = »(i.1.blocks, j.1.blocks), «expr = »(i.2.blocks, j.2.blocks))) :=
begin
  refine [expr ⟨by rintro [ident rfl]; exact [expr ⟨rfl, rfl⟩], _⟩],
  rcases [expr i, "with", "⟨", ident a, ",", ident b, "⟩"],
  rcases [expr j, "with", "⟨", ident a', ",", ident b', "⟩"],
  rintros ["⟨", ident h, ",", ident h', "⟩"],
  have [ident H] [":", expr «expr = »(a, a')] [],
  by { ext1 [] [],
    exact [expr h] },
  induction [expr H] [] [] [],
  congr,
  ext1 [] [],
  exact [expr h']
end

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Rewriting equality in the dependent type
`Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i)` in
non-dependent terms with lists, requiring that the lists of blocks coincide. -/
theorem sigma_pi_composition_eq_iff
(u
 v : «exprΣ , »((c : composition n), ∀
  i : fin c.length, composition (c.blocks_fun i))) : «expr ↔ »(«expr = »(u, v), «expr = »(of_fn (λ
   i, (u.2 i).blocks), of_fn (λ i, (v.2 i).blocks))) :=
begin
  refine [expr ⟨λ H, by rw [expr H] [], λ H, _⟩],
  rcases [expr u, "with", "⟨", ident a, ",", ident b, "⟩"],
  rcases [expr v, "with", "⟨", ident a', ",", ident b', "⟩"],
  dsimp [] [] [] ["at", ident H],
  have [ident h] [":", expr «expr = »(a, a')] [],
  { ext1 [] [],
    have [] [":", expr «expr = »(map list.sum (of_fn (λ
        i : fin (composition.length a), (b i).blocks)), map list.sum (of_fn (λ
        i : fin (composition.length a'), (b' i).blocks)))] [],
    by rw [expr H] [],
    simp [] [] ["only"] ["[", expr map_of_fn, "]"] [] ["at", ident this],
    change [expr «expr = »(of_fn (λ
       i : fin (composition.length a), (b i).blocks.sum), of_fn (λ
       i : fin (composition.length a'), (b' i).blocks.sum))] [] ["at", ident this],
    simpa [] [] [] ["[", expr composition.blocks_sum, ",", expr composition.of_fn_blocks_fun, "]"] [] ["using", expr this] },
  induction [expr h] [] [] [],
  simp [] [] ["only"] ["[", expr true_and, ",", expr eq_self_iff_true, ",", expr heq_iff_eq, "]"] [] [],
  ext [] [ident i] [":", 2],
  have [] [":", expr «expr = »(nth_le (of_fn (λ
      i : fin (composition.length a), (b i).blocks)) i (by simp [] [] [] ["[", expr i.is_lt, "]"] [] []), nth_le (of_fn (λ
      i : fin (composition.length a), (b' i).blocks)) i (by simp [] [] [] ["[", expr i.is_lt, "]"] [] []))] [":=", expr nth_le_of_eq H _],
  rwa ["[", expr nth_le_of_fn, ",", expr nth_le_of_fn, "]"] ["at", ident this]
end

/-- When `a` is a composition of `n` and `b` is a composition of `a.length`, `a.gather b` is the
composition of `n` obtained by gathering all the blocks of `a` corresponding to a block of `b`.
For instance, if `a = [6, 5, 3, 5, 2]` and `b = [2, 3]`, one should gather together
the first two blocks of `a` and its last three blocks, giving `a.gather b = [11, 10]`. -/
def gather (a : Composition n) (b : Composition a.length) : Composition n :=
  { blocks := (a.blocks.split_wrt_composition b).map Sum,
    blocks_pos :=
      by 
        rw [forall_mem_map_iff]
        intro j hj 
        suffices H : ∀ i (_ : i ∈ j), 1 ≤ i 
        exact
          calc 0 < j.length := length_pos_of_mem_split_wrt_composition hj 
            _ ≤ j.sum := length_le_sum_of_one_le _ H 
            
        intro i hi 
        apply a.one_le_blocks 
        rw [←a.blocks.join_split_wrt_composition b]
        exact mem_join_of_mem hj hi,
    blocks_sum :=
      by 
        rw [←sum_join, join_split_wrt_composition, a.blocks_sum] }

theorem length_gather (a : Composition n) (b : Composition a.length) : length (a.gather b) = b.length :=
  show (map List.sum (a.blocks.split_wrt_composition b)).length = b.blocks.length by 
    rw [length_map, length_split_wrt_composition]

/-- An auxiliary function used in the definition of `sigma_equiv_sigma_pi` below, associating to
two compositions `a` of `n` and `b` of `a.length`, and an index `i` bounded by the length of
`a.gather b`, the subcomposition of `a` made of those blocks belonging to the `i`-th block of
`a.gather b`. -/
def sigma_composition_aux (a : Composition n) (b : Composition a.length) (i : Finₓ (a.gather b).length) :
  Composition ((a.gather b).blocksFun i) :=
  { blocks :=
      nth_le (a.blocks.split_wrt_composition b) i
        (by 
          rw [length_split_wrt_composition, ←length_gather]
          exact i.2),
    blocks_pos :=
      fun i hi =>
        a.blocks_pos
          (by 
            rw [←a.blocks.join_split_wrt_composition b]
            exact mem_join_of_mem (nth_le_mem _ _ _) hi),
    blocks_sum :=
      by 
        simp only [Composition.blocksFun, nth_le_map', Composition.gather] }

theorem length_sigma_composition_aux (a : Composition n) (b : Composition a.length) (i : Finₓ b.length) :
  Composition.length (Composition.sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ i.2⟩) =
    Composition.blocksFun b i :=
  show List.length (nth_le (split_wrt_composition a.blocks b) i _) = blocks_fun b i by 
    rw [nth_le_map_rev List.length, nth_le_of_eq (map_length_split_wrt_composition _ _)]
    rfl

theorem blocks_fun_sigma_composition_aux (a : Composition n) (b : Composition a.length) (i : Finₓ b.length)
  (j : Finₓ (blocks_fun b i)) :
  blocks_fun (sigma_composition_aux a b ⟨i, (length_gather a b).symm ▸ i.2⟩)
      ⟨j, (length_sigma_composition_aux a b i).symm ▸ j.2⟩ =
    blocks_fun a (Embedding b i j) :=
  show nth_le (nth_le _ _ _) _ _ = nth_le a.blocks _ _ by 
    rw [nth_le_of_eq (nth_le_split_wrt_composition _ _ _), nth_le_drop', nth_le_take']
    rfl

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Auxiliary lemma to prove that the composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Grouping together some
blocks of `a` according to `b` as in `a.gather b`, one can compute the total size of the blocks
of `a` up to an index `size_up_to b i + j` (where the `j` corresponds to a set of blocks of `a`
that do not fill a whole block of `a.gather b`). The first part corresponds to a sum of blocks
in `a.gather b`, and the second one to a sum of blocks in the next block of
`sigma_composition_aux a b`. This is the content of this lemma. -/
theorem size_up_to_size_up_to_add
(a : composition n)
(b : composition a.length)
{i j : exprℕ()}
(hi : «expr < »(i, b.length))
(hj : «expr < »(j, blocks_fun b ⟨i, hi⟩)) : «expr = »(size_up_to a «expr + »(size_up_to b i, j), «expr + »(size_up_to (a.gather b) i, size_up_to (sigma_composition_aux a b ⟨i, «expr ▸ »((length_gather a b).symm, hi)⟩) j)) :=
begin
  induction [expr j] [] ["with", ident j, ident IHj] [],
  { show [expr «expr = »(sum (take (b.blocks.take i).sum a.blocks), sum (take i (map sum (split_wrt_composition a.blocks b))))],
    induction [expr i] [] ["with", ident i, ident IH] [],
    { refl },
    { have [ident A] [":", expr «expr < »(i, b.length)] [":=", expr nat.lt_of_succ_lt hi],
      have [ident B] [":", expr «expr < »(i, list.length (map list.sum (split_wrt_composition a.blocks b)))] [],
      by simp [] [] [] ["[", expr A, "]"] [] [],
      have [ident C] [":", expr «expr < »(0, blocks_fun b ⟨i, A⟩)] [":=", expr composition.blocks_pos' _ _ _],
      rw ["[", expr sum_take_succ _ _ B, ",", "<-", expr IH A C, "]"] [],
      have [] [":", expr «expr = »(take (sum (take i b.blocks)) a.blocks, take (sum (take i b.blocks)) (take (sum (take «expr + »(i, 1) b.blocks)) a.blocks))] [],
      { rw ["[", expr take_take, ",", expr min_eq_left, "]"] [],
        apply [expr monotone_sum_take _ (nat.le_succ _)] },
      rw ["[", expr this, ",", expr nth_le_map', ",", expr nth_le_split_wrt_composition, ",", "<-", expr take_append_drop (sum (take i b.blocks)) (take (sum (take (nat.succ i) b.blocks)) a.blocks), ",", expr sum_append, "]"] [],
      congr,
      rw ["[", expr take_append_drop, "]"] [] } },
  { have [ident A] [":", expr «expr < »(j, blocks_fun b ⟨i, hi⟩)] [":=", expr lt_trans (lt_add_one j) hj],
    have [ident B] [":", expr «expr < »(j, length (sigma_composition_aux a b ⟨i, «expr ▸ »((length_gather a b).symm, hi)⟩))] [],
    by { convert [] [expr A] [],
      rw ["[", "<-", expr length_sigma_composition_aux, "]"] [],
      refl },
    have [ident C] [":", expr «expr < »(«expr + »(size_up_to b i, j), size_up_to b «expr + »(i, 1))] [],
    { simp [] [] ["only"] ["[", expr size_up_to_succ b hi, ",", expr add_lt_add_iff_left, "]"] [] [],
      exact [expr A] },
    have [ident D] [":", expr «expr < »(«expr + »(size_up_to b i, j), length a)] [":=", expr lt_of_lt_of_le C (b.size_up_to_le _)],
    have [] [":", expr «expr = »(«expr + »(size_up_to b i, nat.succ j), «expr + »(size_up_to b i, j).succ)] [":=", expr rfl],
    rw ["[", expr this, ",", expr size_up_to_succ _ D, ",", expr IHj A, ",", expr size_up_to_succ _ B, "]"] [],
    simp [] [] ["only"] ["[", expr sigma_composition_aux, ",", expr add_assoc, ",", expr add_left_inj, ",", expr fin.coe_mk, "]"] [] [],
    rw ["[", expr nth_le_of_eq (nth_le_split_wrt_composition _ _ _), ",", expr nth_le_drop', ",", expr nth_le_take _ _ C, "]"] [] }
end

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Natural equivalence between `(Σ (a : composition n), composition a.length)` and
`(Σ (c : composition n), Π (i : fin c.length), composition (c.blocks_fun i))`, that shows up as a
change of variables in the proof that composition of formal multilinear series is associative.

Consider a composition `a` of `n` and a composition `b` of `a.length`. Then `b` indicates how to
group together some blocks of `a`, giving altogether `b.length` blocks of blocks. These blocks of
blocks can be called `d₀, ..., d_{a.length - 1}`, and one obtains a composition `c` of `n` by
saying that each `dᵢ` is one single block. The map `⟨a, b⟩ → ⟨c, (d₀, ..., d_{a.length - 1})⟩` is
the direct map in the equiv.

Conversely, if one starts from `c` and the `dᵢ`s, one can join the `dᵢ`s to obtain a composition
`a` of `n`, and register the lengths of the `dᵢ`s in a composition `b` of `a.length`. This is the
inverse map of the equiv.
-/
def sigma_equiv_sigma_pi
(n : exprℕ()) : «expr ≃ »(«exprΣ , »((a : composition n), composition a.length), «exprΣ , »((c : composition n), ∀
  i : fin c.length, composition (c.blocks_fun i))) :=
{ to_fun := λ i, ⟨i.1.gather i.2, i.1.sigma_composition_aux i.2⟩,
  inv_fun := λ
  i, ⟨{ blocks := (of_fn (λ j, (i.2 j).blocks)).join,
     blocks_pos := begin
       simp [] [] ["only"] ["[", expr and_imp, ",", expr list.mem_join, ",", expr exists_imp_distrib, ",", expr forall_mem_of_fn_iff, "]"] [] [],
       exact [expr λ i j hj, composition.blocks_pos _ hj]
     end,
     blocks_sum := by simp [] [] [] ["[", expr sum_of_fn, ",", expr composition.blocks_sum, ",", expr composition.sum_blocks_fun, "]"] [] [] }, { blocks := of_fn (λ
      j, (i.2 j).length),
     blocks_pos := forall_mem_of_fn_iff.2 (λ j, composition.length_pos_of_pos _ (composition.blocks_pos' _ _ _)),
     blocks_sum := by { dsimp ["only"] ["[", expr composition.length, "]"] [] [],
       simp [] [] [] ["[", expr sum_of_fn, "]"] [] [] } }⟩,
  left_inv := begin
    rintros ["⟨", ident a, ",", ident b, "⟩"],
    rw [expr sigma_composition_eq_iff] [],
    dsimp [] [] [] [],
    split,
    { have [ident A] [] [":=", expr length_map list.sum (split_wrt_composition a.blocks b)],
      conv_rhs [] [] { rw ["[", "<-", expr join_split_wrt_composition a.blocks b, ",", "<-", expr of_fn_nth_le (split_wrt_composition a.blocks b), "]"] },
      congr,
      { exact [expr A] },
      { exact [expr (fin.heq_fun_iff A).2 (λ i, rfl)] } },
    { have [ident B] [":", expr «expr = »(composition.length (composition.gather a b), list.length b.blocks)] [":=", expr composition.length_gather _ _],
      conv_rhs [] [] { rw ["[", "<-", expr of_fn_nth_le b.blocks, "]"] },
      congr' [1] [],
      apply [expr (fin.heq_fun_iff B).2 (λ i, _)],
      rw ["[", expr sigma_composition_aux, ",", expr composition.length, ",", expr nth_le_map_rev list.length, ",", expr nth_le_of_eq (map_length_split_wrt_composition _ _), "]"] [],
      refl }
  end,
  right_inv := begin
    rintros ["⟨", ident c, ",", ident d, "⟩"],
    have [] [":", expr «expr = »(map list.sum (of_fn (λ i : fin (composition.length c), (d i).blocks)), c.blocks)] [],
    by simp [] [] [] ["[", expr map_of_fn, ",", expr («expr ∘ »), ",", expr composition.blocks_sum, ",", expr composition.of_fn_blocks_fun, "]"] [] [],
    rw [expr sigma_pi_composition_eq_iff] [],
    dsimp [] [] [] [],
    congr,
    { ext1 [] [],
      dsimp [] ["[", expr composition.gather, "]"] [] [],
      rwa [expr split_wrt_composition_join] [],
      simp [] [] ["only"] ["[", expr map_of_fn, "]"] [] [] },
    { rw [expr fin.heq_fun_iff] [],
      { assume [binders (i)],
        dsimp [] ["[", expr composition.sigma_composition_aux, "]"] [] [],
        rw ["[", expr nth_le_of_eq (split_wrt_composition_join _ _ _), "]"] [],
        { simp [] [] ["only"] ["[", expr nth_le_of_fn', "]"] [] [] },
        { simp [] [] ["only"] ["[", expr map_of_fn, "]"] [] [] } },
      { congr,
        ext1 [] [],
        dsimp [] ["[", expr composition.gather, "]"] [] [],
        rwa [expr split_wrt_composition_join] [],
        simp [] [] ["only"] ["[", expr map_of_fn, "]"] [] [] } }
  end }

end Composition

namespace FormalMultilinearSeries

open Composition

-- error in Analysis.Analytic.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem comp_assoc
(r : formal_multilinear_series 𝕜 G H)
(q : formal_multilinear_series 𝕜 F G)
(p : formal_multilinear_series 𝕜 E F) : «expr = »((r.comp q).comp p, r.comp (q.comp p)) :=
begin
  ext [] [ident n, ident v] [],
  let [ident f] [":", expr «exprΣ , »((a : composition n), composition a.length) → H] [":=", expr λ
   c, r c.2.length (apply_composition q c.2 (apply_composition p c.1 v))],
  let [ident g] [":", expr «exprΣ , »((c : composition n), ∀
    i : fin c.length, composition (c.blocks_fun i)) → H] [":=", expr λ
   c, r c.1.length (λ
    i : fin c.1.length, q (c.2 i).length (apply_composition p (c.2 i) «expr ∘ »(v, c.1.embedding i)))],
  suffices [] [":", expr «expr = »(«expr∑ , »((c), f c), «expr∑ , »((c), g c))],
  by simpa [] [] ["only"] ["[", expr formal_multilinear_series.comp, ",", expr continuous_multilinear_map.sum_apply, ",", expr comp_along_composition_apply, ",", expr continuous_multilinear_map.map_sum, ",", expr finset.sum_sigma', ",", expr apply_composition, "]"] [] [],
  rw ["<-", expr (sigma_equiv_sigma_pi n).sum_comp] [],
  apply [expr finset.sum_congr rfl],
  rintros ["⟨", ident a, ",", ident b, "⟩", "_"],
  dsimp [] ["[", expr f, ",", expr g, ",", expr sigma_equiv_sigma_pi, "]"] [] [],
  apply [expr r.congr (composition.length_gather a b).symm],
  intros [ident i, ident hi1, ident hi2],
  apply [expr q.congr (length_sigma_composition_aux a b _).symm],
  intros [ident j, ident hj1, ident hj2],
  apply [expr p.congr (blocks_fun_sigma_composition_aux a b _ _).symm],
  intros [ident k, ident hk1, ident hk2],
  refine [expr congr_arg v (fin.eq_of_veq _)],
  dsimp [] ["[", expr composition.embedding, "]"] [] [],
  rw ["[", expr size_up_to_size_up_to_add _ _ hi1 hj1, ",", expr add_assoc, "]"] []
end

end FormalMultilinearSeries

