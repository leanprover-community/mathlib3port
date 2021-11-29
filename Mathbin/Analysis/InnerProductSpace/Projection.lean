import Mathbin.Analysis.InnerProductSpace.Basic 
import Mathbin.Analysis.Convex.Basic

/-!
# The orthogonal projection

Given a nonempty complete subspace `K` of an inner product space `E`, this file constructs
`orthogonal_projection K : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`.  This map
satisfies: for any point `u` in `E`, the point `v = orthogonal_projection K u` in `K` minimizes the
distance `∥u - v∥` to `u`.

Also a linear isometry equivalence `reflection K : E ≃ₗᵢ[𝕜] E` is constructed, by choosing, for
each `u : E`, the point `reflection K u` to satisfy
`u + (reflection K u) = 2 • orthogonal_projection K u`.

Basic API for `orthogonal_projection` and `reflection` is developed.

Next, the orthogonal projection is used to prove a series of more subtle lemmas about the
the orthogonal complement of complete subspaces of `E` (the orthogonal complement itself was
defined in `analysis.inner_product_space.basic`); the lemma
`submodule.sup_orthogonal_of_is_complete`, stating that for a complete subspace `K` of `E` we have
`K ⊔ Kᗮ = ⊤`, is a typical example.

The last section covers orthonormal bases, Hilbert bases, etc. The lemma
`maximal_orthonormal_iff_dense_span`, whose proof requires the theory on the orthogonal complement
developed earlier in this file, states that an orthonormal set in an inner product space is
maximal, if and only if its span is dense (i.e., iff it is Hilbert basis, although we do not make
that definition).  Various consequences are stated, including that if `E` is finite-dimensional
then a maximal orthonormal set is a basis (`maximal_orthonormal_iff_basis_of_finite_dimensional`).

## References

The orthogonal projection construction is adapted from
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/


noncomputable theory

open IsROrC Real Filter

open_locale BigOperators TopologicalSpace

variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

local notation "absR" => HasAbs.abs

/-! ### Orthogonal projection in inner product spaces -/


-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Existence of minimizers
Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
 -/
theorem exists_norm_eq_infi_of_complete_convex
{K : set F}
(ne : K.nonempty)
(h₁ : is_complete K)
(h₂ : convex exprℝ() K) : ∀
u : F, «expr∃ , »((v «expr ∈ » K), «expr = »(«expr∥ ∥»(«expr - »(u, v)), «expr⨅ , »((w : K), «expr∥ ∥»(«expr - »(u, w))))) :=
assume u, begin
  let [ident δ] [] [":=", expr «expr⨅ , »((w : K), «expr∥ ∥»(«expr - »(u, w)))],
  letI [] [":", expr nonempty K] [":=", expr ne.to_subtype],
  have [ident zero_le_δ] [":", expr «expr ≤ »(0, δ)] [":=", expr le_cinfi (λ _, norm_nonneg _)],
  have [ident δ_le] [":", expr ∀ w : K, «expr ≤ »(δ, «expr∥ ∥»(«expr - »(u, w)))] [],
  from [expr cinfi_le ⟨0, «expr $ »(set.forall_range_iff.2, λ _, norm_nonneg _)⟩],
  have [ident δ_le'] [":", expr ∀
   w «expr ∈ » K, «expr ≤ »(δ, «expr∥ ∥»(«expr - »(u, w)))] [":=", expr assume w hw, δ_le ⟨w, hw⟩],
  have [ident exists_seq] [":", expr «expr∃ , »((w : exprℕ() → K), ∀
    n, «expr < »(«expr∥ ∥»(«expr - »(u, w n)), «expr + »(δ, «expr / »(1, «expr + »(n, 1)))))] [],
  { have [ident hδ] [":", expr ∀ n : exprℕ(), «expr < »(δ, «expr + »(δ, «expr / »(1, «expr + »(n, 1))))] [],
    from [expr λ n, lt_add_of_le_of_pos (le_refl _) nat.one_div_pos_of_nat],
    have [ident h] [] [":=", expr λ n, exists_lt_of_cinfi_lt (hδ n)],
    let [ident w] [":", expr exprℕ() → K] [":=", expr λ n, classical.some (h n)],
    exact [expr ⟨w, λ n, classical.some_spec (h n)⟩] },
  rcases [expr exists_seq, "with", "⟨", ident w, ",", ident hw, "⟩"],
  have [ident norm_tendsto] [":", expr tendsto (λ n, «expr∥ ∥»(«expr - »(u, w n))) at_top (nhds δ)] [],
  { have [ident h] [":", expr tendsto (λ n : exprℕ(), δ) at_top (nhds δ)] [":=", expr tendsto_const_nhds],
    have [ident h'] [":", expr tendsto (λ n : exprℕ(), «expr + »(δ, «expr / »(1, «expr + »(n, 1)))) at_top (nhds δ)] [],
    { convert [] [expr h.add tendsto_one_div_add_at_top_nhds_0_nat] [],
      simp [] [] ["only"] ["[", expr add_zero, "]"] [] [] },
    exact [expr tendsto_of_tendsto_of_tendsto_of_le_of_le h h' (λ x, δ_le _) (λ x, le_of_lt (hw _))] },
  have [ident seq_is_cauchy] [":", expr cauchy_seq (λ n, (w n : F))] [],
  { rw [expr cauchy_seq_iff_le_tendsto_0] [],
    let [ident b] [] [":=", expr λ
     n : exprℕ(), «expr + »(«expr * »(«expr * »(8, δ), «expr / »(1, «expr + »(n, 1))), «expr * »(«expr * »(4, «expr / »(1, «expr + »(n, 1))), «expr / »(1, «expr + »(n, 1))))],
    use [expr λ n, sqrt (b n)],
    split,
    assume [binders (n)],
    exact [expr sqrt_nonneg _],
    split,
    assume [binders (p q N hp hq)],
    let [ident wp] [] [":=", expr (w p : F)],
    let [ident wq] [] [":=", expr (w q : F)],
    let [ident a] [] [":=", expr «expr - »(u, wq)],
    let [ident b] [] [":=", expr «expr - »(u, wp)],
    let [ident half] [] [":=", expr «expr / »(1, (2 : exprℝ()))],
    let [ident div] [] [":=", expr «expr / »(1, «expr + »((N : exprℝ()), 1))],
    have [] [":", expr «expr = »(«expr + »(«expr * »(«expr * »(4, «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr * »(«expr∥ ∥»(«expr - »(wp, wq)), «expr∥ ∥»(«expr - »(wp, wq)))), «expr * »(2, «expr + »(«expr * »(«expr∥ ∥»(a), «expr∥ ∥»(a)), «expr * »(«expr∥ ∥»(b), «expr∥ ∥»(b)))))] [":=", expr calc
       «expr = »(«expr + »(«expr * »(«expr * »(4, «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr * »(«expr∥ ∥»(«expr - »(wp, wq)), «expr∥ ∥»(«expr - »(wp, wq)))), «expr + »(«expr * »(«expr * »(2, «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr * »(2, «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp)))))), «expr * »(«expr∥ ∥»(«expr - »(wp, wq)), «expr∥ ∥»(«expr - »(wp, wq))))) : by ring []
       «expr = »(..., «expr + »(«expr * »(«expr * »(exprabsR() (2 : exprℝ()), «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr * »(exprabsR() (2 : exprℝ()), «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp)))))), «expr * »(«expr∥ ∥»(«expr - »(wp, wq)), «expr∥ ∥»(«expr - »(wp, wq))))) : by { rw [expr _root_.abs_of_nonneg] [],
         exact [expr zero_le_two] }
       «expr = »(..., «expr + »(«expr * »(«expr∥ ∥»(«expr • »((2 : exprℝ()), «expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr∥ ∥»(«expr • »((2 : exprℝ()), «expr - »(u, «expr • »(half, «expr + »(wq, wp)))))), «expr * »(«expr∥ ∥»(«expr - »(wp, wq)), «expr∥ ∥»(«expr - »(wp, wq))))) : by simp [] [] [] ["[", expr norm_smul, "]"] [] []
       «expr = »(..., «expr + »(«expr * »(«expr∥ ∥»(«expr + »(a, b)), «expr∥ ∥»(«expr + »(a, b))), «expr * »(«expr∥ ∥»(«expr - »(a, b)), «expr∥ ∥»(«expr - »(a, b))))) : begin
         rw ["[", expr smul_sub, ",", expr smul_smul, ",", expr mul_one_div_cancel (_root_.two_ne_zero : «expr ≠ »((2 : exprℝ()), 0)), ",", "<-", expr one_add_one_eq_two, ",", expr add_smul, "]"] [],
         simp [] [] ["only"] ["[", expr one_smul, "]"] [] [],
         have [ident eq₁] [":", expr «expr = »(«expr - »(wp, wq), «expr - »(a, b))] [],
         from [expr (sub_sub_sub_cancel_left _ _ _).symm],
         have [ident eq₂] [":", expr «expr = »(«expr - »(«expr + »(u, u), «expr + »(wq, wp)), «expr + »(a, b))] [],
         show [expr «expr = »(«expr - »(«expr + »(u, u), «expr + »(wq, wp)), «expr + »(«expr - »(u, wq), «expr - »(u, wp)))],
         abel [] [] [],
         rw ["[", expr eq₁, ",", expr eq₂, "]"] []
       end
       «expr = »(..., «expr * »(2, «expr + »(«expr * »(«expr∥ ∥»(a), «expr∥ ∥»(a)), «expr * »(«expr∥ ∥»(b), «expr∥ ∥»(b))))) : parallelogram_law_with_norm],
    have [ident eq] [":", expr «expr ≤ »(δ, «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp)))))] [],
    { rw [expr smul_add] [],
      apply [expr δ_le'],
      apply [expr h₂],
      repeat { exact [expr subtype.mem _] },
      repeat { exact [expr le_of_lt one_half_pos] },
      exact [expr add_halves 1] },
    have [ident eq₁] [":", expr «expr ≤ »(«expr * »(«expr * »(4, δ), δ), «expr * »(«expr * »(4, «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))))] [],
    { mono [] [] [] [],
      mono [] [] [] [],
      norm_num [] [],
      apply [expr mul_nonneg],
      norm_num [] [],
      exact [expr norm_nonneg _] },
    have [ident eq₂] [":", expr «expr ≤ »(«expr * »(«expr∥ ∥»(a), «expr∥ ∥»(a)), «expr * »(«expr + »(δ, div), «expr + »(δ, div)))] [":=", expr mul_self_le_mul_self (norm_nonneg _) (le_trans «expr $ »(le_of_lt, hw q) (add_le_add_left (nat.one_div_le_one_div hq) _))],
    have [ident eq₂'] [":", expr «expr ≤ »(«expr * »(«expr∥ ∥»(b), «expr∥ ∥»(b)), «expr * »(«expr + »(δ, div), «expr + »(δ, div)))] [":=", expr mul_self_le_mul_self (norm_nonneg _) (le_trans «expr $ »(le_of_lt, hw p) (add_le_add_left (nat.one_div_le_one_div hp) _))],
    rw [expr dist_eq_norm] [],
    apply [expr nonneg_le_nonneg_of_sq_le_sq],
    { exact [expr sqrt_nonneg _] },
    rw [expr mul_self_sqrt] [],
    calc
      «expr = »(«expr * »(«expr∥ ∥»(«expr - »(wp, wq)), «expr∥ ∥»(«expr - »(wp, wq))), «expr - »(«expr * »(2, «expr + »(«expr * »(«expr∥ ∥»(a), «expr∥ ∥»(a)), «expr * »(«expr∥ ∥»(b), «expr∥ ∥»(b)))), «expr * »(«expr * »(4, «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))), «expr∥ ∥»(«expr - »(u, «expr • »(half, «expr + »(wq, wp))))))) : by { rw ["<-", expr this] [],
        simp [] [] [] [] [] [] }
      «expr ≤ »(..., «expr - »(«expr * »(2, «expr + »(«expr * »(«expr∥ ∥»(a), «expr∥ ∥»(a)), «expr * »(«expr∥ ∥»(b), «expr∥ ∥»(b)))), «expr * »(«expr * »(4, δ), δ))) : sub_le_sub_left eq₁ _
      «expr ≤ »(..., «expr - »(«expr * »(2, «expr + »(«expr * »(«expr + »(δ, div), «expr + »(δ, div)), «expr * »(«expr + »(δ, div), «expr + »(δ, div)))), «expr * »(«expr * »(4, δ), δ))) : sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add eq₂ eq₂') (by norm_num [] [])) _
      «expr = »(..., «expr + »(«expr * »(«expr * »(8, δ), div), «expr * »(«expr * »(4, div), div))) : by ring [],
    exact [expr add_nonneg (mul_nonneg (mul_nonneg (by norm_num [] []) zero_le_δ) (le_of_lt nat.one_div_pos_of_nat)) (mul_nonneg (mul_nonneg (by norm_num [] []) nat.one_div_pos_of_nat.le) nat.one_div_pos_of_nat.le)],
    apply [expr tendsto.comp],
    { convert [] [expr continuous_sqrt.continuous_at] [],
      exact [expr sqrt_zero.symm] },
    have [ident eq₁] [":", expr tendsto (λ
      n : exprℕ(), «expr * »(«expr * »(8, δ), «expr / »(1, «expr + »(n, 1)))) at_top (nhds (0 : exprℝ()))] [],
    { convert [] [expr (@tendsto_const_nhds _ _ _ «expr * »(8, δ) _).mul tendsto_one_div_add_at_top_nhds_0_nat] [],
      simp [] [] ["only"] ["[", expr mul_zero, "]"] [] [] },
    have [] [":", expr tendsto (λ
      n : exprℕ(), «expr * »((4 : exprℝ()), «expr / »(1, «expr + »(n, 1)))) at_top (nhds (0 : exprℝ()))] [],
    { convert [] [expr (@tendsto_const_nhds _ _ _ (4 : exprℝ()) _).mul tendsto_one_div_add_at_top_nhds_0_nat] [],
      simp [] [] ["only"] ["[", expr mul_zero, "]"] [] [] },
    have [ident eq₂] [":", expr tendsto (λ
      n : exprℕ(), «expr * »(«expr * »((4 : exprℝ()), «expr / »(1, «expr + »(n, 1))), «expr / »(1, «expr + »(n, 1)))) at_top (nhds (0 : exprℝ()))] [],
    { convert [] [expr this.mul tendsto_one_div_add_at_top_nhds_0_nat] [],
      simp [] [] ["only"] ["[", expr mul_zero, "]"] [] [] },
    convert [] [expr eq₁.add eq₂] [],
    simp [] [] ["only"] ["[", expr add_zero, "]"] [] [] },
  rcases [expr cauchy_seq_tendsto_of_is_complete h₁ (λ
    n, _) seq_is_cauchy, "with", "⟨", ident v, ",", ident hv, ",", ident w_tendsto, "⟩"],
  use [expr v],
  use [expr hv],
  have [ident h_cont] [":", expr continuous (λ
    v, «expr∥ ∥»(«expr - »(u, v)))] [":=", expr continuous.comp continuous_norm (continuous.sub continuous_const continuous_id)],
  have [] [":", expr tendsto (λ n, «expr∥ ∥»(«expr - »(u, w n))) at_top (nhds «expr∥ ∥»(«expr - »(u, v)))] [],
  convert [] [expr tendsto.comp h_cont.continuous_at w_tendsto] [],
  exact [expr tendsto_nhds_unique this norm_tendsto],
  exact [expr subtype.mem _]
end

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_infi_iff_real_inner_le_zero
{K : set F}
(h : convex exprℝ() K)
{u : F}
{v : F}
(hv : «expr ∈ »(v, K)) : «expr ↔ »(«expr = »(«expr∥ ∥»(«expr - »(u, v)), «expr⨅ , »((w : K), «expr∥ ∥»(«expr - »(u, w)))), ∀
 w «expr ∈ » K, «expr ≤ »(«expr⟪ , ⟫_ℝ»(«expr - »(u, v), «expr - »(w, v)), 0)) :=
iff.intro (begin
   assume [binders (eq w hw)],
   let [ident δ] [] [":=", expr «expr⨅ , »((w : K), «expr∥ ∥»(«expr - »(u, w)))],
   let [ident p] [] [":=", expr «expr⟪ , ⟫_ℝ»(«expr - »(u, v), «expr - »(w, v))],
   let [ident q] [] [":=", expr «expr ^ »(«expr∥ ∥»(«expr - »(w, v)), 2)],
   letI [] [":", expr nonempty K] [":=", expr ⟨⟨v, hv⟩⟩],
   have [ident zero_le_δ] [":", expr «expr ≤ »(0, δ)] [],
   apply [expr le_cinfi],
   intro [],
   exact [expr norm_nonneg _],
   have [ident δ_le] [":", expr ∀ w : K, «expr ≤ »(δ, «expr∥ ∥»(«expr - »(u, w)))] [],
   assume [binders (w)],
   apply [expr cinfi_le],
   use [expr (0 : exprℝ())],
   rintros ["_", "⟨", "_", ",", ident rfl, "⟩"],
   exact [expr norm_nonneg _],
   have [ident δ_le'] [":", expr ∀
    w «expr ∈ » K, «expr ≤ »(δ, «expr∥ ∥»(«expr - »(u, w)))] [":=", expr assume w hw, δ_le ⟨w, hw⟩],
   have [] [":", expr ∀
    θ : exprℝ(), «expr < »(0, θ) → «expr ≤ »(θ, 1) → «expr ≤ »(«expr * »(2, p), «expr * »(θ, q))] [],
   assume [binders (θ hθ₁ hθ₂)],
   have [] [":", expr «expr ≤ »(«expr ^ »(«expr∥ ∥»(«expr - »(u, v)), 2), «expr + »(«expr - »(«expr ^ »(«expr∥ ∥»(«expr - »(u, v)), 2), «expr * »(«expr * »(2, θ), «expr⟪ , ⟫_ℝ»(«expr - »(u, v), «expr - »(w, v)))), «expr * »(«expr * »(θ, θ), «expr ^ »(«expr∥ ∥»(«expr - »(w, v)), 2))))] [":=", expr calc
      «expr ≤ »(«expr ^ »(«expr∥ ∥»(«expr - »(u, v)), 2), «expr ^ »(«expr∥ ∥»(«expr - »(u, «expr + »(«expr • »(θ, w), «expr • »(«expr - »(1, θ), v)))), 2)) : begin
        simp [] [] ["only"] ["[", expr sq, "]"] [] [],
        apply [expr mul_self_le_mul_self (norm_nonneg _)],
        rw ["[", expr eq, "]"] [],
        apply [expr δ_le'],
        apply [expr h hw hv],
        exacts ["[", expr le_of_lt hθ₁, ",", expr sub_nonneg.2 hθ₂, ",", expr add_sub_cancel'_right _ _, "]"]
      end
      «expr = »(..., «expr ^ »(«expr∥ ∥»(«expr - »(«expr - »(u, v), «expr • »(θ, «expr - »(w, v)))), 2)) : begin
        have [] [":", expr «expr = »(«expr - »(u, «expr + »(«expr • »(θ, w), «expr • »(«expr - »(1, θ), v))), «expr - »(«expr - »(u, v), «expr • »(θ, «expr - »(w, v))))] [],
        { rw ["[", expr smul_sub, ",", expr sub_smul, ",", expr one_smul, "]"] [],
          simp [] [] ["only"] ["[", expr sub_eq_add_neg, ",", expr add_comm, ",", expr add_left_comm, ",", expr add_assoc, ",", expr neg_add_rev, "]"] [] [] },
        rw [expr this] []
      end
      «expr = »(..., «expr + »(«expr - »(«expr ^ »(«expr∥ ∥»(«expr - »(u, v)), 2), «expr * »(«expr * »(2, θ), inner «expr - »(u, v) «expr - »(w, v))), «expr * »(«expr * »(θ, θ), «expr ^ »(«expr∥ ∥»(«expr - »(w, v)), 2)))) : begin
        rw ["[", expr norm_sub_sq, ",", expr inner_smul_right, ",", expr norm_smul, "]"] [],
        simp [] [] ["only"] ["[", expr sq, "]"] [] [],
        show [expr «expr = »(«expr + »(«expr - »(«expr * »(«expr∥ ∥»(«expr - »(u, v)), «expr∥ ∥»(«expr - »(u, v))), «expr * »(2, «expr * »(θ, inner «expr - »(u, v) «expr - »(w, v)))), «expr * »(«expr * »(exprabsR() θ, «expr∥ ∥»(«expr - »(w, v))), «expr * »(exprabsR() θ, «expr∥ ∥»(«expr - »(w, v))))), «expr + »(«expr - »(«expr * »(«expr∥ ∥»(«expr - »(u, v)), «expr∥ ∥»(«expr - »(u, v))), «expr * »(«expr * »(2, θ), inner «expr - »(u, v) «expr - »(w, v))), «expr * »(«expr * »(θ, θ), «expr * »(«expr∥ ∥»(«expr - »(w, v)), «expr∥ ∥»(«expr - »(w, v))))))],
        rw [expr abs_of_pos hθ₁] [],
        ring []
      end],
   have [ident eq₁] [":", expr «expr = »(«expr + »(«expr - »(«expr ^ »(«expr∥ ∥»(«expr - »(u, v)), 2), «expr * »(«expr * »(2, θ), inner «expr - »(u, v) «expr - »(w, v))), «expr * »(«expr * »(θ, θ), «expr ^ »(«expr∥ ∥»(«expr - »(w, v)), 2))), «expr + »(«expr ^ »(«expr∥ ∥»(«expr - »(u, v)), 2), «expr - »(«expr * »(«expr * »(θ, θ), «expr ^ »(«expr∥ ∥»(«expr - »(w, v)), 2)), «expr * »(«expr * »(2, θ), inner «expr - »(u, v) «expr - »(w, v)))))] [],
   by abel [] [] [],
   rw ["[", expr eq₁, ",", expr le_add_iff_nonneg_right, "]"] ["at", ident this],
   have [ident eq₂] [":", expr «expr = »(«expr - »(«expr * »(«expr * »(θ, θ), «expr ^ »(«expr∥ ∥»(«expr - »(w, v)), 2)), «expr * »(«expr * »(2, θ), inner «expr - »(u, v) «expr - »(w, v))), «expr * »(θ, «expr - »(«expr * »(θ, «expr ^ »(«expr∥ ∥»(«expr - »(w, v)), 2)), «expr * »(2, inner «expr - »(u, v) «expr - »(w, v)))))] [],
   ring [],
   rw [expr eq₂] ["at", ident this],
   have [] [] [":=", expr le_of_sub_nonneg (nonneg_of_mul_nonneg_left this hθ₁)],
   exact [expr this],
   by_cases [expr hq, ":", expr «expr = »(q, 0)],
   { rw [expr hq] ["at", ident this],
     have [] [":", expr «expr ≤ »(p, 0)] [],
     have [] [] [":=", expr this (1 : exprℝ()) (by norm_num [] []) (by norm_num [] [])],
     linarith [] [] [],
     exact [expr this] },
   { have [ident q_pos] [":", expr «expr < »(0, q)] [],
     apply [expr lt_of_le_of_ne],
     exact [expr sq_nonneg _],
     intro [ident h],
     exact [expr hq h.symm],
     by_contradiction [ident hp],
     rw [expr not_le] ["at", ident hp],
     let [ident θ] [] [":=", expr min (1 : exprℝ()) «expr / »(p, q)],
     have [ident eq₁] [":", expr «expr ≤ »(«expr * »(θ, q), p)] [":=", expr calc
        «expr ≤ »(«expr * »(θ, q), «expr * »(«expr / »(p, q), q)) : mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        «expr = »(..., p) : div_mul_cancel _ hq],
     have [] [":", expr «expr ≤ »(«expr * »(2, p), p)] [":=", expr calc
        «expr ≤ »(«expr * »(2, p), «expr * »(θ, q)) : by { refine [expr this θ (lt_min (by norm_num [] []) (div_pos hp q_pos)) (by norm_num [] [])] }
        «expr ≤ »(..., p) : eq₁],
     linarith [] [] [] }
 end) (begin
   assume [binders (h)],
   letI [] [":", expr nonempty K] [":=", expr ⟨⟨v, hv⟩⟩],
   apply [expr le_antisymm],
   { apply [expr le_cinfi],
     assume [binders (w)],
     apply [expr nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)],
     have [] [] [":=", expr h w w.2],
     calc
       «expr ≤ »(«expr * »(«expr∥ ∥»(«expr - »(u, v)), «expr∥ ∥»(«expr - »(u, v))), «expr - »(«expr * »(«expr∥ ∥»(«expr - »(u, v)), «expr∥ ∥»(«expr - »(u, v))), «expr * »(2, inner «expr - »(u, v) «expr - »((w : F), v)))) : by linarith [] [] []
       «expr ≤ »(..., «expr + »(«expr - »(«expr ^ »(«expr∥ ∥»(«expr - »(u, v)), 2), «expr * »(2, inner «expr - »(u, v) «expr - »((w : F), v))), «expr ^ »(«expr∥ ∥»(«expr - »((w : F), v)), 2))) : by { rw [expr sq] [],
         refine [expr le_add_of_nonneg_right _],
         exact [expr sq_nonneg _] }
       «expr = »(..., «expr ^ »(«expr∥ ∥»(«expr - »(«expr - »(u, v), «expr - »(w, v))), 2)) : norm_sub_sq.symm
       «expr = »(..., «expr * »(«expr∥ ∥»(«expr - »(u, w)), «expr∥ ∥»(«expr - »(u, w)))) : by { have [] [":", expr «expr = »(«expr - »(«expr - »(u, v), «expr - »(w, v)), «expr - »(u, w))] [],
         abel [] [] [],
         rw ["[", expr this, ",", expr sq, "]"] [] } },
   { show [expr «expr ≤ »(«expr⨅ , »((w : K), «expr∥ ∥»(«expr - »(u, w))), λ
       w : K, «expr∥ ∥»(«expr - »(u, w)) ⟨v, hv⟩)],
     apply [expr cinfi_le],
     use [expr 0],
     rintros [ident y, "⟨", ident z, ",", ident rfl, "⟩"],
     exact [expr norm_nonneg _] }
 end)

variable (K : Submodule 𝕜 E)

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace
(h : is_complete («expr↑ »(K) : set E)) : ∀
u : E, «expr∃ , »((v «expr ∈ » K), «expr = »(«expr∥ ∥»(«expr - »(u, v)), «expr⨅ , »((w : (K : set E)), «expr∥ ∥»(«expr - »(u, w))))) :=
begin
  letI [] [":", expr inner_product_space exprℝ() E] [":=", expr inner_product_space.is_R_or_C_to_real 𝕜 E],
  letI [] [":", expr module exprℝ() E] [":=", expr restrict_scalars.module exprℝ() 𝕜 E],
  letI [] [":", expr is_scalar_tower exprℝ() 𝕜 E] [":=", expr restrict_scalars.is_scalar_tower _ _ _],
  let [ident K'] [":", expr submodule exprℝ() E] [":=", expr submodule.restrict_scalars exprℝ() K],
  exact [expr exists_norm_eq_infi_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex]
end

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superceded by `norm_eq_infi_iff_inner_eq_zero` that gives the same conclusion over
any `is_R_or_C` field.
-/
theorem norm_eq_infi_iff_real_inner_eq_zero
(K : submodule exprℝ() F)
{u : F}
{v : F}
(hv : «expr ∈ »(v, K)) : «expr ↔ »(«expr = »(«expr∥ ∥»(«expr - »(u, v)), «expr⨅ , »((w : («expr↑ »(K) : set F)), «expr∥ ∥»(«expr - »(u, w)))), ∀
 w «expr ∈ » K, «expr = »(«expr⟪ , ⟫_ℝ»(«expr - »(u, v), w), 0)) :=
iff.intro (begin
   assume [binders (h)],
   have [ident h] [":", expr ∀ w «expr ∈ » K, «expr ≤ »(«expr⟪ , ⟫_ℝ»(«expr - »(u, v), «expr - »(w, v)), 0)] [],
   { rwa ["[", expr norm_eq_infi_iff_real_inner_le_zero, "]"] ["at", ident h],
     exacts ["[", expr K.convex, ",", expr hv, "]"] },
   assume [binders (w hw)],
   have [ident le] [":", expr «expr ≤ »(«expr⟪ , ⟫_ℝ»(«expr - »(u, v), w), 0)] [],
   let [ident w'] [] [":=", expr «expr + »(w, v)],
   have [] [":", expr «expr ∈ »(w', K)] [":=", expr submodule.add_mem _ hw hv],
   have [ident h₁] [] [":=", expr h w' this],
   have [ident h₂] [":", expr «expr = »(«expr - »(w', v), w)] [],
   simp [] [] ["only"] ["[", expr add_neg_cancel_right, ",", expr sub_eq_add_neg, "]"] [] [],
   rw [expr h₂] ["at", ident h₁],
   exact [expr h₁],
   have [ident ge] [":", expr «expr ≥ »(«expr⟪ , ⟫_ℝ»(«expr - »(u, v), w), 0)] [],
   let [ident w''] [] [":=", expr «expr + »(«expr- »(w), v)],
   have [] [":", expr «expr ∈ »(w'', K)] [":=", expr submodule.add_mem _ (submodule.neg_mem _ hw) hv],
   have [ident h₁] [] [":=", expr h w'' this],
   have [ident h₂] [":", expr «expr = »(«expr - »(w'', v), «expr- »(w))] [],
   simp [] [] ["only"] ["[", expr neg_inj, ",", expr add_neg_cancel_right, ",", expr sub_eq_add_neg, "]"] [] [],
   rw ["[", expr h₂, ",", expr inner_neg_right, "]"] ["at", ident h₁],
   linarith [] [] [],
   exact [expr le_antisymm le ge]
 end) (begin
   assume [binders (h)],
   have [] [":", expr ∀ w «expr ∈ » K, «expr ≤ »(«expr⟪ , ⟫_ℝ»(«expr - »(u, v), «expr - »(w, v)), 0)] [],
   assume [binders (w hw)],
   let [ident w'] [] [":=", expr «expr - »(w, v)],
   have [] [":", expr «expr ∈ »(w', K)] [":=", expr submodule.sub_mem _ hw hv],
   have [ident h₁] [] [":=", expr h w' this],
   exact [expr le_of_eq h₁],
   rwa [expr norm_eq_infi_iff_real_inner_le_zero] [],
   exacts ["[", expr submodule.convex _, ",", expr hv, "]"]
 end)

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero
{u : E}
{v : E}
(hv : «expr ∈ »(v, K)) : «expr ↔ »(«expr = »(«expr∥ ∥»(«expr - »(u, v)), «expr⨅ , »((w : («expr↑ »(K) : set E)), «expr∥ ∥»(«expr - »(u, w)))), ∀
 w «expr ∈ » K, «expr = »(«expr⟪ , ⟫»(«expr - »(u, v), w), 0)) :=
begin
  letI [] [":", expr inner_product_space exprℝ() E] [":=", expr inner_product_space.is_R_or_C_to_real 𝕜 E],
  letI [] [":", expr module exprℝ() E] [":=", expr restrict_scalars.module exprℝ() 𝕜 E],
  letI [] [":", expr is_scalar_tower exprℝ() 𝕜 E] [":=", expr restrict_scalars.is_scalar_tower _ _ _],
  let [ident K'] [":", expr submodule exprℝ() E] [":=", expr K.restrict_scalars exprℝ()],
  split,
  { assume [binders (H)],
    have [ident A] [":", expr ∀
     w «expr ∈ » K, «expr = »(re «expr⟪ , ⟫»(«expr - »(u, v), w), 0)] [":=", expr (norm_eq_infi_iff_real_inner_eq_zero K' hv).1 H],
    assume [binders (w hw)],
    apply [expr ext],
    { simp [] [] [] ["[", expr A w hw, "]"] [] [] },
    { symmetry,
      calc
        «expr = »(im (0 : 𝕜), 0) : im.map_zero
        «expr = »(..., re «expr⟪ , ⟫»(«expr - »(u, v), «expr • »(«expr- »(I), w))) : (A _ (K.smul_mem «expr- »(I) hw)).symm
        «expr = »(..., re «expr * »(«expr- »(I), «expr⟪ , ⟫»(«expr - »(u, v), w))) : by rw [expr inner_smul_right] []
        «expr = »(..., im «expr⟪ , ⟫»(«expr - »(u, v), w)) : by simp [] [] [] [] [] [] } },
  { assume [binders (H)],
    have [] [":", expr ∀ w «expr ∈ » K', «expr = »(«expr⟪ , ⟫_ℝ»(«expr - »(u, v), w), 0)] [],
    { assume [binders (w hw)],
      rw ["[", expr real_inner_eq_re_inner, ",", expr H w hw, "]"] [],
      exact [expr zero_re'] },
    exact [expr (norm_eq_infi_iff_real_inner_eq_zero K' hv).2 this] }
end

section orthogonalProjection

variable [CompleteSpace K]

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonal_projection` and should not
be used once that is defined. -/
def orthogonalProjectionFn (v : E) :=
  (exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some

variable {K}

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem (v : E) : orthogonalProjectionFn K v ∈ K :=
  (exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonal_projection_fn_inner_eq_zero (v : E) : ∀ w _ : w ∈ K, ⟪v - orthogonalProjectionFn K v, w⟫ = 0 :=
  by 
    rw [←norm_eq_infi_iff_inner_eq_zero K (orthogonal_projection_fn_mem v)]
    exact (exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some_spec

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
theorem eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
{u v : E}
(hvm : «expr ∈ »(v, K))
(hvo : ∀ w «expr ∈ » K, «expr = »(«expr⟪ , ⟫»(«expr - »(u, v), w), 0)) : «expr = »(orthogonal_projection_fn K u, v) :=
begin
  rw ["[", "<-", expr sub_eq_zero, ",", "<-", expr inner_self_eq_zero, "]"] [],
  have [ident hvs] [":", expr «expr ∈ »(«expr - »(orthogonal_projection_fn K u, v), K)] [":=", expr submodule.sub_mem K (orthogonal_projection_fn_mem u) hvm],
  have [ident huo] [":", expr «expr = »(«expr⟪ , ⟫»(«expr - »(u, orthogonal_projection_fn K u), «expr - »(orthogonal_projection_fn K u, v)), 0)] [":=", expr orthogonal_projection_fn_inner_eq_zero u _ hvs],
  have [ident huv] [":", expr «expr = »(«expr⟪ , ⟫»(«expr - »(u, v), «expr - »(orthogonal_projection_fn K u, v)), 0)] [":=", expr hvo _ hvs],
  have [ident houv] [":", expr «expr = »(«expr⟪ , ⟫»(«expr - »(«expr - »(u, v), «expr - »(u, orthogonal_projection_fn K u)), «expr - »(orthogonal_projection_fn K u, v)), 0)] [],
  { rw ["[", expr inner_sub_left, ",", expr huo, ",", expr huv, ",", expr sub_zero, "]"] [] },
  rwa [expr sub_sub_sub_cancel_left] ["at", ident houv]
end

variable (K)

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem orthogonal_projection_fn_norm_sq
(v : E) : «expr = »(«expr * »(«expr∥ ∥»(v), «expr∥ ∥»(v)), «expr + »(«expr * »(«expr∥ ∥»(«expr - »(v, orthogonal_projection_fn K v)), «expr∥ ∥»(«expr - »(v, orthogonal_projection_fn K v))), «expr * »(«expr∥ ∥»(orthogonal_projection_fn K v), «expr∥ ∥»(orthogonal_projection_fn K v)))) :=
begin
  set [] [ident p] [] [":="] [expr orthogonal_projection_fn K v] [],
  have [ident h'] [":", expr «expr = »(«expr⟪ , ⟫»(«expr - »(v, p), p), 0)] [],
  { exact [expr orthogonal_projection_fn_inner_eq_zero _ _ (orthogonal_projection_fn_mem v)] },
  convert [] [expr norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero «expr - »(v, p) p h'] ["using", 2]; simp [] [] [] [] [] []
end

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The orthogonal projection onto a complete subspace. -/ def orthogonal_projection : «expr →L[ ] »(E, 𝕜, K) :=
linear_map.mk_continuous { to_fun := λ v, ⟨orthogonal_projection_fn K v, orthogonal_projection_fn_mem v⟩,
  map_add' := λ x y, begin
    have [ident hm] [":", expr «expr ∈ »(«expr + »(orthogonal_projection_fn K x, orthogonal_projection_fn K y), K)] [":=", expr submodule.add_mem K (orthogonal_projection_fn_mem x) (orthogonal_projection_fn_mem y)],
    have [ident ho] [":", expr ∀
     w «expr ∈ » K, «expr = »(«expr⟪ , ⟫»(«expr - »(«expr + »(x, y), «expr + »(orthogonal_projection_fn K x, orthogonal_projection_fn K y)), w), 0)] [],
    { intros [ident w, ident hw],
      rw ["[", expr add_sub_comm, ",", expr inner_add_left, ",", expr orthogonal_projection_fn_inner_eq_zero _ w hw, ",", expr orthogonal_projection_fn_inner_eq_zero _ w hw, ",", expr add_zero, "]"] [] },
    ext [] [] [],
    simp [] [] [] ["[", expr eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho, "]"] [] []
  end,
  map_smul' := λ c x, begin
    have [ident hm] [":", expr «expr ∈ »(«expr • »(c, orthogonal_projection_fn K x), K)] [":=", expr submodule.smul_mem K _ (orthogonal_projection_fn_mem x)],
    have [ident ho] [":", expr ∀
     w «expr ∈ » K, «expr = »(«expr⟪ , ⟫»(«expr - »(«expr • »(c, x), «expr • »(c, orthogonal_projection_fn K x)), w), 0)] [],
    { intros [ident w, ident hw],
      rw ["[", "<-", expr smul_sub, ",", expr inner_smul_left, ",", expr orthogonal_projection_fn_inner_eq_zero _ w hw, ",", expr mul_zero, "]"] [] },
    ext [] [] [],
    simp [] [] [] ["[", expr eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho, "]"] [] []
  end } 1 (λ x, begin
   simp [] [] ["only"] ["[", expr one_mul, ",", expr linear_map.coe_mk, "]"] [] [],
   refine [expr le_of_pow_le_pow 2 (norm_nonneg _) (by norm_num [] []) _],
   change [expr «expr ≤ »(«expr ^ »(«expr∥ ∥»(orthogonal_projection_fn K x), 2), «expr ^ »(«expr∥ ∥»(x), 2))] [] [],
   nlinarith [] [] ["[", expr orthogonal_projection_fn_norm_sq K x, "]"]
 end)

variable {K}

@[simp]
theorem orthogonal_projection_fn_eq (v : E) : orthogonalProjectionFn K v = (orthogonalProjection K v : E) :=
  rfl

/-- The characterization of the orthogonal projection.  -/
@[simp]
theorem orthogonal_projection_inner_eq_zero (v : E) : ∀ w _ : w ∈ K, ⟪v - orthogonalProjection K v, w⟫ = 0 :=
  orthogonal_projection_fn_inner_eq_zero v

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`.  -/
@[simp]
theorem sub_orthogonal_projection_mem_orthogonal (v : E) : v - orthogonalProjection K v ∈ Kᗮ :=
  by 
    intro w hw 
    rw [inner_eq_zero_sym]
    exact orthogonal_projection_inner_eq_zero _ _ hw

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
theorem eq_orthogonal_projection_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K) (hvo : ∀ w _ : w ∈ K, ⟪u - v, w⟫ = 0) :
  (orthogonalProjection K u : E) = v :=
  eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hvm hvo

/-- The orthogonal projections onto equal subspaces are coerced back to the same point in `E`. -/
theorem eq_orthogonal_projection_of_eq_submodule {K' : Submodule 𝕜 E} [CompleteSpace K'] (h : K = K') (u : E) :
  (orthogonalProjection K u : E) = (orthogonalProjection K' u : E) :=
  by 
    change orthogonalProjectionFn K u = orthogonalProjectionFn K' u 
    congr 
    exact h

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp]
theorem orthogonal_projection_mem_subspace_eq_self (v : K) : orthogonalProjection K v = v :=
  by 
    ext 
    apply eq_orthogonal_projection_of_mem_of_inner_eq_zero <;> simp 

/-- A point equals its orthogonal projection if and only if it lies in the subspace. -/
theorem orthogonal_projection_eq_self_iff {v : E} : (orthogonalProjection K v : E) = v ↔ v ∈ K :=
  by 
    refine' ⟨fun h => _, fun h => eq_orthogonal_projection_of_mem_of_inner_eq_zero h _⟩
    ·
      rw [←h]
      simp 
    ·
      simp 

/-- Orthogonal projection onto the `submodule.map` of a subspace. -/
theorem orthogonal_projection_map_apply {E E' : Type _} [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E']
  (f : E ≃ₗᵢ[𝕜] E') (p : Submodule 𝕜 E) [FiniteDimensional 𝕜 p] (x : E') :
  (orthogonalProjection (p.map (f.to_linear_equiv : E →ₗ[𝕜] E')) x : E') = f (orthogonalProjection p (f.symm x)) :=
  by 
    apply eq_orthogonal_projection_of_mem_of_inner_eq_zero
    ·
      exact
        ⟨orthogonalProjection p (f.symm x), Submodule.coe_mem _,
          by 
            simp ⟩
    rintro w ⟨a, ha, rfl⟩
    suffices  : inner (f (f.symm x - orthogonalProjection p (f.symm x))) (f a) = (0 : 𝕜)
    ·
      simpa using this 
    rw [f.inner_map_map]
    exact orthogonal_projection_inner_eq_zero _ _ ha

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp]
theorem orthogonal_projection_bot : orthogonalProjection (⊥ : Submodule 𝕜 E) = 0 :=
  by 
    ext

variable (K)

/-- The orthogonal projection has norm `≤ 1`. -/
theorem orthogonal_projection_norm_le : ∥orthogonalProjection K∥ ≤ 1 :=
  LinearMap.mk_continuous_norm_le _
    (by 
      normNum)
    _

variable (𝕜)

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem smul_orthogonal_projection_singleton
{v : E}
(w : E) : «expr = »(«expr • »((«expr ^ »(«expr∥ ∥»(v), 2) : 𝕜), (orthogonal_projection «expr ∙ »(𝕜, v) w : E)), «expr • »(«expr⟪ , ⟫»(v, w), v)) :=
begin
  suffices [] [":", expr «expr = »(«expr↑ »(orthogonal_projection «expr ∙ »(𝕜, v) «expr • »((«expr ^ »(«expr∥ ∥»(v), 2) : 𝕜), w)), «expr • »(«expr⟪ , ⟫»(v, w), v))],
  { simpa [] [] [] [] [] ["using", expr this] },
  apply [expr eq_orthogonal_projection_of_mem_of_inner_eq_zero],
  { rw [expr submodule.mem_span_singleton] [],
    use [expr «expr⟪ , ⟫»(v, w)] },
  { intros [ident x, ident hx],
    obtain ["⟨", ident c, ",", ident rfl, "⟩", ":=", expr submodule.mem_span_singleton.mp hx],
    have [ident hv] [":", expr «expr = »(«expr ^ »(«expr↑ »(«expr∥ ∥»(v)), 2), «expr⟪ , ⟫»(v, v))] [":=", expr by { norm_cast [],
       simp [] [] [] ["[", expr norm_sq_eq_inner, "]"] [] [] }],
    simp [] [] [] ["[", expr inner_sub_left, ",", expr inner_smul_left, ",", expr inner_smul_right, ",", expr ring_equiv.map_div, ",", expr mul_comm, ",", expr hv, ",", expr inner_product_space.conj_sym, ",", expr hv, "]"] [] [] }
end

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Formula for orthogonal projection onto a single vector. -/
theorem orthogonal_projection_singleton
{v : E}
(w : E) : «expr = »((orthogonal_projection «expr ∙ »(𝕜, v) w : E), «expr • »(«expr / »(«expr⟪ , ⟫»(v, w), «expr ^ »(«expr∥ ∥»(v), 2)), v)) :=
begin
  by_cases [expr hv, ":", expr «expr = »(v, 0)],
  { rw ["[", expr hv, ",", expr eq_orthogonal_projection_of_eq_submodule submodule.span_zero_singleton, "]"] [],
    { simp [] [] [] [] [] [] },
    { apply_instance } },
  have [ident hv'] [":", expr «expr ≠ »(«expr∥ ∥»(v), 0)] [":=", expr ne_of_gt (norm_pos_iff.mpr hv)],
  have [ident key] [":", expr «expr = »(«expr • »(«expr * »(«expr ⁻¹»((«expr ^ »(«expr∥ ∥»(v), 2) : 𝕜)), «expr ^ »(«expr∥ ∥»(v), 2)), «expr↑ »(orthogonal_projection «expr ∙ »(𝕜, v) w)), «expr • »(«expr * »(«expr ⁻¹»((«expr ^ »(«expr∥ ∥»(v), 2) : 𝕜)), «expr⟪ , ⟫»(v, w)), v))] [],
  { simp [] [] [] ["[", expr mul_smul, ",", expr smul_orthogonal_projection_singleton 𝕜 w, "]"] [] [] },
  convert [] [expr key] []; field_simp [] ["[", expr hv', "]"] [] []
end

/-- Formula for orthogonal projection onto a single unit vector. -/
theorem orthogonal_projection_unit_singleton {v : E} (hv : ∥v∥ = 1) (w : E) :
  (orthogonalProjection (𝕜∙v) w : E) = ⟪v, w⟫ • v :=
  by 
    rw [←smul_orthogonal_projection_singleton 𝕜 w]
    simp [hv]

end orthogonalProjection

section reflection

variable {𝕜} (K) [CompleteSpace K]

/-- Auxiliary definition for `reflection`: the reflection as a linear equivalence. -/
def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive (bit0 (K.subtype.comp (orthogonalProjection K).toLinearMap) - LinearMap.id)
    fun x =>
      by 
        simp [bit0]

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Reflection in a complete subspace of an inner product space.  The word "reflection" is
sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The definition here, of
reflection in a subspace, is a more general sense of the word that includes both those common
cases. -/ def reflection : «expr ≃ₗᵢ[ ] »(E, 𝕜, E) :=
{ norm_map' := begin
    intros [ident x],
    let [ident w] [":", expr K] [":=", expr orthogonal_projection K x],
    let [ident v] [] [":=", expr «expr - »(x, w)],
    have [] [":", expr «expr = »(«expr⟪ , ⟫»(v, w), 0)] [":=", expr orthogonal_projection_inner_eq_zero x w w.2],
    convert [] [expr norm_sub_eq_norm_add this] ["using", 2],
    { rw ["[", expr linear_equiv.coe_mk, ",", expr reflection_linear_equiv, ",", expr linear_equiv.to_fun_eq_coe, ",", expr linear_equiv.coe_of_involutive, ",", expr linear_map.sub_apply, ",", expr linear_map.id_apply, ",", expr bit0, ",", expr linear_map.add_apply, ",", expr linear_map.comp_apply, ",", expr submodule.subtype_apply, ",", expr continuous_linear_map.to_linear_map_eq_coe, ",", expr continuous_linear_map.coe_coe, "]"] [],
      dsimp [] ["[", expr w, ",", expr v, "]"] [] [],
      abel [] [] [] },
    { simp [] [] ["only"] ["[", expr add_sub_cancel'_right, ",", expr eq_self_iff_true, "]"] [] [] }
  end,
  ..reflection_linear_equiv K }

variable {K}

/-- The result of reflecting. -/
theorem reflection_apply (p : E) : reflection K p = bit0 («expr↑ » (orthogonalProjection K p)) - p :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm : (reflection K).symm = reflection K :=
  rfl

variable (K)

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (p : E) : reflection K (reflection K p) = p :=
  (reflection K).left_inv p

/-- Reflection is involutive. -/
theorem reflection_involutive : Function.Involutive (reflection K) :=
  reflection_reflection K

/-- Reflection is involutive. -/
@[simp]
theorem reflection_trans_reflection : (reflection K).trans (reflection K) = LinearIsometryEquiv.refl 𝕜 E :=
  LinearIsometryEquiv.ext$ reflection_involutive K

variable {K}

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff (x : E) : reflection K x = x ↔ x ∈ K :=
  by 
    rw [←orthogonal_projection_eq_self_iff, reflection_apply, sub_eq_iff_eq_add', ←two_smul 𝕜, ←two_smul' 𝕜]
    refine' (smul_right_injective E _).eq_iff 
    exact two_ne_zero

theorem reflection_mem_subspace_eq_self {x : E} (hx : x ∈ K) : reflection K x = x :=
  (reflection_eq_self_iff x).mpr hx

/-- Reflection in the `submodule.map` of a subspace. -/
theorem reflection_map_apply {E E' : Type _} [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
  (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] (x : E') :
  reflection (K.map (f.to_linear_equiv : E →ₗ[𝕜] E')) x = f (reflection K (f.symm x)) :=
  by 
    simp [bit0, reflection_apply, orthogonal_projection_map_apply f K x]

/-- Reflection in the `submodule.map` of a subspace. -/
theorem reflection_map {E E' : Type _} [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
  (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] :
  reflection (K.map (f.to_linear_equiv : E →ₗ[𝕜] E')) = f.symm.trans ((reflection K).trans f) :=
  LinearIsometryEquiv.ext$ reflection_map_apply f K

/-- Reflection through the trivial subspace {0} is just negation. -/
@[simp]
theorem reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜 :=
  by 
    ext <;> simp [reflection_apply]

end reflection

section Orthogonal

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
theorem submodule.sup_orthogonal_inf_of_complete_space
{K₁ K₂ : submodule 𝕜 E}
(h : «expr ≤ »(K₁, K₂))
[complete_space K₁] : «expr = »(«expr ⊔ »(K₁, «expr ⊓ »(«expr ᗮ»(K₁), K₂)), K₂) :=
begin
  ext [] [ident x] [],
  rw [expr submodule.mem_sup] [],
  let [ident v] [":", expr K₁] [":=", expr orthogonal_projection K₁ x],
  have [ident hvm] [":", expr «expr ∈ »(«expr - »(x, v), «expr ᗮ»(K₁))] [":=", expr sub_orthogonal_projection_mem_orthogonal x],
  split,
  { rintro ["⟨", ident y, ",", ident hy, ",", ident z, ",", ident hz, ",", ident rfl, "⟩"],
    exact [expr K₂.add_mem (h hy) hz.2] },
  { exact [expr λ hx, ⟨v, v.prop, «expr - »(x, v), ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel'_right _ _⟩] }
end

variable {K}

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
theorem Submodule.sup_orthogonal_of_complete_space [CompleteSpace K] : K⊔Kᗮ = ⊤ :=
  by 
    convert Submodule.sup_orthogonal_inf_of_complete_space (le_top : K ≤ ⊤)
    simp 

variable (K)

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
theorem submodule.exists_sum_mem_mem_orthogonal
[complete_space K]
(v : E) : «expr∃ , »((y «expr ∈ » K) (z «expr ∈ » «expr ᗮ»(K)), «expr = »(v, «expr + »(y, z))) :=
begin
  have [ident h_mem] [":", expr «expr ∈ »(v, «expr ⊔ »(K, «expr ᗮ»(K)))] [":=", expr by simp [] [] [] ["[", expr submodule.sup_orthogonal_of_complete_space, "]"] [] []],
  obtain ["⟨", ident y, ",", ident hy, ",", ident z, ",", ident hz, ",", ident hyz, "⟩", ":=", expr submodule.mem_sup.mp h_mem],
  exact [expr ⟨y, hy, z, hz, hyz.symm⟩]
end

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `K` is complete, then the orthogonal complement of its orthogonal complement is itself. -/
@[simp]
theorem submodule.orthogonal_orthogonal [complete_space K] : «expr = »(«expr ᗮ»(«expr ᗮ»(K)), K) :=
begin
  ext [] [ident v] [],
  split,
  { obtain ["⟨", ident y, ",", ident hy, ",", ident z, ",", ident hz, ",", ident rfl, "⟩", ":=", expr K.exists_sum_mem_mem_orthogonal v],
    intros [ident hv],
    have [ident hz'] [":", expr «expr = »(z, 0)] [],
    { have [ident hyz] [":", expr «expr = »(«expr⟪ , ⟫»(z, y), 0)] [":=", expr by simp [] [] [] ["[", expr hz y hy, ",", expr inner_eq_zero_sym, "]"] [] []],
      simpa [] [] [] ["[", expr inner_add_right, ",", expr hyz, "]"] [] ["using", expr hv z hz] },
    simp [] [] [] ["[", expr hy, ",", expr hz', "]"] [] [] },
  { intros [ident hv, ident w, ident hw],
    rw [expr inner_eq_zero_sym] [],
    exact [expr hw v hv] }
end

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem submodule.orthogonal_orthogonal_eq_closure
[complete_space E] : «expr = »(«expr ᗮ»(«expr ᗮ»(K)), K.topological_closure) :=
begin
  refine [expr le_antisymm _ _],
  { convert [] [expr submodule.orthogonal_orthogonal_monotone K.submodule_topological_closure] [],
    haveI [] [":", expr complete_space K.topological_closure] [":=", expr K.is_closed_topological_closure.complete_space_coe],
    rw [expr K.topological_closure.orthogonal_orthogonal] [] },
  { exact [expr K.topological_closure_minimal K.le_orthogonal_orthogonal «expr ᗮ»(K).is_closed_orthogonal] }
end

variable {K}

/-- If `K` is complete, `K` and `Kᗮ` are complements of each other. -/
theorem Submodule.is_compl_orthogonal_of_complete_space [CompleteSpace K] : IsCompl K Kᗮ :=
  ⟨K.orthogonal_disjoint, le_of_eqₓ Submodule.sup_orthogonal_of_complete_space.symm⟩

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem submodule.orthogonal_eq_bot_iff
[complete_space (K : set E)] : «expr ↔ »(«expr = »(«expr ᗮ»(K), «expr⊥»()), «expr = »(K, «expr⊤»())) :=
begin
  refine [expr ⟨_, λ h, by rw ["[", expr h, ",", expr submodule.top_orthogonal_eq_bot, "]"] []⟩],
  intro [ident h],
  have [] [":", expr «expr = »(«expr ⊔ »(K, «expr ᗮ»(K)), «expr⊤»())] [":=", expr submodule.sup_orthogonal_of_complete_space],
  rwa ["[", expr h, ",", expr sup_comm, ",", expr bot_sup_eq, "]"] ["at", ident this]
end

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonal_projection_of_mem_orthogonal [CompleteSpace K] {u v : E} (hv : v ∈ K) (hvo : u - v ∈ Kᗮ) :
  (orthogonalProjection K u : E) = v :=
  eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hv fun w => inner_eq_zero_sym.mp ∘ hvo w

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonal_projection_of_mem_orthogonal' [CompleteSpace K] {u v z : E} (hv : v ∈ K) (hz : z ∈ Kᗮ)
  (hu : u = v+z) : (orthogonalProjection K u : E) = v :=
  eq_orthogonal_projection_of_mem_orthogonal hv
    (by 
      simpa [hu])

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
theorem orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero [CompleteSpace K] {v : E} (hv : v ∈ Kᗮ) :
  orthogonalProjection K v = 0 :=
  by 
    ext 
    convert eq_orthogonal_projection_of_mem_orthogonal _ _ <;> simp [hv]

/-- The reflection in `K` of an element of `Kᗮ` is its negation. -/
theorem reflection_mem_subspace_orthogonal_complement_eq_neg [CompleteSpace K] {v : E} (hv : v ∈ Kᗮ) :
  reflection K v = -v :=
  by 
    simp [reflection_apply, orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv]

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
theorem orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero [CompleteSpace E] {v : E} (hv : v ∈ K) :
  orthogonalProjection Kᗮ v = 0 :=
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero (K.le_orthogonal_orthogonal hv)

/-- The reflection in `Kᗮ` of an element of `K` is its negation. -/
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg [CompleteSpace E] {v : E} (hv : v ∈ K) :
  reflection Kᗮ v = -v :=
  reflection_mem_subspace_orthogonal_complement_eq_neg (K.le_orthogonal_orthogonal hv)

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
theorem orthogonal_projection_orthogonal_complement_singleton_eq_zero [CompleteSpace E] (v : E) :
  orthogonalProjection (𝕜∙v)ᗮ v = 0 :=
  orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero (Submodule.mem_span_singleton_self v)

/-- The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`. -/
theorem reflection_orthogonal_complement_singleton_eq_neg [CompleteSpace E] (v : E) : reflection (𝕜∙v)ᗮ v = -v :=
  reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem reflection_sub
[complete_space F]
{v w : F}
(h : «expr = »(«expr∥ ∥»(v), «expr∥ ∥»(w))) : «expr = »(reflection «expr ᗮ»(«expr ∙ »(exprℝ(), «expr - »(v, w))) v, w) :=
begin
  set [] [ident R] [":", expr «expr ≃ₗᵢ[ ] »(F, exprℝ(), F)] [":="] [expr reflection «expr ᗮ»(«expr ∙ »(exprℝ(), «expr - »(v, w)))] [],
  suffices [] [":", expr «expr = »(«expr + »(R v, R v), «expr + »(w, w))],
  { apply [expr smul_right_injective F (by norm_num [] [] : «expr ≠ »((2 : exprℝ()), 0))],
    simpa [] [] [] ["[", expr two_smul, "]"] [] ["using", expr this] },
  have [ident h₁] [":", expr «expr = »(R «expr - »(v, w), «expr- »(«expr - »(v, w)))] [":=", expr reflection_orthogonal_complement_singleton_eq_neg «expr - »(v, w)],
  have [ident h₂] [":", expr «expr = »(R «expr + »(v, w), «expr + »(v, w))] [],
  { apply [expr reflection_mem_subspace_eq_self],
    apply [expr mem_orthogonal_singleton_of_inner_left],
    rw [expr real_inner_add_sub_eq_zero_iff] [],
    exact [expr h] },
  convert [] [expr congr_arg2 ((«expr + »)) h₂ h₁] ["using", 1],
  { simp [] [] [] [] [] [] },
  { abel [] [] [] }
end

variable (K)

/-- In a complete space `E`, a vector splits as the sum of its orthogonal projections onto a
complete submodule `K` and onto the orthogonal complement of `K`.-/
theorem eq_sum_orthogonal_projection_self_orthogonal_complement [CompleteSpace E] [CompleteSpace K] (w : E) :
  w = (orthogonalProjection K w : E)+(orthogonalProjection Kᗮ w : E) :=
  by 
    obtain ⟨y, hy, z, hz, hwyz⟩ := K.exists_sum_mem_mem_orthogonal w 
    convert hwyz
    ·
      exact eq_orthogonal_projection_of_mem_orthogonal' hy hz hwyz
    ·
      rw [add_commₓ] at hwyz 
      refine' eq_orthogonal_projection_of_mem_orthogonal' hz _ hwyz 
      simp [hy]

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
theorem id_eq_sum_orthogonal_projection_self_orthogonal_complement [CompleteSpace E] [CompleteSpace K] :
  ContinuousLinearMap.id 𝕜 E = K.subtypeL.comp (orthogonalProjection K)+Kᗮ.subtypeL.comp (orthogonalProjection Kᗮ) :=
  by 
    ext w 
    exact eq_sum_orthogonal_projection_self_orthogonal_complement K w

/-- The orthogonal projection is self-adjoint. -/
theorem inner_orthogonal_projection_left_eq_right [CompleteSpace E] [CompleteSpace K] (u v : E) :
  ⟪«expr↑ » (orthogonalProjection K u), v⟫ = ⟪u, orthogonalProjection K v⟫ :=
  by 
    nthRw 0[eq_sum_orthogonal_projection_self_orthogonal_complement K v]
    nthRw 1[eq_sum_orthogonal_projection_self_orthogonal_complement K u]
    rw [inner_add_left, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal (Submodule.coe_mem (orthogonalProjection K u))
        (Submodule.coe_mem (orthogonalProjection Kᗮ v)),
      Submodule.inner_left_of_mem_orthogonal (Submodule.coe_mem (orthogonalProjection K v))
        (Submodule.coe_mem (orthogonalProjection Kᗮ u))]

open FiniteDimensional

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem submodule.finrank_add_inf_finrank_orthogonal
{K₁ K₂ : submodule 𝕜 E}
[finite_dimensional 𝕜 K₂]
(h : «expr ≤ »(K₁, K₂)) : «expr = »(«expr + »(finrank 𝕜 K₁, finrank 𝕜 («expr ⊓ »(«expr ᗮ»(K₁), K₂) : submodule 𝕜 E)), finrank 𝕜 K₂) :=
begin
  haveI [] [] [":=", expr submodule.finite_dimensional_of_le h],
  have [ident hd] [] [":=", expr submodule.dim_sup_add_dim_inf_eq K₁ «expr ⊓ »(«expr ᗮ»(K₁), K₂)],
  rw ["[", "<-", expr inf_assoc, ",", expr (submodule.orthogonal_disjoint K₁).eq_bot, ",", expr bot_inf_eq, ",", expr finrank_bot, ",", expr submodule.sup_orthogonal_inf_of_complete_space h, "]"] ["at", ident hd],
  rw [expr add_zero] ["at", ident hd],
  exact [expr hd.symm]
end

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem Submodule.finrank_add_inf_finrank_orthogonal' {K₁ K₂ : Submodule 𝕜 E} [FiniteDimensional 𝕜 K₂] (h : K₁ ≤ K₂)
  {n : ℕ} (h_dim : (finrank 𝕜 K₁+n) = finrank 𝕜 K₂) : finrank 𝕜 (K₁ᗮ⊓K₂ : Submodule 𝕜 E) = n :=
  by 
    rw [←add_right_injₓ (finrank 𝕜 K₁)]
    simp [Submodule.finrank_add_inf_finrank_orthogonal h, h_dim]

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem Submodule.finrank_add_finrank_orthogonal [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) :
  (finrank 𝕜 K+finrank 𝕜 Kᗮ) = finrank 𝕜 E :=
  by 
    convert Submodule.finrank_add_inf_finrank_orthogonal (le_top : K ≤ ⊤) using 1
    ·
      rw [inf_top_eq]
    ·
      simp 

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem Submodule.finrank_add_finrank_orthogonal' [FiniteDimensional 𝕜 E] {K : Submodule 𝕜 E} {n : ℕ}
  (h_dim : (finrank 𝕜 K+n) = finrank 𝕜 E) : finrank 𝕜 Kᗮ = n :=
  by 
    rw [←add_right_injₓ (finrank 𝕜 K)]
    simp [Submodule.finrank_add_finrank_orthogonal, h_dim]

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

/-- In a finite-dimensional inner product space, the dimension of the orthogonal complement of the
span of a nonzero vector is one less than the dimension of the space. -/
theorem finrank_orthogonal_span_singleton {n : ℕ} [_i : Fact (finrank 𝕜 E = n+1)] {v : E} (hv : v ≠ 0) :
  finrank 𝕜 (𝕜∙v)ᗮ = n :=
  Submodule.finrank_add_finrank_orthogonal'$
    by 
      simp [finrank_span_singleton hv, _i.elim, add_commₓ]

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An element `φ` of the orthogonal group of `F` can be factored as a product of reflections, and
specifically at most as many reflections as the dimension of the complement of the fixed subspace
of `φ`. -/
theorem linear_isometry_equiv.reflections_generate_dim_aux
[finite_dimensional exprℝ() F]
{n : exprℕ()}
(φ : «expr ≃ₗᵢ[ ] »(F, exprℝ(), F))
(hn : «expr ≤ »(finrank exprℝ() «expr ᗮ»(«expr - »(continuous_linear_map.id exprℝ() F, φ.to_continuous_linear_equiv).ker), n)) : «expr∃ , »((l : list F), «expr ∧ »(«expr ≤ »(l.length, n), «expr = »(φ, (l.map (λ
     v, reflection «expr ᗮ»(«expr ∙ »(exprℝ(), v)))).prod))) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident φ],
  { refine [expr ⟨«expr[ , ]»([]), rfl.le, _⟩],
    have [] [":", expr «expr = »(«expr - »(continuous_linear_map.id exprℝ() F, φ.to_continuous_linear_equiv).ker, «expr⊤»())] [],
    { rwa ["[", expr nat.le_zero_iff, ",", expr finrank_eq_zero, ",", expr submodule.orthogonal_eq_bot_iff, "]"] ["at", ident hn] },
    symmetry,
    ext [] [ident x] [],
    simpa [] [] [] ["[", expr sub_eq_zero, "]"] [] ["using", expr congr_arg (λ
      f : «expr →ₗ[ ] »(F, exprℝ(), F), f x) (linear_map.ker_eq_top.mp this)] },
  { let [ident W] [] [":=", expr «expr - »(continuous_linear_map.id exprℝ() F, φ.to_continuous_linear_equiv).ker],
    have [ident hW] [":", expr ∀ w «expr ∈ » W, «expr = »(φ w, w)] [":=", expr λ w hw, (sub_eq_zero.mp hw).symm],
    by_cases [expr hn', ":", expr «expr ≤ »(finrank exprℝ() «expr ᗮ»(W), n)],
    { obtain ["⟨", ident V, ",", ident hV₁, ",", ident hV₂, "⟩", ":=", expr IH φ hn'],
      exact [expr ⟨V, hV₁.trans n.le_succ, hV₂⟩] },
    haveI [] [":", expr nontrivial «expr ᗮ»(W)] [":=", expr nontrivial_of_finrank_pos (by linarith [] [] ["[", expr zero_le n, "]"] : «expr < »(0, finrank exprℝ() «expr ᗮ»(W)))],
    obtain ["⟨", ident v, ",", ident hv, "⟩", ":=", expr exists_ne (0 : «expr ᗮ»(W))],
    have [ident hφv] [":", expr «expr ∈ »(φ v, «expr ᗮ»(W))] [],
    { intros [ident w, ident hw],
      rw ["[", "<-", expr hW w hw, ",", expr linear_isometry_equiv.inner_map_map, "]"] [],
      exact [expr v.prop w hw] },
    have [ident hv'] [":", expr «expr ∉ »((v : F), W)] [],
    { intros [ident h],
      exact [expr hv ((submodule.mem_left_iff_eq_zero_of_disjoint W.orthogonal_disjoint).mp h)] },
    let [ident x] [":", expr F] [":=", expr «expr - »(v, φ v)],
    let [ident ρ] [] [":=", expr reflection «expr ᗮ»(«expr ∙ »(exprℝ(), x))],
    let [ident V] [] [":=", expr «expr - »(continuous_linear_map.id exprℝ() F, (φ.trans ρ).to_continuous_linear_equiv).ker],
    have [ident hV] [":", expr ∀ w, «expr = »(ρ (φ w), w) → «expr ∈ »(w, V)] [],
    { intros [ident w, ident hw],
      change [expr «expr = »(«expr - »(w, ρ (φ w)), 0)] [] [],
      rw ["[", expr sub_eq_zero, ",", expr hw, "]"] [] },
    have [ident H₂V] [":", expr «expr ≤ »(W, V)] [],
    { intros [ident w, ident hw],
      apply [expr hV],
      rw [expr hW w hw] [],
      refine [expr reflection_mem_subspace_eq_self _],
      apply [expr mem_orthogonal_singleton_of_inner_left],
      exact [expr submodule.sub_mem _ v.prop hφv _ hw] },
    have [ident H₁V] [":", expr «expr ∈ »((v : F), V)] [],
    { apply [expr hV],
      have [] [":", expr «expr = »(ρ v, φ v)] [":=", expr reflection_sub (by simp [] [] [] [] [] [])],
      simp [] [] [] ["[", "<-", expr this, ",", expr ρ, "]"] [] [] },
    have [] [":", expr «expr ≤ »(finrank exprℝ() «expr ᗮ»(V), n)] [],
    { change [expr «expr ≤ »(finrank exprℝ() «expr ᗮ»(W), «expr + »(n, 1))] [] ["at", ident hn],
      have [] [":", expr «expr ≤ »(«expr + »(finrank exprℝ() W, 1), finrank exprℝ() V)] [":=", expr submodule.finrank_lt_finrank_of_lt (set_like.lt_iff_le_and_exists.2 ⟨H₂V, v, H₁V, hv'⟩)],
      have [] [":", expr «expr = »(«expr + »(finrank exprℝ() V, finrank exprℝ() «expr ᗮ»(V)), finrank exprℝ() F)] [":=", expr V.finrank_add_finrank_orthogonal],
      have [] [":", expr «expr = »(«expr + »(finrank exprℝ() W, finrank exprℝ() «expr ᗮ»(W)), finrank exprℝ() F)] [":=", expr W.finrank_add_finrank_orthogonal],
      linarith [] [] [] },
    obtain ["⟨", ident l, ",", ident hl, ",", ident hφl, "⟩", ":=", expr IH (φ.trans ρ) this],
    refine [expr ⟨[«expr :: »/«expr :: »/«expr :: »](x, l), _, _⟩],
    { simp [] [] [] ["[", expr hl, ",", expr nat.succ_le_succ, "]"] [] [] },
    have [] [] [":=", expr congr_arg (λ ψ, linear_isometry_equiv.trans ψ ρ) hφl],
    convert [] [expr this] ["using", 1],
    { simp [] [] [] ["[", "<-", expr linear_isometry_equiv.trans_assoc φ ρ ρ, "]"] [] [] },
    { change [expr «expr = »(_, «expr * »(_, _))] [] [],
      simp [] [] [] [] [] [] } }
end

/-- The orthogonal group of `F` is generated by reflections; specifically each element `φ` of the
orthogonal group is a product of at most as many reflections as the dimension of `F`.

Special case of the **Cartan–Dieudonné theorem**. -/
theorem LinearIsometryEquiv.reflections_generate_dim [FiniteDimensional ℝ F] (φ : F ≃ₗᵢ[ℝ] F) :
  ∃ l : List F, l.length ≤ finrank ℝ F ∧ φ = (l.map fun v => reflection (ℝ∙v)ᗮ).Prod :=
  let ⟨l, hl₁, hl₂⟩ := φ.reflections_generate_dim_aux le_rfl
  ⟨l, hl₁.trans (Submodule.finrank_le _), hl₂⟩

/-- The orthogonal group of `F` is generated by reflections. -/
theorem LinearIsometryEquiv.reflections_generate [FiniteDimensional ℝ F] :
  Subgroup.closure (Set.Range fun v : F => reflection (ℝ∙v)ᗮ) = ⊤ :=
  by 
    rw [Subgroup.eq_top_iff']
    intro φ 
    rcases φ.reflections_generate_dim with ⟨l, _, rfl⟩
    apply (Subgroup.closure _).list_prod_mem 
    intro x hx 
    rcases list.mem_map.mp hx with ⟨a, _, hax⟩
    exact Subgroup.subset_closure ⟨a, hax⟩

end Orthogonal

section OrthogonalFamily

variable {ι : Type _}

/-- An orthogonal family of subspaces of `E` satisfies `direct_sum.submodule_is_internal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
theorem OrthogonalFamily.submodule_is_internal_iff [DecidableEq ι] [FiniteDimensional 𝕜 E] {V : ι → Submodule 𝕜 E}
  (hV : OrthogonalFamily 𝕜 V) : DirectSum.SubmoduleIsInternal V ↔ (supr V)ᗮ = ⊥ :=
  by 
    simp only [DirectSum.submodule_is_internal_iff_independent_and_supr_eq_top, hV.independent, true_andₓ,
      Submodule.orthogonal_eq_bot_iff]

end OrthogonalFamily

section orthonormalBasis

/-! ### Existence of Hilbert basis, orthonormal basis, etc. -/


variable {𝕜 E} {v : Set E}

open FiniteDimensional Submodule Set

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the orthogonal
complement of its span is empty. -/
theorem maximal_orthonormal_iff_orthogonal_complement_eq_bot
(hv : orthonormal 𝕜 (coe : v → E)) : «expr ↔ »(∀
 u «expr ⊇ » v, orthonormal 𝕜 (coe : u → E) → «expr = »(u, v), «expr = »(«expr ᗮ»(span 𝕜 v), «expr⊥»())) :=
begin
  rw [expr submodule.eq_bot_iff] [],
  split,
  { contrapose ["!"] [],
    rintros ["⟨", ident x, ",", ident hx', ",", ident hx, "⟩"],
    let [ident e] [] [":=", expr «expr • »((«expr ⁻¹»(«expr∥ ∥»(x)) : 𝕜), x)],
    have [ident he] [":", expr «expr = »(«expr∥ ∥»(e), 1)] [":=", expr by simp [] [] [] ["[", expr e, ",", expr norm_smul_inv_norm hx, "]"] [] []],
    have [ident he'] [":", expr «expr ∈ »(e, «expr ᗮ»(span 𝕜 v))] [":=", expr smul_mem' _ _ hx'],
    have [ident he''] [":", expr «expr ∉ »(e, v)] [],
    { intros [ident hev],
      have [] [":", expr «expr = »(e, 0)] [],
      { have [] [":", expr «expr ∈ »(e, «expr ⊓ »(span 𝕜 v, «expr ᗮ»(span 𝕜 v)))] [":=", expr ⟨subset_span hev, he'⟩],
        simpa [] [] [] ["[", expr (span 𝕜 v).inf_orthogonal_eq_bot, "]"] [] ["using", expr this] },
      have [] [":", expr «expr ≠ »(e, 0)] [":=", expr hv.ne_zero ⟨e, hev⟩],
      contradiction },
    refine [expr ⟨v.insert e, v.subset_insert e, ⟨_, _⟩, (v.ne_insert_of_not_mem he'').symm⟩],
    { rintros ["⟨", ident a, ",", ident ha', "⟩"],
      cases [expr eq_or_mem_of_mem_insert ha'] ["with", ident ha, ident ha],
      { simp [] [] [] ["[", expr ha, ",", expr he, "]"] [] [] },
      { exact [expr hv.1 ⟨a, ha⟩] } },
    { have [ident h_end] [":", expr ∀ a «expr ∈ » v, «expr = »(«expr⟪ , ⟫»(a, e), 0)] [],
      { intros [ident a, ident ha],
        exact [expr he' a (submodule.subset_span ha)] },
      rintros ["⟨", ident a, ",", ident ha', "⟩"],
      cases [expr eq_or_mem_of_mem_insert ha'] ["with", ident ha, ident ha],
      { rintros ["⟨", ident b, ",", ident hb', "⟩", ident hab'],
        have [ident hb] [":", expr «expr ∈ »(b, v)] [],
        { refine [expr mem_of_mem_insert_of_ne hb' _],
          intros [ident hbe'],
          apply [expr hab'],
          simp [] [] [] ["[", expr ha, ",", expr hbe', "]"] [] [] },
        rw [expr inner_eq_zero_sym] [],
        simpa [] [] [] ["[", expr ha, "]"] [] ["using", expr h_end b hb] },
      rintros ["⟨", ident b, ",", ident hb', "⟩", ident hab'],
      cases [expr eq_or_mem_of_mem_insert hb'] ["with", ident hb, ident hb],
      { simpa [] [] [] ["[", expr hb, "]"] [] ["using", expr h_end a ha] },
      have [] [":", expr «expr ≠ »((⟨a, ha⟩ : v), ⟨b, hb⟩)] [],
      { intros [ident hab''],
        apply [expr hab'],
        simpa [] [] [] [] [] ["using", expr hab''] },
      exact [expr hv.2 this] } },
  { simp [] [] ["only"] ["[", expr subset.antisymm_iff, "]"] [] [],
    rintros [ident h, ident u, "(", ident huv, ":", expr «expr ⊆ »(v, u), ")", ident hu],
    refine [expr ⟨_, huv⟩],
    intros [ident x, ident hxu],
    refine [expr (mt (h x) (hu.ne_zero ⟨x, hxu⟩)).imp_symm _],
    intros [ident hxv, ident y, ident hy],
    have [ident hxv'] [":", expr «expr ∉ »((⟨x, hxu⟩ : u), («expr ⁻¹' »(coe, v) : set u))] [":=", expr by simp [] [] [] ["[", expr huv, ",", expr hxv, "]"] [] []],
    obtain ["⟨", ident l, ",", ident hl, ",", ident rfl, "⟩", ":", expr «expr∃ , »((l «expr ∈ » finsupp.supported 𝕜 𝕜 («expr ⁻¹' »(coe, v) : set u)), «expr = »(finsupp.total «expr↥ »(u) E 𝕜 coe l, y))],
    { rw ["<-", expr finsupp.mem_span_image_iff_total] [],
      simp [] [] [] ["[", expr huv, ",", expr inter_eq_self_of_subset_left, ",", expr hy, "]"] [] [] },
    exact [expr hu.inner_finsupp_eq_zero hxv' hl] }
end

/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the closure of its
span is the whole space. -/
theorem maximal_orthonormal_iff_dense_span [CompleteSpace E] (hv : Orthonormal 𝕜 (coeₓ : v → E)) :
  (∀ u _ : u ⊇ v, Orthonormal 𝕜 (coeₓ : u → E) → u = v) ↔ (span 𝕜 v).topologicalClosure = ⊤ :=
  by 
    rw [maximal_orthonormal_iff_orthogonal_complement_eq_bot hv, ←Submodule.orthogonal_eq_top_iff,
      (span 𝕜 v).orthogonal_orthogonal_eq_closure]

/-- Any orthonormal subset can be extended to an orthonormal set whose span is dense. -/
theorem exists_subset_is_orthonormal_dense_span [CompleteSpace E] (hv : Orthonormal 𝕜 (coeₓ : v → E)) :
  ∃ (u : _)(_ : u ⊇ v), Orthonormal 𝕜 (coeₓ : u → E) ∧ (span 𝕜 u).topologicalClosure = ⊤ :=
  by 
    obtain ⟨u, hus, hu, hu_max⟩ := exists_maximal_orthonormal hv 
    rw [maximal_orthonormal_iff_dense_span hu] at hu_max 
    exact ⟨u, hus, hu, hu_max⟩

variable (𝕜 E)

/-- An inner product space admits an orthonormal set whose span is dense. -/
theorem exists_is_orthonormal_dense_span [CompleteSpace E] :
  ∃ u : Set E, Orthonormal 𝕜 (coeₓ : u → E) ∧ (span 𝕜 u).topologicalClosure = ⊤ :=
  let ⟨u, hus, hu, hu_max⟩ := exists_subset_is_orthonormal_dense_span (orthonormal_empty 𝕜 E)
  ⟨u, hu, hu_max⟩

variable {𝕜 E}

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An orthonormal set in a finite-dimensional `inner_product_space` is maximal, if and only if it
is a basis. -/
theorem maximal_orthonormal_iff_basis_of_finite_dimensional
(hv : orthonormal 𝕜 (coe : v → E)) : «expr ↔ »(∀
 u «expr ⊇ » v, orthonormal 𝕜 (coe : u → E) → «expr = »(u, v), «expr∃ , »((b : basis v 𝕜 E), «expr = »(«expr⇑ »(b), coe))) :=
begin
  rw [expr maximal_orthonormal_iff_orthogonal_complement_eq_bot hv] [],
  have [ident hv_compl] [":", expr is_complete (span 𝕜 v : set E)] [":=", expr (span 𝕜 v).complete_of_finite_dimensional],
  rw [expr submodule.orthogonal_eq_bot_iff] [],
  have [ident hv_coe] [":", expr «expr = »(range (coe : v → E), v)] [":=", expr by simp [] [] [] [] [] []],
  split,
  { refine [expr λ h, ⟨basis.mk hv.linear_independent _, basis.coe_mk _ _⟩],
    convert [] [expr h] [] },
  { rintros ["⟨", ident h, ",", ident coe_h, "⟩"],
    rw ["[", "<-", expr h.span_eq, ",", expr coe_h, ",", expr hv_coe, "]"] [] }
end

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
theorem exists_subset_is_orthonormal_basis (hv : Orthonormal 𝕜 (coeₓ : v → E)) :
  ∃ (u : _)(_ : u ⊇ v)(b : Basis u 𝕜 E), Orthonormal 𝕜 b ∧ «expr⇑ » b = coeₓ :=
  by 
    obtain ⟨u, hus, hu, hu_max⟩ := exists_maximal_orthonormal hv 
    obtain ⟨b, hb⟩ := (maximal_orthonormal_iff_basis_of_finite_dimensional hu).mp hu_max 
    exact
      ⟨u, hus, b,
        by 
          rwa [hb],
        hb⟩

variable (𝕜 E)

/-- Index for an arbitrary orthonormal basis on a finite-dimensional `inner_product_space`. -/
def OrthonormalBasisIndex : Set E :=
  Classical.some (exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E))

/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
def orthonormalBasis : Basis (OrthonormalBasisIndex 𝕜 E) 𝕜 E :=
  (exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E)).some_spec.some_spec.some

theorem orthonormal_basis_orthonormal : Orthonormal 𝕜 (orthonormalBasis 𝕜 E) :=
  (exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E)).some_spec.some_spec.some_spec.1

@[simp]
theorem coe_orthonormal_basis : «expr⇑ » (orthonormalBasis 𝕜 E) = coeₓ :=
  (exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E)).some_spec.some_spec.some_spec.2

instance : Fintype (OrthonormalBasisIndex 𝕜 E) :=
  @IsNoetherian.fintypeBasisIndex _ _ _ _ _ _ _ (IsNoetherian.iff_fg.2 inferInstance) (orthonormalBasis 𝕜 E)

variable {𝕜 E}

/-- An `n`-dimensional `inner_product_space` has an orthonormal basis indexed by `fin n`. -/
def finOrthonormalBasis {n : ℕ} (hn : finrank 𝕜 E = n) : Basis (Finₓ n) 𝕜 E :=
  have h : Fintype.card (OrthonormalBasisIndex 𝕜 E) = n :=
    by 
      rw [←finrank_eq_card_basis (orthonormalBasis 𝕜 E), hn]
  (orthonormalBasis 𝕜 E).reindex (Fintype.equivFinOfCardEq h)

theorem fin_orthonormal_basis_orthonormal {n : ℕ} (hn : finrank 𝕜 E = n) : Orthonormal 𝕜 (finOrthonormalBasis hn) :=
  suffices Orthonormal 𝕜 (orthonormalBasis _ _ ∘ Equiv.symm _)by 
    simp only [finOrthonormalBasis, Basis.coe_reindex]
    assumption
  (orthonormal_basis_orthonormal 𝕜 E).comp _ (Equiv.injective _)

section SubordinateOrthonormalBasis

open DirectSum

variable {n : ℕ} (hn : finrank 𝕜 E = n) {ι : Type _} [Fintype ι] [DecidableEq ι] {V : ι → Submodule 𝕜 E}
  (hV : submodule_is_internal V)

/-- Exhibit a bijection between `fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
@[irreducible]
def DirectSum.SubmoduleIsInternal.sigmaOrthonormalBasisIndexEquiv : (Σi, OrthonormalBasisIndex 𝕜 (V i)) ≃ Finₓ n :=
  let b := hV.collected_basis fun i => orthonormalBasis 𝕜 (V i)
  Fintype.equivFinOfCardEq$ (FiniteDimensional.finrank_eq_card_basis b).symm.trans hn

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. -/
@[irreducible]
def DirectSum.SubmoduleIsInternal.subordinateOrthonormalBasis : Basis (Finₓ n) 𝕜 E :=
  (hV.collected_basis fun i => orthonormalBasis 𝕜 (V i)).reindex (hV.sigma_orthonormal_basis_index_equiv hn)

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
def DirectSum.SubmoduleIsInternal.subordinateOrthonormalBasisIndex (a : Finₓ n) : ι :=
  ((hV.sigma_orthonormal_basis_index_equiv hn).symm a).1

-- error in Analysis.InnerProductSpace.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The basis constructed in `orthogonal_family.subordinate_orthonormal_basis` is orthonormal. -/
theorem direct_sum.submodule_is_internal.subordinate_orthonormal_basis_orthonormal
(hV' : orthogonal_family 𝕜 V) : orthonormal 𝕜 (hV.subordinate_orthonormal_basis hn) :=
begin
  simp [] [] ["only"] ["[", expr direct_sum.submodule_is_internal.subordinate_orthonormal_basis, ",", expr basis.coe_reindex, "]"] [] [],
  have [] [":", expr orthonormal 𝕜 (hV.collected_basis (λ
     i, orthonormal_basis 𝕜 (V i)))] [":=", expr hV.collected_basis_orthonormal hV' (λ
    i, orthonormal_basis_orthonormal 𝕜 (V i))],
  exact [expr this.comp _ (equiv.injective _)]
end

/-- The basis constructed in `orthogonal_family.subordinate_orthonormal_basis` is subordinate to
the `orthogonal_family` in question. -/
theorem DirectSum.SubmoduleIsInternal.subordinate_orthonormal_basis_subordinate (a : Finₓ n) :
  hV.subordinate_orthonormal_basis hn a ∈ V (hV.subordinate_orthonormal_basis_index hn a) :=
  by 
    simpa only [DirectSum.SubmoduleIsInternal.subordinateOrthonormalBasis, Basis.coe_reindex] using
      hV.collected_basis_mem (fun i => orthonormalBasis 𝕜 (V i)) ((hV.sigma_orthonormal_basis_index_equiv hn).symm a)

attribute [irreducible] DirectSum.SubmoduleIsInternal.subordinateOrthonormalBasisIndex

end SubordinateOrthonormalBasis

end FiniteDimensional

end orthonormalBasis

