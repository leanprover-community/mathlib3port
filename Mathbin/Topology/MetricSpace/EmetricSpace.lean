import Mathbin.Data.Nat.Interval 
import Mathbin.Data.Real.Ennreal 
import Mathbin.Topology.UniformSpace.Pi 
import Mathbin.Topology.UniformSpace.UniformConvergence 
import Mathbin.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

This file is devoted to the definition and study of `emetric_spaces`, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `emetric_space` therefore extends `uniform_space` (and `topological_space`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `pseudo_emetric_space`, where we don't require `edist x y = 0 → x = y` and we specialize
to `emetric_space` at the end.
-/


open Set Filter Classical

noncomputable theory

open_locale uniformity TopologicalSpace BigOperators Filter Nnreal Ennreal

universe u v w

variable {α : Type u} {β : Type v}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [LinearOrderₓ β] {U : Filter (α × α)} (z : β) (D : α → α → β)
  (H : ∀ s, s ∈ U ↔ ∃ (ε : _)(_ : ε > z), ∀ {a b : α}, D a b < ε → (a, b) ∈ s) :
  U = ⨅(ε : _)(_ : ε > z), 𝓟 { p:α × α | D p.1 p.2 < ε } :=
  le_antisymmₓ (le_infi$ fun ε => le_infi$ fun ε0 => le_principal_iff.2$ (H _).2 ⟨ε, ε0, fun a b => id⟩)
    fun r ur =>
      let ⟨ε, ε0, h⟩ := (H _).1 ur 
      mem_infi_of_mem ε$ mem_infi_of_mem ε0$ mem_principal.2$ fun ⟨a, b⟩ => h

/-- `has_edist α` means that `α` is equipped with an extended distance. -/
class HasEdist (α : Type _) where 
  edist : α → α → ℝ≥0∞

export HasEdist(edist)

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Creating a uniform space from an extended distance. -/
def uniform_space_of_edist
(edist : α → α → «exprℝ≥0∞»())
(edist_self : ∀ x : α, «expr = »(edist x x, 0))
(edist_comm : ∀ x y : α, «expr = »(edist x y, edist y x))
(edist_triangle : ∀ x y z : α, «expr ≤ »(edist x z, «expr + »(edist x y, edist y z))) : uniform_space α :=
uniform_space.of_core { uniformity := «expr⨅ , »((ε «expr > » 0), expr𝓟() {p : «expr × »(α, α) | «expr < »(edist p.1 p.2, ε)}),
  refl := «expr $ »(le_infi, assume
   ε, «expr $ »(le_infi, by simp [] [] [] ["[", expr set.subset_def, ",", expr id_rel, ",", expr edist_self, ",", expr («expr > »), "]"] [] [] { contextual := tt })),
  comp := «expr $ »(le_infi, assume
   ε, «expr $ »(le_infi, assume h, have «expr = »((2 : «exprℝ≥0∞»()), (2 : exprℕ())) := by simp [] [] [] [] [] [],
    have A : «expr < »(0, «expr / »(ε, 2)) := ennreal.div_pos_iff.2 ⟨ne_of_gt h, by { convert [] [expr ennreal.nat_ne_top 2] [] }⟩,
    «expr $ »(lift'_le «expr $ »(mem_infi_of_mem «expr / »(ε, 2), mem_infi_of_mem A (subset.refl _)), have ∀
     a
     b
     c : α, «expr < »(edist a c, «expr / »(ε, 2)) → «expr < »(edist c b, «expr / »(ε, 2)) → «expr < »(edist a b, ε), from assume
     a b c hac hcb, calc
       «expr ≤ »(edist a b, «expr + »(edist a c, edist c b)) : edist_triangle _ _ _
       «expr < »(..., «expr + »(«expr / »(ε, 2), «expr / »(ε, 2))) : ennreal.add_lt_add hac hcb
       «expr = »(..., ε) : by rw ["[", expr ennreal.add_halves, "]"] [],
     by simpa [] [] [] ["[", expr comp_rel, "]"] [] []))),
  symm := «expr $ »(tendsto_infi.2, assume
   ε, «expr $ »(tendsto_infi.2, assume
    h, «expr $ »(tendsto_infi' ε, «expr $ »(tendsto_infi' h, «expr $ »(tendsto_principal_principal.2, by simp [] [] [] ["[", expr edist_comm, "]"] [] []))))) }

/-- Extended (pseudo) metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each pseudo_emetric space induces a canonical `uniform_space` and hence a canonical
`topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `pseudo_emetric_space` structure, the uniformity fields are not necessary, they
will be filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating a `pseudo_emetric_space` structure
on a product.

Continuity of `edist` is proved in `topology.instances.ennreal`
-/
class PseudoEmetricSpace (α : Type u) extends HasEdist α : Type u where 
  edist_self : ∀ x : α, edist x x = 0 
  edist_comm : ∀ x y : α, edist x y = edist y x 
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y+edist y z 
  toUniformSpace : UniformSpace α := uniformSpaceOfEdist edist edist_self edist_comm edist_triangle 
  uniformity_edist : 𝓤 α = ⨅(ε : _)(_ : ε > 0), 𝓟 { p:α × α | edist p.1 p.2 < ε } :=  by 
  runTac 
    control_laws_tac

variable [PseudoEmetricSpace α]

instance (priority := 100) PseudoEmetricSpace.toUniformSpace' : UniformSpace α :=
  PseudoEmetricSpace.toUniformSpace

export PseudoEmetricSpace(edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x+edist z y :=
  by 
    rw [edist_comm z] <;> apply edist_triangle

theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z+edist y z :=
  by 
    rw [edist_comm y] <;> apply edist_triangle

theorem edist_triangle4 (x y z t : α) : edist x t ≤ (edist x y+edist y z)+edist z t :=
  calc edist x t ≤ edist x z+edist z t := edist_triangle x z t 
    _ ≤ (edist x y+edist y z)+edist z t := add_le_add_right (edist_triangle x y z) _
    

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
  edist (f m) (f n) ≤ ∑i in Finset.ico m n, edist (f i) (f (i+1)) :=
  by 
    revert n 
    refine' Nat.le_induction _ _
    ·
      simp only [Finset.sum_empty, Finset.Ico_self, edist_self]
      exact le_reflₓ (0 : ℝ≥0∞)
    ·
      intro n hn hrec 
      calc edist (f m) (f (n+1)) ≤ edist (f m) (f n)+edist (f n) (f (n+1)) :=
        edist_triangle _ _ _ _ ≤ (∑i in Finset.ico m n, _)+_ :=
        add_le_add hrec le_rfl _ = ∑i in Finset.ico m (n+1), _ :=
        by 
          rw [Nat.Ico_succ_right_eq_insert_Ico hn, Finset.sum_insert, add_commₓ] <;> simp 

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
  edist (f 0) (f n) ≤ ∑i in Finset.range n, edist (f i) (f (i+1)) :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_edist f (Nat.zero_leₓ n)

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
  (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k+1)) ≤ d k) : edist (f m) (f n) ≤ ∑i in Finset.ico m n, d i :=
  le_transₓ (edist_le_Ico_sum_edist f hmn)$
    Finset.sum_le_sum$ fun k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
  (hd : ∀ {k}, k < n → edist (f k) (f (k+1)) ≤ d k) : edist (f 0) (f n) ≤ ∑i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_of_edist_le (zero_le n) fun _ _ => hd

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_pseudoedist : 𝓤 α = ⨅(ε : _)(_ : ε > 0), 𝓟 { p:α × α | edist p.1 p.2 < ε } :=
  PseudoEmetricSpace.uniformity_edist

theorem uniformity_basis_edist : (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p:α × α | edist p.1 p.2 < ε } :=
  (@uniformity_pseudoedist α _).symm ▸
    has_basis_binfi_principal
      (fun r hr p hp =>
        ⟨min r p, lt_minₓ hr hp, fun x hx => lt_of_lt_of_leₓ hx (min_le_leftₓ _ _),
          fun x hx => lt_of_lt_of_leₓ hx (min_le_rightₓ _ _)⟩)
      ⟨1, Ennreal.zero_lt_one⟩

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {s : Set (α × α)} :
  s ∈ 𝓤 α ↔ ∃ (ε : _)(_ : ε > 0), ∀ {a b : α}, edist a b < ε → (a, b) ∈ s :=
  uniformity_basis_edist.mem_uniformity_iff

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
protected theorem Emetric.mk_uniformity_basis {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞} (hf₀ : ∀ x, p x → 0 < f x)
  (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) : (𝓤 α).HasBasis p fun x => { p:α × α | edist p.1 p.2 < f x } :=
  by 
    refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
    split 
    ·
      rintro ⟨ε, ε₀, hε⟩
      rcases hf ε ε₀ with ⟨i, hi, H⟩
      exact ⟨i, hi, fun x hx => hε$ lt_of_lt_of_leₓ hx H⟩
    ·
      exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
protected theorem Emetric.mk_uniformity_basis_le {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞} (hf₀ : ∀ x, p x → 0 < f x)
  (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) : (𝓤 α).HasBasis p fun x => { p:α × α | edist p.1 p.2 ≤ f x } :=
  by 
    refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
    split 
    ·
      rintro ⟨ε, ε₀, hε⟩
      rcases exists_between ε₀ with ⟨ε', hε'⟩
      rcases hf ε' hε'.1 with ⟨i, hi, H⟩
      exact ⟨i, hi, fun x hx => hε$ lt_of_le_of_ltₓ (le_transₓ hx H) hε'.2⟩
    ·
      exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_ltₓ hx)⟩

theorem uniformity_basis_edist_le : (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p:α × α | edist p.1 p.2 ≤ ε } :=
  Emetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_reflₓ ε⟩

theorem uniformity_basis_edist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
  (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p:α × α | edist p.1 p.2 < ε } :=
  Emetric.mk_uniformity_basis (fun _ => And.left)
    fun ε ε₀ =>
      let ⟨δ, hδ⟩ := exists_between hε'
      ⟨min ε δ, ⟨lt_minₓ ε₀ hδ.1, lt_of_le_of_ltₓ (min_le_rightₓ _ _) hδ.2⟩, min_le_leftₓ _ _⟩

theorem uniformity_basis_edist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
  (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p:α × α | edist p.1 p.2 ≤ ε } :=
  Emetric.mk_uniformity_basis_le (fun _ => And.left)
    fun ε ε₀ =>
      let ⟨δ, hδ⟩ := exists_between hε'
      ⟨min ε δ, ⟨lt_minₓ ε₀ hδ.1, lt_of_le_of_ltₓ (min_le_rightₓ _ _) hδ.2⟩, min_le_leftₓ _ _⟩

theorem uniformity_basis_edist_nnreal :
  (𝓤 α).HasBasis (fun ε :  ℝ≥0  => 0 < ε) fun ε => { p:α × α | edist p.1 p.2 < ε } :=
  Emetric.mk_uniformity_basis (fun _ => Ennreal.coe_pos.2)
    fun ε ε₀ =>
      let ⟨δ, hδ⟩ := Ennreal.lt_iff_exists_nnreal_btwn.1 ε₀
      ⟨δ, Ennreal.coe_pos.1 hδ.1, le_of_ltₓ hδ.2⟩

theorem uniformity_basis_edist_inv_nat :
  (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p:α × α | edist p.1 p.2 < «expr↑ » n⁻¹ } :=
  Emetric.mk_uniformity_basis (fun n _ => Ennreal.inv_pos.2$ Ennreal.nat_ne_top n)
    fun ε ε₀ =>
      let ⟨n, hn⟩ := Ennreal.exists_inv_nat_lt (ne_of_gtₓ ε₀)
      ⟨n, trivialₓ, le_of_ltₓ hn⟩

theorem uniformity_basis_edist_inv_two_pow :
  (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p:α × α | edist p.1 p.2 < 2⁻¹ ^ n } :=
  Emetric.mk_uniformity_basis (fun n _ => Ennreal.pow_pos (Ennreal.inv_pos.2 Ennreal.two_ne_top) _)
    fun ε ε₀ =>
      let ⟨n, hn⟩ := Ennreal.exists_inv_two_pow_lt (ne_of_gtₓ ε₀)
      ⟨n, trivialₓ, le_of_ltₓ hn⟩

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p:α × α | edist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, fun a b => id⟩

namespace Emetric

instance (priority := 900) : is_countably_generated (𝓤 α) :=
  is_countably_generated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_infi⟩

/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
theorem uniform_continuous_on_iff [PseudoEmetricSpace β] {f : α → β} {s : Set α} :
  UniformContinuousOn f s ↔
    ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {a b}, a ∈ s → b ∈ s → edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniform_continuous_on_iff uniformity_basis_edist

/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
theorem uniform_continuous_iff [PseudoEmetricSpace β] {f : α → β} :
  UniformContinuous f ↔ ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniform_continuous_iff uniformity_basis_edist

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
theorem uniform_embedding_iff [PseudoEmetricSpace β] {f : α → β} :
  UniformEmbedding f ↔
    Function.Injective f ∧
      UniformContinuous f ∧ ∀ δ _ : δ > 0, ∃ (ε : _)(_ : ε > 0), ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  uniform_embedding_def'.trans$
    and_congr Iff.rfl$
      and_congr Iff.rfl
        ⟨fun H δ δ0 =>
            let ⟨t, tu, ht⟩ := H _ (edist_mem_uniformity δ0)
            let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 tu
            ⟨ε, ε0, fun a b h => ht _ _ (hε h)⟩,
          fun H s su =>
            let ⟨δ, δ0, hδ⟩ := mem_uniformity_edist.1 su 
            let ⟨ε, ε0, hε⟩ := H _ δ0
            ⟨_, edist_mem_uniformity ε0, fun a b h => hδ (hε h)⟩⟩

/-- If a map between pseudoemetric spaces is a uniform embedding then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniform_embedding [PseudoEmetricSpace β] {f : α → β} :
  UniformEmbedding f →
    (∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
      ∀ δ _ : δ > 0, ∃ (ε : _)(_ : ε > 0), ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  by 
    intro h 
    exact ⟨uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1, (uniform_embedding_iff.1 h).2.2⟩

/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
protected theorem cauchy_iff {f : Filter α} :
  Cauchy f ↔ f ≠ ⊥ ∧ ∀ ε _ : ε > 0, ∃ (t : _)(_ : t ∈ f), ∀ x y _ : x ∈ t _ : y ∈ t, edist x y < ε :=
  by 
    rw [←ne_bot_iff] <;> exact uniformity_basis_edist.cauchy_iff

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀ n, 0 < B n)
  (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) → ∃ x, tendsto u at_top (𝓝 x)) :
  CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences (fun n => { p:α × α | edist p.1 p.2 < B n })
    (fun n => edist_mem_uniformity$ hB n) H

/-- A sequentially complete pseudoemetric space is complete. -/
theorem complete_of_cauchy_seq_tendsto : (∀ u : ℕ → α, CauchySeq u → ∃ a, tendsto u at_top (𝓝 a)) → CompleteSpace α :=
  UniformSpace.complete_of_cauchy_seq_tendsto

/-- Expressing locally uniform convergence on a set using `edist`. -/
theorem tendsto_locally_uniformly_on_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α} {p : Filter ι}
  {s : Set β} :
  TendstoLocallyUniformlyOn F f p s ↔
    ∀ ε _ : ε > 0, ∀ x _ : x ∈ s, ∃ (t : _)(_ : t ∈ 𝓝[s] x), ∀ᶠn in p, ∀ y _ : y ∈ t, edist (f y) (F n y) < ε :=
  by 
    refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => _⟩
    rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
    rcases H ε εpos x hx with ⟨t, ht, Ht⟩
    exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `edist`. -/
theorem tendsto_uniformly_on_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
  TendstoUniformlyOn F f p s ↔ ∀ ε _ : ε > 0, ∀ᶠn in p, ∀ x _ : x ∈ s, edist (f x) (F n x) < ε :=
  by 
    refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => _⟩
    rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
    exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/-- Expressing locally uniform convergence using `edist`. -/
theorem tendsto_locally_uniformly_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α} {p : Filter ι} :
  TendstoLocallyUniformly F f p ↔
    ∀ ε _ : ε > 0, ∀ x : β, ∃ (t : _)(_ : t ∈ 𝓝 x), ∀ᶠn in p, ∀ y _ : y ∈ t, edist (f y) (F n y) < ε :=
  by 
    simp only [←tendsto_locally_uniformly_on_univ, tendsto_locally_uniformly_on_iff, mem_univ, forall_const,
      exists_prop, nhds_within_univ]

/-- Expressing uniform convergence using `edist`. -/
theorem tendsto_uniformly_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} :
  TendstoUniformly F f p ↔ ∀ ε _ : ε > 0, ∀ᶠn in p, ∀ x, edist (f x) (F n x) < ε :=
  by 
    simp only [←tendsto_uniformly_on_univ, tendsto_uniformly_on_iff, mem_univ, forall_const]

end Emetric

open Emetric

/-- Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def PseudoEmetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEmetricSpace α)
  (H : @uniformity _ U = @uniformity _ PseudoEmetricSpace.toUniformSpace) : PseudoEmetricSpace α :=
  { edist := @edist _ m.to_has_edist, edist_self := edist_self, edist_comm := edist_comm,
    edist_triangle := edist_triangle, toUniformSpace := U,
    uniformity_edist := H.trans (@PseudoEmetricSpace.uniformity_edist α _) }

/-- The extended pseudometric induced by a function taking values in a pseudoemetric space. -/
def PseudoEmetricSpace.induced {α β} (f : α → β) (m : PseudoEmetricSpace β) : PseudoEmetricSpace α :=
  { edist := fun x y => edist (f x) (f y), edist_self := fun x => edist_self _, edist_comm := fun x y => edist_comm _ _,
    edist_triangle := fun x y z => edist_triangle _ _ _, toUniformSpace := UniformSpace.comap f m.to_uniform_space,
    uniformity_edist :=
      by 
        apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ fun x y => edist (f x) (f y)
        refine' fun s => mem_comap.trans _ 
        split  <;> intro H
        ·
          rcases H with ⟨r, ru, rs⟩
          rcases mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩
          refine' ⟨ε, ε0, fun a b h => rs (hε _)⟩
          exact h
        ·
          rcases H with ⟨ε, ε0, hε⟩
          exact ⟨_, edist_mem_uniformity ε0, fun ⟨a, b⟩ => hε⟩ }

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type _} {p : α → Prop} [t : PseudoEmetricSpace α] : PseudoEmetricSpace (Subtype p) :=
  t.induced coeₓ

/-- The extended psuedodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition -/
theorem Subtype.edist_eq {p : α → Prop} (x y : Subtype p) : edist x y = edist (x : α) y :=
  rfl

/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.pseudoEmetricSpaceMax [PseudoEmetricSpace β] : PseudoEmetricSpace (α × β) :=
  { edist := fun x y => max (edist x.1 y.1) (edist x.2 y.2),
    edist_self :=
      fun x =>
        by 
          simp ,
    edist_comm :=
      fun x y =>
        by 
          simp [edist_comm],
    edist_triangle :=
      fun x y z =>
        max_leₓ (le_transₓ (edist_triangle _ _ _) (add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _)))
          (le_transₓ (edist_triangle _ _ _) (add_le_add (le_max_rightₓ _ _) (le_max_rightₓ _ _))),
    uniformity_edist :=
      by 
        refine' uniformity_prod.trans _ 
        simp only [PseudoEmetricSpace.uniformity_edist, comap_infi]
        rw [←infi_inf_eq]
        congr 
        funext 
        rw [←infi_inf_eq]
        congr 
        funext 
        simp [inf_principal, ext_iff, max_lt_iff],
    toUniformSpace := Prod.uniformSpace }

theorem Prod.edist_eq [PseudoEmetricSpace β] (x y : α × β) : edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
  rfl

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance pseudoEmetricSpacePi [∀ b, PseudoEmetricSpace (π b)] : PseudoEmetricSpace (∀ b, π b) :=
  { edist := fun f g => Finset.sup univ fun b => edist (f b) (g b),
    edist_self :=
      fun f =>
        bot_unique$
          Finset.sup_le$
            by 
              simp ,
    edist_comm :=
      fun f g =>
        by 
          unfold edist <;> congr <;> funext a <;> exact edist_comm _ _,
    edist_triangle :=
      fun f g h =>
        by 
          simp only [Finset.sup_le_iff]
          intro b hb 
          exact le_transₓ (edist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb)),
    toUniformSpace := Pi.uniformSpace _,
    uniformity_edist :=
      by 
        simp only [Pi.uniformity, PseudoEmetricSpace.uniformity_edist, comap_infi, gt_iff_lt, preimage_set_of_eq,
          comap_principal]
        rw [infi_comm]
        congr 
        funext ε 
        rw [infi_comm]
        congr 
        funext εpos 
        change 0 < ε at εpos 
        simp [Set.ext_iff, εpos] }

theorem edist_pi_def [∀ b, PseudoEmetricSpace (π b)] (f g : ∀ b, π b) :
  edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl

@[simp]
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun x : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)

theorem edist_le_pi_edist [∀ b, PseudoEmetricSpace (π b)] (f g : ∀ b, π b) (b : β) : edist (f b) (g b) ≤ edist f g :=
  Finset.le_sup (Finset.mem_univ b)

theorem edist_pi_le_iff [∀ b, PseudoEmetricSpace (π b)] {f g : ∀ b, π b} {d : ℝ≥0∞} :
  edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans$
    by 
      simp only [Finset.mem_univ, forall_const]

end Pi

namespace Emetric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set α}

/-- `emetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
def ball (x : α) (ε : ℝ≥0∞) : Set α :=
  { y | edist y x < ε }

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ edist y x < ε :=
  Iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ edist x y < ε :=
  by 
    rw [edist_comm] <;> rfl

/-- `emetric.closed_ball x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def closed_ball (x : α) (ε : ℝ≥0∞) :=
  { y | edist y x ≤ ε }

@[simp]
theorem mem_closed_ball : y ∈ closed_ball x ε ↔ edist y x ≤ ε :=
  Iff.rfl

@[simp]
theorem closed_ball_top (x : α) : closed_ball x ∞ = univ :=
  eq_univ_of_forall$ fun y => le_top

theorem ball_subset_closed_ball : ball x ε ⊆ closed_ball x ε :=
  fun y hy => le_of_ltₓ hy

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  lt_of_le_of_ltₓ (zero_le _) hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
  show edist x x < ε by 
    rw [edist_self] <;> assumption

theorem mem_closed_ball_self : x ∈ closed_ball x ε :=
  show edist x x ≤ ε by 
    rw [edist_self] <;> exact bot_le

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
  by 
    simp [edist_comm]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
  fun y yx : _ < ε₁ => lt_of_lt_of_leₓ yx h

theorem closed_ball_subset_closed_ball (h : ε₁ ≤ ε₂) : closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
  fun y yx : _ ≤ ε₁ => le_transₓ yx h

theorem ball_disjoint (h : (ε₁+ε₂) ≤ edist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
  eq_empty_iff_forall_not_mem.2$
    fun z ⟨h₁, h₂⟩ => not_lt_of_le (edist_triangle_left x y z) (lt_of_lt_of_leₓ (Ennreal.add_lt_add h₁ h₂) h)

theorem ball_subset (h : (edist x y+ε₁) ≤ ε₂) (h' : edist x y ≠ ∞) : ball x ε₁ ⊆ ball y ε₂ :=
  fun z zx =>
    calc edist z y ≤ edist z x+edist x y := edist_triangle _ _ _ 
      _ = edist x y+edist z x := add_commₓ _ _ 
      _ < edist x y+ε₁ := Ennreal.add_lt_add_left h' zx 
      _ ≤ ε₂ := h
      

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_ball_subset_ball
(h : «expr ∈ »(y, ball x ε)) : «expr∃ , »((ε' «expr > » 0), «expr ⊆ »(ball y ε', ball x ε)) :=
begin
  have [] [":", expr «expr < »(0, «expr - »(ε, edist y x))] [":=", expr by simpa [] [] [] [] [] ["using", expr h]],
  refine [expr ⟨«expr - »(ε, edist y x), this, ball_subset _ (ne_top_of_lt h)⟩],
  exact [expr (add_tsub_cancel_of_le (mem_ball.mp h).le).le]
end

theorem ball_eq_empty_iff : ball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_not_mem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gtₓ fun ε0 => h _ (mem_ball_self ε0)),
      fun ε0 y h => not_lt_of_le (le_of_eqₓ ε0) (pos_of_mem_ball h)⟩

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
def edist_lt_top_setoid : Setoidₓ α :=
  { R := fun x y => edist x y < ⊤,
    iseqv :=
      ⟨fun x =>
          by 
            rw [edist_self]
            exact Ennreal.coe_lt_top,
        fun x y h =>
          by 
            rwa [edist_comm],
        fun x y z hxy hyz => lt_of_le_of_ltₓ (edist_triangle x y z) (Ennreal.add_lt_top.2 ⟨hxy, hyz⟩)⟩ }

@[simp]
theorem ball_zero : ball x 0 = ∅ :=
  by 
    rw [Emetric.ball_eq_empty_iff]

theorem nhds_basis_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (ball x) :=
  nhds_basis_uniformity uniformity_basis_edist

theorem nhds_basis_closed_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (closed_ball x) :=
  nhds_basis_uniformity uniformity_basis_edist_le

theorem nhds_eq : 𝓝 x = ⨅(ε : _)(_ : ε > 0), 𝓟 (ball x ε) :=
  nhds_basis_eball.eq_binfi

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ (ε : _)(_ : ε > 0), ball x ε ⊆ s :=
  nhds_basis_eball.mem_iff

theorem is_open_iff : IsOpen s ↔ ∀ x _ : x ∈ s, ∃ (ε : _)(_ : ε > 0), ball x ε ⊆ s :=
  by 
    simp [is_open_iff_nhds, mem_nhds_iff]

theorem is_open_ball : IsOpen (ball x ε) :=
  is_open_iff.2$ fun y => exists_ball_subset_ball

theorem is_closed_ball_top : IsClosed (ball x ⊤) :=
  is_open_compl_iff.1$
    is_open_iff.2$
      fun y hy =>
        ⟨⊤, Ennreal.coe_lt_top,
          subset_compl_iff_disjoint.2$
            ball_disjoint$
              by 
                rw [Ennreal.top_add]
                exact le_of_not_ltₓ hy⟩

theorem ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
  is_open_ball.mem_nhds (mem_ball_self ε0)

theorem closed_ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : closed_ball x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closed_ball

theorem ball_prod_same [PseudoEmetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) : (ball x r).Prod (ball y r) = ball (x, y) r :=
  ext$ fun z => max_lt_iff.symm

theorem closed_ball_prod_same [PseudoEmetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
  (closed_ball x r).Prod (closed_ball y r) = closed_ball (x, y) r :=
  ext$ fun z => max_le_iff.symm

/-- ε-characterization of the closure in pseudoemetric spaces -/
theorem mem_closure_iff : x ∈ Closure s ↔ ∀ ε _ : ε > 0, ∃ (y : _)(_ : y ∈ s), edist x y < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_eball).trans$
    by 
      simp only [mem_ball, edist_comm x]

theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
  tendsto u f (𝓝 a) ↔ ∀ ε _ : ε > 0, ∀ᶠx in f, edist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff

theorem tendsto_at_top [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
  tendsto u at_top (𝓝 a) ↔ ∀ ε _ : ε > 0, ∃ N, ∀ n _ : n ≥ N, edist (u n) a < ε :=
  (at_top_basis.tendsto_iff nhds_basis_eball).trans$
    by 
      simp only [exists_prop, true_andₓ, mem_Ici, mem_ball]

/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
@[nolint ge_or_gt]
theorem cauchy_seq_iff [Nonempty β] [SemilatticeSup β] {u : β → α} :
  CauchySeq u ↔ ∀ ε _ : ε > 0, ∃ N, ∀ m n _ : m ≥ N _ : n ≥ N, edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchy_seq_iff

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchy_seq_iff' [Nonempty β] [SemilatticeSup β] {u : β → α} :
  CauchySeq u ↔ ∀ ε _ : ε > (0 : ℝ≥0∞), ∃ N, ∀ n _ : n ≥ N, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchy_seq_iff'

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchy_seq_iff_nnreal [Nonempty β] [SemilatticeSup β] {u : β → α} :
  CauchySeq u ↔ ∀ ε :  ℝ≥0 , 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
  uniformity_basis_edist_nnreal.cauchy_seq_iff'

theorem totally_bounded_iff {s : Set α} :
  TotallyBounded s ↔ ∀ ε _ : ε > 0, ∃ t : Set α, finite t ∧ s ⊆ ⋃(y : _)(_ : y ∈ t), ball y ε :=
  ⟨fun H ε ε0 => H _ (edist_mem_uniformity ε0),
    fun H r ru =>
      let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru 
      let ⟨t, ft, h⟩ := H ε ε0
      ⟨t, ft, subset.trans h$ Union_subset_Union$ fun y => Union_subset_Union$ fun yt z => hε⟩⟩

theorem totally_bounded_iff' {s : Set α} :
  TotallyBounded s ↔ ∀ ε _ : ε > 0, ∃ (t : _)(_ : t ⊆ s), finite t ∧ s ⊆ ⋃(y : _)(_ : y ∈ t), ball y ε :=
  ⟨fun H ε ε0 => (totally_bounded_iff_subset.1 H) _ (edist_mem_uniformity ε0),
    fun H r ru =>
      let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru 
      let ⟨t, _, ft, h⟩ := H ε ε0
      ⟨t, ft, subset.trans h$ Union_subset_Union$ fun y => Union_subset_Union$ fun yt z => hε⟩⟩

section Compact

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a countable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that is dense in `s`. -/
theorem subset_countable_closure_of_almost_dense_set
(s : set α)
(hs : ∀
 ε «expr > » 0, «expr∃ , »((t : set α), «expr ∧ »(countable t, «expr ⊆ »(s, «expr⋃ , »((x «expr ∈ » t), closed_ball x ε))))) : «expr∃ , »((t «expr ⊆ » s), «expr ∧ »(countable t, «expr ⊆ »(s, closure t))) :=
begin
  rcases [expr s.eq_empty_or_nonempty, "with", ident rfl, "|", "⟨", ident x₀, ",", ident hx₀, "⟩"],
  { exact [expr ⟨«expr∅»(), empty_subset _, countable_empty, empty_subset _⟩] },
  choose ["!"] [ident T] [ident hTc, ident hsT] ["using", expr λ
   n : exprℕ(), hs «expr ⁻¹»(n) (by simp [] [] [] [] [] [])],
  have [] [":", expr ∀
   r x, «expr∃ , »((y «expr ∈ » s), «expr ⊆ »(«expr ∩ »(closed_ball x r, s), closed_ball y «expr * »(r, 2)))] [],
  { intros [ident r, ident x],
    rcases [expr «expr ∩ »(closed_ball x r, s).eq_empty_or_nonempty, "with", ident he, "|", "⟨", ident y, ",", ident hxy, ",", ident hys, "⟩"],
    { refine [expr ⟨x₀, hx₀, _⟩],
      rw [expr he] [],
      exact [expr empty_subset _] },
    { refine [expr ⟨y, hys, λ z hz, _⟩],
      calc
        «expr ≤ »(edist z y, «expr + »(edist z x, edist y x)) : edist_triangle_right _ _ _
        «expr ≤ »(..., «expr + »(r, r)) : add_le_add hz.1 hxy
        «expr = »(..., «expr * »(r, 2)) : (mul_two r).symm } },
  choose [] [ident f] [ident hfs, ident hf] [],
  refine [expr ⟨«expr⋃ , »((n : exprℕ()), «expr '' »(f «expr ⁻¹»(n), T n)), «expr $ »(Union_subset, λ
     n, image_subset_iff.2 (λ z hz, hfs _ _)), «expr $ »(countable_Union, λ n, (hTc n).image _), _⟩],
  refine [expr λ x hx, mem_closure_iff.2 (λ ε ε0, _)],
  rcases [expr ennreal.exists_inv_nat_lt (ennreal.half_pos ε0.lt.ne').ne', "with", "⟨", ident n, ",", ident hn, "⟩"],
  rcases [expr mem_bUnion_iff.1 (hsT n hx), "with", "⟨", ident y, ",", ident hyn, ",", ident hyx, "⟩"],
  refine [expr ⟨f «expr ⁻¹»(n) y, mem_Union.2 ⟨n, mem_image_of_mem _ hyn⟩, _⟩],
  calc
    «expr ≤ »(edist x (f «expr ⁻¹»(n) y), «expr * »(«expr ⁻¹»(n), 2)) : hf _ _ ⟨hyx, hx⟩
    «expr < »(..., ε) : ennreal.mul_lt_of_lt_div hn
end

/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set.  -/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
  ∃ (t : _)(_ : t ⊆ s), countable t ∧ s ⊆ Closure t :=
  by 
    refine' subset_countable_closure_of_almost_dense_set s fun ε hε => _ 
    rcases totally_bounded_iff'.1 hs.totally_bounded ε hε with ⟨t, hts, htf, hst⟩
    exact ⟨t, htf.countable, subset.trans hst (bUnion_mono$ fun _ _ => ball_subset_closed_ball)⟩

end Compact

section SecondCountable

open _Root_.TopologicalSpace

variable (α)

/-- A sigma compact pseudo emetric space has second countable topology. This is not an instance
to avoid a loop with `sigma_compact_space_of_locally_compact_second_countable`.  -/
theorem second_countable_of_sigma_compact [SigmaCompactSpace α] : second_countable_topology α :=
  by 
    suffices  : separable_space α
    ·
      exact UniformSpace.second_countable_of_separable α 
    choose T hTsub hTc hsubT using fun n => subset_countable_closure_of_compact (is_compact_compact_covering α n)
    refine' ⟨⟨⋃n, T n, countable_Union hTc, fun x => _⟩⟩
    rcases Union_eq_univ_iff.1 (Union_compact_covering α) x with ⟨n, hn⟩
    exact closure_mono (subset_Union _ n) (hsubT _ hn)

variable {α}

theorem second_countable_of_almost_dense_set
  (hs : ∀ ε _ : ε > 0, ∃ t : Set α, countable t ∧ (⋃(x : _)(_ : x ∈ t), closed_ball x ε) = univ) :
  second_countable_topology α :=
  by 
    suffices  : separable_space α
    ·
      exact UniformSpace.second_countable_of_separable α 
    rcases subset_countable_closure_of_almost_dense_set (univ : Set α) fun ε ε0 => _ with ⟨t, -, htc, ht⟩
    ·
      exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩
    ·
      rcases hs ε ε0 with ⟨t, htc, ht⟩
      exact ⟨t, htc, univ_subset_iff.2 ht⟩

end SecondCountable

section Diam

/-- The diameter of a set in a pseudoemetric space, named `emetric.diam` -/
def diam (s : Set α) :=
  ⨆(x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s), edist x y

theorem diam_le_iff {d : ℝ≥0∞} : diam s ≤ d ↔ ∀ x _ : x ∈ s y _ : y ∈ s, edist x y ≤ d :=
  by 
    simp only [diam, supr_le_iff]

theorem diam_image_le_iff {d : ℝ≥0∞} {f : β → α} {s : Set β} :
  diam (f '' s) ≤ d ↔ ∀ x _ : x ∈ s y _ : y ∈ s, edist (f x) (f y) ≤ d :=
  by 
    simp only [diam_le_iff, ball_image_iff]

theorem edist_le_of_diam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : diam s ≤ d) : edist x y ≤ d :=
  diam_le_iff.1 hd x hx y hy

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
theorem edist_le_diam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ diam s :=
  edist_le_of_diam_le hx hy le_rfl

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
theorem diam_le {d : ℝ≥0∞} (h : ∀ x _ : x ∈ s y _ : y ∈ s, edist x y ≤ d) : diam s ≤ d :=
  diam_le_iff.2 h

/-- The diameter of a subsingleton vanishes. -/
theorem diam_subsingleton (hs : s.subsingleton) : diam s = 0 :=
  nonpos_iff_eq_zero.1$ diam_le$ fun x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

/-- The diameter of the empty set vanishes -/
@[simp]
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty

/-- The diameter of a singleton vanishes -/
@[simp]
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton

theorem diam_Union_mem_option {ι : Type _} (o : Option ι) (s : ι → Set α) :
  diam (⋃(i : _)(_ : i ∈ o), s i) = ⨆(i : _)(_ : i ∈ o), diam (s i) :=
  by 
    cases o <;> simp 

theorem diam_insert : diam (insert x s) = max (⨆(y : _)(_ : y ∈ s), edist x y) (diam s) :=
  eq_of_forall_ge_iff$
    fun d =>
      by 
        simp only [diam_le_iff, ball_insert_iff, edist_self, edist_comm x, max_le_iff, supr_le_iff, zero_le, true_andₓ,
          forall_and_distrib, and_selfₓ, ←and_assoc]

theorem diam_pair : diam ({x, y} : Set α) = edist x y :=
  by 
    simp only [supr_singleton, diam_insert, diam_singleton, Ennreal.max_zero_right]

theorem diam_triple : diam ({x, y, z} : Set α) = max (max (edist x y) (edist x z)) (edist y z) :=
  by 
    simp only [diam_insert, supr_insert, supr_singleton, diam_singleton, Ennreal.max_zero_right, Ennreal.sup_eq_max]

/-- The diameter is monotonous with respect to inclusion -/
theorem diam_mono {s t : Set α} (h : s ⊆ t) : diam s ≤ diam t :=
  diam_le$ fun x hx y hy => edist_le_diam_of_mem (h hx) (h hy)

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The diameter of a union is controlled by the diameter of the sets, and the edistance
between two points in the sets. -/
theorem diam_union
{t : set α}
(xs : «expr ∈ »(x, s))
(yt : «expr ∈ »(y, t)) : «expr ≤ »(diam «expr ∪ »(s, t), «expr + »(«expr + »(diam s, edist x y), diam t)) :=
begin
  have [ident A] [":", expr ∀
   a «expr ∈ » s, ∀
   b «expr ∈ » t, «expr ≤ »(edist a b, «expr + »(«expr + »(diam s, edist x y), diam t))] [":=", expr λ a ha b hb, calc
     «expr ≤ »(edist a b, «expr + »(«expr + »(edist a x, edist x y), edist y b)) : edist_triangle4 _ _ _ _
     «expr ≤ »(..., «expr + »(«expr + »(diam s, edist x y), diam t)) : add_le_add (add_le_add (edist_le_diam_of_mem ha xs) (le_refl _)) (edist_le_diam_of_mem yt hb)],
  refine [expr diam_le (λ a ha b hb, _)],
  cases [expr (mem_union _ _ _).1 ha] ["with", ident h'a, ident h'a]; cases [expr (mem_union _ _ _).1 hb] ["with", ident h'b, ident h'b],
  { calc
      «expr ≤ »(edist a b, diam s) : edist_le_diam_of_mem h'a h'b
      «expr ≤ »(..., «expr + »(diam s, «expr + »(edist x y, diam t))) : le_self_add
      «expr = »(..., «expr + »(«expr + »(diam s, edist x y), diam t)) : (add_assoc _ _ _).symm },
  { exact [expr A a h'a b h'b] },
  { have [ident Z] [] [":=", expr A b h'b a h'a],
    rwa ["[", expr edist_comm, "]"] ["at", ident Z] },
  { calc
      «expr ≤ »(edist a b, diam t) : edist_le_diam_of_mem h'a h'b
      «expr ≤ »(..., «expr + »(«expr + »(diam s, edist x y), diam t)) : le_add_self }
end

theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s+diam t :=
  let ⟨x, ⟨xs, xt⟩⟩ := h 
  by 
    simpa using diam_union xs xt

theorem diam_closed_ball {r : ℝ≥0∞} : diam (closed_ball x r) ≤ 2*r :=
  diam_le$
    fun a ha b hb =>
      calc edist a b ≤ edist a x+edist b x := edist_triangle_right _ _ _ 
        _ ≤ r+r := add_le_add ha hb 
        _ = 2*r := (two_mul r).symm
        

theorem diam_ball {r : ℝ≥0∞} : diam (ball x r) ≤ 2*r :=
  le_transₓ (diam_mono ball_subset_closed_ball) diam_closed_ball

theorem diam_pi_le_of_le {π : β → Type _} [Fintype β] [∀ b, PseudoEmetricSpace (π b)] {s : ∀ b : β, Set (π b)}
  {c : ℝ≥0∞} (h : ∀ b, diam (s b) ≤ c) : diam (Set.Pi univ s) ≤ c :=
  by 
    apply diam_le fun x hx y hy => edist_pi_le_iff.mpr _ 
    rw [mem_univ_pi] at hx hy 
    exact fun b => diam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

end Diam

end Emetric

/-- We now define `emetric_space`, extending `pseudo_emetric_space`. -/
class EmetricSpace (α : Type u) extends PseudoEmetricSpace α : Type u where 
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y

variable {γ : Type w} [EmetricSpace γ]

instance (priority := 100) EmetricSpace.toUniformSpace' : UniformSpace γ :=
  PseudoEmetricSpace.toUniformSpace

export EmetricSpace(eq_of_edist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
  Iff.intro eq_of_edist_eq_zero fun this : x = y => this ▸ edist_self _

@[simp]
theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y :=
  Iff.intro (fun h => eq_of_edist_eq_zero h.symm) fun this : x = y => this ▸ (edist_self _).symm

theorem edist_le_zero {x y : γ} : edist x y ≤ 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans edist_eq_zero

@[simp]
theorem edist_pos {x y : γ} : 0 < edist x y ↔ x ≠ y :=
  by 
    simp [←not_leₓ]

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {x y : γ} (h : ∀ ε _ : ε > 0, edist x y ≤ ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense bot_le h)

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniform_embedding_iff'
[emetric_space β]
{f : γ → β} : «expr ↔ »(uniform_embedding f, «expr ∧ »(∀
  ε «expr > » 0, «expr∃ , »((δ «expr > » 0), ∀
   {a
    b : γ}, «expr < »(edist a b, δ) → «expr < »(edist (f a) (f b), ε)), ∀
  δ «expr > » 0, «expr∃ , »((ε «expr > » 0), ∀
   {a b : γ}, «expr < »(edist (f a) (f b), ε) → «expr < »(edist a b, δ)))) :=
begin
  split,
  { assume [binders (h)],
    exact [expr ⟨emetric.uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1, (uniform_embedding_iff.1 h).2.2⟩] },
  { rintros ["⟨", ident h₁, ",", ident h₂, "⟩"],
    refine [expr uniform_embedding_iff.2 ⟨_, emetric.uniform_continuous_iff.2 h₁, h₂⟩],
    assume [binders (x y hxy)],
    have [] [":", expr «expr ≤ »(edist x y, 0)] [],
    { refine [expr le_of_forall_lt' (λ δ δpos, _)],
      rcases [expr h₂ δ δpos, "with", "⟨", ident ε, ",", ident εpos, ",", ident hε, "⟩"],
      have [] [":", expr «expr < »(edist (f x) (f y), ε)] [],
      by simpa [] [] [] ["[", expr hxy, "]"] [] [],
      exact [expr hε this] },
    simpa [] [] [] [] [] ["using", expr this] }
end

/-- An emetric space is separated -/
instance (priority := 100) to_separated : SeparatedSpace γ :=
  separated_def.2$ fun x y h => eq_of_forall_edist_le$ fun ε ε0 => le_of_ltₓ (h _ (edist_mem_uniformity ε0))

/-- If a  `pseudo_emetric_space` is separated, then it is an `emetric_space`. -/
def emetricOfT2PseudoEmetricSpace {α : Type _} [PseudoEmetricSpace α] (h : SeparatedSpace α) : EmetricSpace α :=
  { ‹PseudoEmetricSpace α› with
    eq_of_edist_eq_zero :=
      fun x y hdist =>
        by 
          refine' separated_def.1 h x y fun s hs => _ 
          obtain ⟨ε, hε, H⟩ := mem_uniformity_edist.1 hs 
          exact
            H
              (show edist x y < ε by 
                rwa [hdist]) }

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def EmetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EmetricSpace γ)
  (H : @uniformity _ U = @uniformity _ PseudoEmetricSpace.toUniformSpace) : EmetricSpace γ :=
  { edist := @edist _ m.to_has_edist, edist_self := edist_self, eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _,
    edist_comm := edist_comm, edist_triangle := edist_triangle, toUniformSpace := U,
    uniformity_edist := H.trans (@PseudoEmetricSpace.uniformity_edist γ _) }

/-- The extended metric induced by an injective function taking values in a emetric space. -/
def EmetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EmetricSpace β) : EmetricSpace γ :=
  { edist := fun x y => edist (f x) (f y), edist_self := fun x => edist_self _,
    eq_of_edist_eq_zero := fun x y h => hf (edist_eq_zero.1 h), edist_comm := fun x y => edist_comm _ _,
    edist_triangle := fun x y z => edist_triangle _ _ _, toUniformSpace := UniformSpace.comap f m.to_uniform_space,
    uniformity_edist :=
      by 
        apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ fun x y => edist (f x) (f y)
        refine' fun s => mem_comap.trans _ 
        split  <;> intro H
        ·
          rcases H with ⟨r, ru, rs⟩
          rcases mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩
          refine' ⟨ε, ε0, fun a b h => rs (hε _)⟩
          exact h
        ·
          rcases H with ⟨ε, ε0, hε⟩
          exact ⟨_, edist_mem_uniformity ε0, fun ⟨a, b⟩ => hε⟩ }

/-- Emetric space instance on subsets of emetric spaces -/
instance {α : Type _} {p : α → Prop} [t : EmetricSpace α] : EmetricSpace (Subtype p) :=
  t.induced coeₓ fun x y => Subtype.ext_iff_val.2

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance prod.emetric_space_max [emetric_space β] : emetric_space «expr × »(γ, β) :=
{ eq_of_edist_eq_zero := λ x y h, begin
    cases [expr max_le_iff.1 (le_of_eq h)] ["with", ident h₁, ident h₂],
    have [ident A] [":", expr «expr = »(x.fst, y.fst)] [":=", expr edist_le_zero.1 h₁],
    have [ident B] [":", expr «expr = »(x.snd, y.snd)] [":=", expr edist_le_zero.1 h₂],
    exact [expr prod.ext_iff.2 ⟨A, B⟩]
  end,
  ..prod.pseudo_emetric_space_max }

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_edist : 𝓤 γ = ⨅(ε : _)(_ : ε > 0), 𝓟 { p:γ × γ | edist p.1 p.2 < ε } :=
  PseudoEmetricSpace.uniformity_edist

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/ instance emetric_space_pi [∀ b, emetric_space (π b)] : emetric_space (∀ b, π b) :=
{ eq_of_edist_eq_zero := assume f g eq0, begin
    have [ident eq1] [":", expr «expr ≤ »(sup univ (λ b : β, edist (f b) (g b)), 0)] [":=", expr le_of_eq eq0],
    simp [] [] ["only"] ["[", expr finset.sup_le_iff, "]"] [] ["at", ident eq1],
    exact [expr «expr $ »(funext, assume b, «expr $ »(edist_le_zero.1, «expr $ »(eq1 b, mem_univ b)))]
  end,
  ..pseudo_emetric_space_pi }

end Pi

namespace Emetric

/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
  ∃ (t : _)(_ : t ⊆ s), countable t ∧ s = Closure t :=
  by 
    rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
    exact ⟨t, hts, htc, subset.antisymm hsub (closure_minimal hts hs.is_closed)⟩

section Diam

variable {s : Set γ}

theorem diam_eq_zero_iff : diam s = 0 ↔ s.subsingleton :=
  ⟨fun h x hx y hy => edist_le_zero.1$ h ▸ edist_le_diam_of_mem hx hy, diam_subsingleton⟩

-- error in Topology.MetricSpace.EmetricSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem diam_pos_iff : «expr ↔ »(«expr < »(0, diam s), «expr∃ , »((x «expr ∈ » s) (y «expr ∈ » s), «expr ≠ »(x, y))) :=
begin
  have [] [] [":=", expr not_congr (@diam_eq_zero_iff _ _ s)],
  dunfold [ident set.subsingleton] ["at", ident this],
  push_neg ["at", ident this],
  simpa [] [] ["only"] ["[", expr pos_iff_ne_zero, ",", expr exists_prop, "]"] [] ["using", expr this]
end

end Diam

end Emetric

