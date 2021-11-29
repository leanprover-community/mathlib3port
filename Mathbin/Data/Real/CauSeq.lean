import Mathbin.Algebra.Order.AbsoluteValue 
import Mathbin.Algebra.BigOperators.Order

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.

There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `is_cau_seq`: a predicate that says `f : ℕ → β` is Cauchy.
* `cau_seq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/


open_locale BigOperators

open IsAbsoluteValue

theorem exists_forall_ge_and {α} [LinearOrderₓ α] {P Q : α → Prop} :
  (∃ i, ∀ j _ : j ≥ i, P j) → (∃ i, ∀ j _ : j ≥ i, Q j) → ∃ i, ∀ j _ : j ≥ i, P j ∧ Q j
| ⟨a, h₁⟩, ⟨b, h₂⟩ =>
  let ⟨c, ac, bc⟩ := exists_ge_of_linear a b
  ⟨c, fun j hj => ⟨h₁ _ (le_transₓ ac hj), h₂ _ (le_transₓ bc hj)⟩⟩

section 

variable {α : Type _} [LinearOrderedField α] {β : Type _} [Ringₓ β] (abv : β → α) [IsAbsoluteValue abv]

theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
  ∃ (δ : _)(_ : δ > 0), ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv ((a₁+a₂) - b₁+b₂) < ε :=
  ⟨ε / 2, half_pos ε0,
    fun a₁ a₂ b₁ b₂ h₁ h₂ =>
      by 
        simpa [add_halves, sub_eq_add_neg, add_commₓ, add_left_commₓ, add_assocₓ] using
          lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add h₁ h₂)⟩

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rat_mul_continuous_lemma
{ε K₁ K₂ : α}
(ε0 : «expr < »(0, ε)) : «expr∃ , »((δ «expr > » 0), ∀
 {a₁
  a₂
  b₁
  b₂ : β}, «expr < »(abv a₁, K₁) → «expr < »(abv b₂, K₂) → «expr < »(abv «expr - »(a₁, b₁), δ) → «expr < »(abv «expr - »(a₂, b₂), δ) → «expr < »(abv «expr - »(«expr * »(a₁, a₂), «expr * »(b₁, b₂)), ε)) :=
begin
  have [ident K0] [":", expr «expr < »((0 : α), max 1 (max K₁ K₂))] [":=", expr lt_of_lt_of_le zero_lt_one (le_max_left _ _)],
  have [ident εK] [] [":=", expr div_pos (half_pos ε0) K0],
  refine [expr ⟨_, εK, λ a₁ a₂ b₁ b₂ ha₁ hb₂ h₁ h₂, _⟩],
  replace [ident ha₁] [] [":=", expr lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))],
  replace [ident hb₂] [] [":=", expr lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _))],
  have [] [] [":=", expr add_lt_add (mul_lt_mul' (le_of_lt h₁) hb₂ (abv_nonneg abv _) εK) (mul_lt_mul' (le_of_lt h₂) ha₁ (abv_nonneg abv _) εK)],
  rw ["[", "<-", expr abv_mul abv, ",", expr mul_comm, ",", expr div_mul_cancel _ (ne_of_gt K0), ",", "<-", expr abv_mul abv, ",", expr add_halves, "]"] ["at", ident this],
  simpa [] [] [] ["[", expr mul_add, ",", expr add_mul, ",", expr sub_eq_add_neg, ",", expr add_comm, ",", expr add_left_comm, "]"] [] ["using", expr lt_of_le_of_lt (abv_add abv _ _) this]
end

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rat_inv_continuous_lemma
{β : Type*}
[field β]
(abv : β → α)
[is_absolute_value abv]
{ε K : α}
(ε0 : «expr < »(0, ε))
(K0 : «expr < »(0, K)) : «expr∃ , »((δ «expr > » 0), ∀
 {a
  b : β}, «expr ≤ »(K, abv a) → «expr ≤ »(K, abv b) → «expr < »(abv «expr - »(a, b), δ) → «expr < »(abv «expr - »(«expr ⁻¹»(a), «expr ⁻¹»(b)), ε)) :=
begin
  have [ident KK] [] [":=", expr mul_pos K0 K0],
  have [ident εK] [] [":=", expr mul_pos ε0 KK],
  refine [expr ⟨_, εK, λ a b ha hb h, _⟩],
  have [ident a0] [] [":=", expr lt_of_lt_of_le K0 ha],
  have [ident b0] [] [":=", expr lt_of_lt_of_le K0 hb],
  rw ["[", expr inv_sub_inv ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), ",", expr abv_div abv, ",", expr abv_mul abv, ",", expr mul_comm, ",", expr abv_sub abv, ",", "<-", expr mul_div_cancel ε (ne_of_gt KK), "]"] [],
  exact [expr div_lt_div h (mul_le_mul hb ha (le_of_lt K0) (abv_nonneg abv _)) «expr $ »(le_of_lt, mul_pos ε0 KK) KK]
end

end 

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
def IsCauSeq {α : Type _} [LinearOrderedField α] {β : Type _} [Ringₓ β] (abv : β → α) (f : ℕ → β) : Prop :=
  ∀ ε _ : ε > 0, ∃ i, ∀ j _ : j ≥ i, abv (f j - f i) < ε

namespace IsCauSeq

variable {α : Type _} [LinearOrderedField α] {β : Type _} [Ringₓ β] {abv : β → α} [IsAbsoluteValue abv] {f : ℕ → β}

@[nolint ge_or_gt]
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) : ∃ i, ∀ j k _ : j ≥ i _ : k ≥ i, abv (f j - f k) < ε :=
  by 
    refine' (hf _ (half_pos ε0)).imp fun i hi j k ij ik => _ 
    rw [←add_halves ε]
    refine' lt_of_le_of_ltₓ (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) _)
    rw [abv_sub abv]
    exact hi _ ik

theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) : ∃ i, ∀ j _ : j ≥ i, ∀ k _ : k ≥ j, abv (f k - f j) < ε :=
  let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun j ij k jk => H _ _ (le_transₓ ij jk) ij⟩

end IsCauSeq

/-- `cau_seq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def CauSeq {α : Type _} [LinearOrderedField α] (β : Type _) [Ringₓ β] (abv : β → α) : Type _ :=
  { f : ℕ → β // IsCauSeq abv f }

namespace CauSeq

variable {α : Type _} [LinearOrderedField α]

section Ringₓ

variable {β : Type _} [Ringₓ β] {abv : β → α}

instance : CoeFun (CauSeq β abv) fun _ => ℕ → β :=
  ⟨Subtype.val⟩

@[simp]
theorem mk_to_fun f (hf : IsCauSeq abv f) : @coeFn (CauSeq β abv) _ _ ⟨f, hf⟩ = f :=
  rfl

theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g :=
  Subtype.eq (funext h)

theorem is_cau (f : CauSeq β abv) : IsCauSeq abv f :=
  f.2

theorem cauchy (f : CauSeq β abv) : ∀ {ε}, 0 < ε → ∃ i, ∀ j _ : j ≥ i, abv (f j - f i) < ε :=
  f.2

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def of_eq (f : CauSeq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : CauSeq β abv :=
  ⟨g,
    fun ε =>
      by 
        rw [show g = f from (funext e).symm] <;> exact f.cauchy⟩

variable [IsAbsoluteValue abv]

@[nolint ge_or_gt]
theorem cauchy₂ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ j k _ : j ≥ i _ : k ≥ i, abv (f j - f k) < ε :=
  f.2.cauchy₂

theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ j _ : j ≥ i, ∀ k _ : k ≥ j, abv (f k - f j) < ε :=
  f.2.cauchy₃

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bounded (f : cau_seq β abv) : «expr∃ , »((r), ∀ i, «expr < »(abv (f i), r)) :=
begin
  cases [expr f.cauchy zero_lt_one] ["with", ident i, ident h],
  let [ident R] [] [":=", expr «expr∑ in , »((j), finset.range «expr + »(i, 1), abv (f j))],
  have [] [":", expr ∀ j «expr ≤ » i, «expr ≤ »(abv (f j), R)] [],
  { intros [ident j, ident ij],
    change [expr «expr ≤ »(λ j, abv (f j) j, R)] [] [],
    apply [expr finset.single_le_sum],
    { intros [],
      apply [expr abv_nonneg abv] },
    { rwa ["[", expr finset.mem_range, ",", expr nat.lt_succ_iff, "]"] [] } },
  refine [expr ⟨«expr + »(R, 1), λ j, _⟩],
  cases [expr lt_or_le j i] ["with", ident ij, ident ij],
  { exact [expr lt_of_le_of_lt (this _ (le_of_lt ij)) (lt_add_one _)] },
  { have [] [] [":=", expr lt_of_le_of_lt (abv_add abv _ _) (add_lt_add_of_le_of_lt (this _ (le_refl _)) (h _ ij))],
    rw ["[", expr add_sub, ",", expr add_comm, "]"] ["at", ident this],
    simpa [] [] [] [] [] [] }
end

theorem bounded' (f : CauSeq β abv) (x : α) : ∃ (r : _)(_ : r > x), ∀ i, abv (f i) < r :=
  let ⟨r, h⟩ := f.bounded
  ⟨max r (x+1), lt_of_lt_of_leₓ (lt_add_one _) (le_max_rightₓ _ _), fun i => lt_of_lt_of_leₓ (h i) (le_max_leftₓ _ _)⟩

instance : Add (CauSeq β abv) :=
  ⟨fun f g =>
      ⟨fun i => (f i+g i : β),
        fun ε ε0 =>
          let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0 
          let ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0)
          ⟨i,
            fun j ij =>
              let ⟨H₁, H₂⟩ := H _ (le_reflₓ _)
              Hδ (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp]
theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f+g) i = f i+g i :=
  rfl

variable (abv)

/-- The constant Cauchy sequence. -/
def const (x : β) : CauSeq β abv :=
  ⟨fun i => x,
    fun ε ε0 =>
      ⟨0,
        fun j ij =>
          by 
            simpa [abv_zero abv] using ε0⟩⟩

variable {abv}

local notation "const" => const abv

@[simp]
theorem const_apply (x : β) (i : ℕ) : (const x : ℕ → β) i = x :=
  rfl

theorem const_inj {x y : β} : (const x : CauSeq β abv) = const y ↔ x = y :=
  ⟨fun h => congr_argₓ (fun f : CauSeq β abv => (f : ℕ → β) 0) h, congr_argₓ _⟩

instance : HasZero (CauSeq β abv) :=
  ⟨const 0⟩

instance : HasOne (CauSeq β abv) :=
  ⟨const 1⟩

instance : Inhabited (CauSeq β abv) :=
  ⟨0⟩

@[simp]
theorem zero_apply i : (0 : CauSeq β abv) i = 0 :=
  rfl

@[simp]
theorem one_apply i : (1 : CauSeq β abv) i = 1 :=
  rfl

@[simp]
theorem const_zero : const 0 = 0 :=
  rfl

theorem const_add (x y : β) : const (x+y) = const x+const y :=
  ext$ fun i => rfl

instance : Mul (CauSeq β abv) :=
  ⟨fun f g =>
      ⟨fun i => (f i*g i : β),
        fun ε ε0 =>
          let ⟨F, F0, hF⟩ := f.bounded' 0
          let ⟨G, G0, hG⟩ := g.bounded' 0
          let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0 
          let ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0)
          ⟨i,
            fun j ij =>
              let ⟨H₁, H₂⟩ := H _ (le_reflₓ _)
              Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp]
theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f*g) i = f i*g i :=
  rfl

theorem const_mul (x y : β) : const (x*y) = const x*const y :=
  ext$ fun i => rfl

instance : Neg (CauSeq β abv) :=
  ⟨fun f =>
      of_eq (const (-1)*f) (fun x => -f x)
        fun i =>
          by 
            simp ⟩

@[simp]
theorem neg_apply (f : CauSeq β abv) i : (-f) i = -f i :=
  rfl

theorem const_neg (x : β) : const (-x) = -const x :=
  ext$ fun i => rfl

instance : Sub (CauSeq β abv) :=
  ⟨fun f g =>
      of_eq (f+-g) (fun x => f x - g x)
        fun i =>
          by 
            simp [sub_eq_add_neg]⟩

@[simp]
theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
  rfl

theorem const_sub (x y : β) : const (x - y) = const x - const y :=
  ext$ fun i => rfl

instance : Ringₓ (CauSeq β abv) :=
  by 
    refineStruct
        { neg := Neg.neg, add := ·+·, zero := (0 : CauSeq β abv), mul := ·*·, one := 1, sub := Sub.sub,
          npow := @npowRec (CauSeq β abv) ⟨1⟩ ⟨·*·⟩, nsmul := @nsmulRec (CauSeq β abv) ⟨0⟩ ⟨·+·⟩,
          zsmul := @zsmulRec (CauSeq β abv) ⟨0⟩ ⟨·+·⟩ ⟨Neg.neg⟩ } <;>
      intros  <;>
        try 
            rfl <;>
          apply ext <;> simp [mul_addₓ, mul_assocₓ, add_mulₓ, add_commₓ, add_left_commₓ, sub_eq_add_neg]

instance {β : Type _} [CommRingₓ β] {abv : β → α} [IsAbsoluteValue abv] : CommRingₓ (CauSeq β abv) :=
  { CauSeq.ring with
    mul_comm :=
      by 
        intros  <;> apply ext <;> simp [mul_left_commₓ, mul_commₓ] }

/-- `lim_zero f` holds when `f` approaches 0. -/
def lim_zero {abv : β → α} (f : CauSeq β abv) : Prop :=
  ∀ ε _ : ε > 0, ∃ i, ∀ j _ : j ≥ i, abv (f j) < ε

theorem add_lim_zero {f g : CauSeq β abv} (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f+g)
| ε, ε0 =>
  (exists_forall_ge_and (hf _$ half_pos ε0) (hg _$ half_pos ε0)).imp$
    fun i H j ij =>
      let ⟨H₁, H₂⟩ := H _ ij 
      by 
        simpa [add_halves ε] using lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add H₁ H₂)

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_lim_zero_right (f : cau_seq β abv) {g} (hg : lim_zero g) : lim_zero «expr * »(f, g)
| ε, ε0 := let ⟨F, F0, hF⟩ := f.bounded' 0 in
«expr $ »(«expr $ »(hg _, div_pos ε0 F0).imp, λ
 i
 H
 j
 ij, by have [] [] [":=", expr mul_lt_mul' «expr $ »(le_of_lt, hF j) (H _ ij) (abv_nonneg abv _) F0]; rwa ["[", expr mul_comm F, ",", expr div_mul_cancel _ (ne_of_gt F0), ",", "<-", expr abv_mul abv, "]"] ["at", ident this])

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_lim_zero_left {f} (g : cau_seq β abv) (hg : lim_zero f) : lim_zero «expr * »(f, g)
| ε, ε0 := let ⟨G, G0, hG⟩ := g.bounded' 0 in
«expr $ »(«expr $ »(hg _, div_pos ε0 G0).imp, λ
 i
 H
 j
 ij, by have [] [] [":=", expr mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _)]; rwa ["[", expr div_mul_cancel _ (ne_of_gt G0), ",", "<-", expr abv_mul abv, "]"] ["at", ident this])

theorem neg_lim_zero {f : CauSeq β abv} (hf : lim_zero f) : lim_zero (-f) :=
  by 
    rw [←neg_one_mul] <;> exact mul_lim_zero_right _ hf

theorem sub_lim_zero {f g : CauSeq β abv} (hf : lim_zero f) (hg : lim_zero g) : lim_zero (f - g) :=
  by 
    simpa only [sub_eq_add_neg] using add_lim_zero hf (neg_lim_zero hg)

theorem lim_zero_sub_rev {f g : CauSeq β abv} (hfg : lim_zero (f - g)) : lim_zero (g - f) :=
  by 
    simpa using neg_lim_zero hfg

theorem zero_lim_zero : lim_zero (0 : CauSeq β abv)
| ε, ε0 =>
  ⟨0,
    fun j ij =>
      by 
        simpa [abv_zero abv] using ε0⟩

theorem const_lim_zero {x : β} : lim_zero (const x) ↔ x = 0 :=
  ⟨fun H =>
      (abv_eq_zero abv).1$
        eq_of_le_of_forall_le_of_dense (abv_nonneg abv _)$
          fun ε ε0 =>
            let ⟨i, hi⟩ := H _ ε0 
            le_of_ltₓ$ hi _ (le_reflₓ _),
    fun e => e.symm ▸ zero_lim_zero⟩

instance Equiv : Setoidₓ (CauSeq β abv) :=
  ⟨fun f g => lim_zero (f - g),
    ⟨fun f =>
        by 
          simp [zero_lim_zero],
      fun f g h =>
        by 
          simpa using neg_lim_zero h,
      fun f g h fg gh =>
        by 
          simpa [sub_eq_add_neg, add_assocₓ] using add_lim_zero fg gh⟩⟩

theorem add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) : (f1+g1) ≈ f2+g2 :=
  by 
    change lim_zero ((f1+g1) - _)
    convert add_lim_zero hf hg using 1
    simp only [sub_eq_add_neg, add_assocₓ]
    rw [add_commₓ (-f2)]
    simp only [add_assocₓ]
    congr 2
    simp 

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem neg_equiv_neg {f g : cau_seq β abv} (hf : «expr ≈ »(f, g)) : «expr ≈ »(«expr- »(f), «expr- »(g)) :=
begin
  have [ident hf] [":", expr lim_zero _] [":=", expr neg_lim_zero hf],
  show [expr lim_zero «expr - »(«expr- »(f), «expr- »(g))],
  convert [] [expr hf] ["using", 1],
  simp [] [] [] [] [] []
end

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem equiv_def₃
{f g : cau_seq β abv}
(h : «expr ≈ »(f, g))
{ε : α}
(ε0 : «expr < »(0, ε)) : «expr∃ , »((i), ∀ j «expr ≥ » i, ∀ k «expr ≥ » j, «expr < »(abv «expr - »(f k, g j), ε)) :=
«expr $ »((exists_forall_ge_and «expr $ »(h _, half_pos ε0) «expr $ »(f.cauchy₃, half_pos ε0)).imp, λ
 i H j ij k jk, let ⟨h₁, h₂⟩ := H _ ij in
 by have [] [] [":=", expr lt_of_le_of_lt (abv_add abv «expr - »(f j, g j) _) (add_lt_add h₁ (h₂ _ jk))]; rwa ["[", expr sub_add_sub_cancel', ",", expr add_halves, "]"] ["at", ident this])

theorem lim_zero_congr {f g : CauSeq β abv} (h : f ≈ g) : lim_zero f ↔ lim_zero g :=
  ⟨fun l =>
      by 
        simpa using add_lim_zero (Setoidₓ.symm h) l,
    fun l =>
      by 
        simpa using add_lim_zero h l⟩

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem abv_pos_of_not_lim_zero
{f : cau_seq β abv}
(hf : «expr¬ »(lim_zero f)) : «expr∃ , »((K «expr > » 0), «expr∃ , »((i), ∀ j «expr ≥ » i, «expr ≤ »(K, abv (f j)))) :=
begin
  haveI [] [] [":=", expr classical.prop_decidable],
  by_contra [ident nk],
  refine [expr hf (λ ε ε0, _)],
  simp [] [] [] ["[", expr not_forall, "]"] [] ["at", ident nk],
  cases [expr f.cauchy₃ (half_pos ε0)] ["with", ident i, ident hi],
  rcases [expr nk _ (half_pos ε0) i, "with", "⟨", ident j, ",", ident ij, ",", ident hj, "⟩"],
  refine [expr ⟨j, λ k jk, _⟩],
  have [] [] [":=", expr lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)],
  rwa ["[", expr sub_add_cancel, ",", expr add_halves, "]"] ["at", ident this]
end

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_near
(f : exprℕ() → β)
(g : cau_seq β abv)
(h : ∀ ε «expr > » 0, «expr∃ , »((i), ∀ j «expr ≥ » i, «expr < »(abv «expr - »(f j, g j), ε))) : is_cau_seq abv f
| ε, ε0 := let ⟨i, hi⟩ := exists_forall_ge_and (h _ «expr $ »(half_pos, half_pos ε0)) «expr $ »(g.cauchy₃, half_pos ε0) in
⟨i, λ j ij, begin
   cases [expr hi _ (le_refl _)] ["with", ident h₁, ident h₂],
   rw [expr abv_sub abv] ["at", ident h₁],
   have [] [] [":=", expr lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)],
   have [] [] [":=", expr lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij))],
   rwa ["[", expr add_halves, ",", expr add_halves, ",", expr add_right_comm, ",", expr sub_add_sub_cancel, ",", expr sub_add_sub_cancel, "]"] ["at", ident this]
 end⟩

theorem not_lim_zero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬lim_zero f :=
  fun this : lim_zero f =>
    have  : lim_zero (f - 0) :=
      by 
        simpa 
    hf this

theorem mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : (g*f) ≈ 0 :=
  have  : lim_zero (f - 0) := hf 
  have  : lim_zero (g*f) :=
    mul_lim_zero_right _$
      by 
        simpa 
  show lim_zero ((g*f) - 0)by 
    simpa

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_not_equiv_zero
{f g : cau_seq _ abv}
(hf : «expr¬ »(«expr ≈ »(f, 0)))
(hg : «expr¬ »(«expr ≈ »(g, 0))) : «expr¬ »(«expr ≈ »(«expr * »(f, g), 0)) :=
assume: lim_zero «expr - »(«expr * »(f, g), 0), have hlz : lim_zero «expr * »(f, g), by simpa [] [] [] [] [] [],
have hf' : «expr¬ »(lim_zero f), by simpa [] [] [] [] [] ["using", expr show «expr¬ »(lim_zero «expr - »(f, 0)), from hf],
have hg' : «expr¬ »(lim_zero g), by simpa [] [] [] [] [] ["using", expr show «expr¬ »(lim_zero «expr - »(g, 0)), from hg],
begin
  rcases [expr abv_pos_of_not_lim_zero hf', "with", "⟨", ident a1, ",", ident ha1, ",", ident N1, ",", ident hN1, "⟩"],
  rcases [expr abv_pos_of_not_lim_zero hg', "with", "⟨", ident a2, ",", ident ha2, ",", ident N2, ",", ident hN2, "⟩"],
  have [] [":", expr «expr < »(0, «expr * »(a1, a2))] [],
  from [expr mul_pos ha1 ha2],
  cases [expr hlz _ this] ["with", ident N, ident hN],
  let [ident i] [] [":=", expr max N (max N1 N2)],
  have [ident hN'] [] [":=", expr hN i (le_max_left _ _)],
  have [ident hN1'] [] [":=", expr hN1 i (le_trans (le_max_left _ _) (le_max_right _ _))],
  have [ident hN1'] [] [":=", expr hN2 i (le_trans (le_max_right _ _) (le_max_right _ _))],
  apply [expr not_le_of_lt hN'],
  change [expr «expr ≤ »(_, abv «expr * »(_, _))] [] [],
  rw [expr is_absolute_value.abv_mul abv] [],
  apply [expr mul_le_mul]; try { assumption },
  { apply [expr le_of_lt ha2] },
  { apply [expr is_absolute_value.abv_nonneg abv] }
end

theorem const_equiv {x y : β} : const x ≈ const y ↔ x = y :=
  show lim_zero _ ↔ _ by 
    rw [←const_sub, const_lim_zero, sub_eq_zero]

end Ringₓ

section CommRingₓ

variable {β : Type _} [CommRingₓ β] {abv : β → α} [IsAbsoluteValue abv]

theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : (f*g) ≈ 0 :=
  by 
    rw [mul_commₓ] <;> apply mul_equiv_zero _ hf

end CommRingₓ

section IsDomain

variable {β : Type _} [Ringₓ β] [IsDomain β] (abv : β → α) [IsAbsoluteValue abv]

theorem one_not_equiv_zero : ¬const abv 1 ≈ const abv 0 :=
  fun h =>
    have  : ∀ ε _ : ε > 0, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε := h 
    have h1 : abv 1 ≤ 0 :=
      le_of_not_gtₓ$
        fun h2 : 0 < abv 1 =>
          Exists.elim (this _ h2)$
            fun i hi =>
              lt_irreflₓ (abv 1)$
                by 
                  simpa using hi _ (le_reflₓ _)
    have h2 : 0 ≤ abv 1 := IsAbsoluteValue.abv_nonneg _ _ 
    have  : abv 1 = 0 := le_antisymmₓ h1 h2 
    have  : (1 : β) = 0 := (IsAbsoluteValue.abv_eq_zero abv).1 this 
    absurd this one_ne_zero

end IsDomain

section Field

variable {β : Type _} [Field β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_aux {f : CauSeq β abv} (hf : ¬lim_zero f) : ∀ ε _ : ε > 0, ∃ i, ∀ j _ : j ≥ i, abv (f j⁻¹ - f i⁻¹) < ε
| ε, ε0 =>
  let ⟨K, K0, HK⟩ := abv_pos_of_not_lim_zero hf 
  let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0 
  let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
  ⟨i,
    fun j ij =>
      let ⟨iK, H'⟩ := H _ (le_reflₓ _)
      Hδ (H _ ij).1 iK (H' _ ij)⟩

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : CauSeq β abv) (hf : ¬lim_zero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩

@[simp]
theorem inv_apply {f : CauSeq β abv} hf i : inv f hf i = f i⁻¹ :=
  rfl

theorem inv_mul_cancel {f : CauSeq β abv} hf : (inv f hf*f) ≈ 1 :=
  fun ε ε0 =>
    let ⟨K, K0, i, H⟩ := abv_pos_of_not_lim_zero hf
    ⟨i,
      fun j ij =>
        by 
          simpa [(abv_pos abv).1 (lt_of_lt_of_leₓ K0 (H _ ij)), abv_zero abv] using ε0⟩

theorem const_inv {x : β} (hx : x ≠ 0) :
  const abv (x⁻¹) =
    inv (const abv x)
      (by 
        rwa [const_lim_zero]) :=
  ext
    fun n =>
      by 
        simp [inv_apply, const_apply]

end Field

section Abs

local notation "const" => const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def Pos (f : CauSeq α abs) : Prop :=
  ∃ (K : _)(_ : K > 0), ∃ i, ∀ j _ : j ≥ i, K ≤ f j

theorem not_lim_zero_of_pos {f : CauSeq α abs} : Pos f → ¬lim_zero f
| ⟨F, F0, hF⟩, H =>
  let ⟨i, h⟩ := exists_forall_ge_and hF (H _ F0)
  let ⟨h₁, h₂⟩ := h _ (le_reflₓ _)
  not_lt_of_le h₁ (abs_lt.1 h₂).2

theorem const_pos {x : α} : Pos (const x) ↔ 0 < x :=
  ⟨fun ⟨K, K0, i, h⟩ => lt_of_lt_of_leₓ K0 (h _ (le_reflₓ _)), fun h => ⟨x, h, 0, fun j _ => le_reflₓ _⟩⟩

theorem add_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f+g)
| ⟨F, F0, hF⟩, ⟨G, G0, hG⟩ =>
  let ⟨i, h⟩ := exists_forall_ge_and hF hG
  ⟨_, _root_.add_pos F0 G0, i,
    fun j ij =>
      let ⟨h₁, h₂⟩ := h _ ij 
      add_le_add h₁ h₂⟩

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pos_add_lim_zero {f g : cau_seq α abs} : pos f → lim_zero g → pos «expr + »(f, g)
| ⟨F, F0, hF⟩, H := let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0)) in
⟨_, half_pos F0, i, λ j ij, begin
   cases [expr h j ij] ["with", ident h₁, ident h₂],
   have [] [] [":=", expr add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)],
   rwa ["[", "<-", expr sub_eq_add_neg, ",", expr sub_self_div_two, "]"] ["at", ident this]
 end⟩

protected theorem mul_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f*g)
| ⟨F, F0, hF⟩, ⟨G, G0, hG⟩ =>
  let ⟨i, h⟩ := exists_forall_ge_and hF hG
  ⟨_, _root_.mul_pos F0 G0, i,
    fun j ij =>
      let ⟨h₁, h₂⟩ := h _ ij 
      mul_le_mul h₁ h₂ (le_of_ltₓ G0) (le_transₓ (le_of_ltₓ F0) h₁)⟩

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem trichotomy (f : cau_seq α abs) : «expr ∨ »(pos f, «expr ∨ »(lim_zero f, pos «expr- »(f))) :=
begin
  cases [expr classical.em (lim_zero f)] []; simp [] [] [] ["*"] [] [],
  rcases [expr abv_pos_of_not_lim_zero h, "with", "⟨", ident K, ",", ident K0, ",", ident hK, "⟩"],
  rcases [expr exists_forall_ge_and hK (f.cauchy₃ K0), "with", "⟨", ident i, ",", ident hi, "⟩"],
  refine [expr (le_total 0 (f i)).imp _ _]; refine [expr λ
   h, ⟨K, K0, i, λ
    j ij, _⟩]; have [] [] [":=", expr (hi _ ij).1]; cases [expr hi _ (le_refl _)] ["with", ident h₁, ident h₂],
  { rwa [expr abs_of_nonneg] ["at", ident this],
    rw [expr abs_of_nonneg h] ["at", ident h₁],
    exact [expr (le_add_iff_nonneg_right _).1 «expr $ »(le_trans h₁, «expr $ »(neg_le_sub_iff_le_add'.1, le_of_lt «expr $ »(abs_lt.1, h₂ _ ij).1))] },
  { rwa [expr abs_of_nonpos] ["at", ident this],
    rw [expr abs_of_nonpos h] ["at", ident h₁],
    rw ["[", "<-", expr sub_le_sub_iff_right, ",", expr zero_sub, "]"] [],
    exact [expr le_trans (le_of_lt «expr $ »(abs_lt.1, h₂ _ ij).2) h₁] }
end

instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩

instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩

theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h :=
  show Pos (h - f)by 
    simpa [sub_eq_add_neg, add_commₓ, add_left_commₓ] using pos_add_lim_zero fg (neg_lim_zero gh)

-- error in Data.Real.CauSeq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_of_eq_of_lt {f g h : cau_seq α abs} (fg : «expr ≈ »(f, g)) (gh : «expr < »(g, h)) : «expr < »(f, h) :=
by have [] [] [":=", expr pos_add_lim_zero gh (neg_lim_zero fg)]; rwa ["[", "<-", expr sub_eq_add_neg, ",", expr sub_sub_sub_cancel_right, "]"] ["at", ident this]

theorem lt_transₓ {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h :=
  show Pos (h - f)by 
    simpa [sub_eq_add_neg, add_commₓ, add_left_commₓ] using add_pos fg gh

theorem lt_irreflₓ {f : CauSeq α abs} : ¬f < f
| h =>
  not_lim_zero_of_pos h
    (by 
      simp [zero_lim_zero])

theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
  hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoidₓ.trans hfg)

theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
  hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoidₓ.trans h hgh)

instance : Preorderₓ (CauSeq α abs) :=
  { lt := · < ·, le := fun f g => f < g ∨ f ≈ g, le_refl := fun f => Or.inr (Setoidₓ.refl _),
    le_trans :=
      fun f g h fg =>
        match fg with 
        | Or.inl fg, Or.inl gh => Or.inl$ lt_transₓ fg gh
        | Or.inl fg, Or.inr gh => Or.inl$ lt_of_lt_of_eq fg gh
        | Or.inr fg, Or.inl gh => Or.inl$ lt_of_eq_of_lt fg gh
        | Or.inr fg, Or.inr gh => Or.inr$ Setoidₓ.trans fg gh,
    lt_iff_le_not_le :=
      fun f g =>
        ⟨fun h => ⟨Or.inl h, not_orₓ (mt (lt_transₓ h) lt_irreflₓ) (not_lim_zero_of_pos h)⟩,
          fun ⟨h₁, h₂⟩ => h₁.resolve_right (mt (fun h => Or.inr (Setoidₓ.symm h)) h₂)⟩ }

theorem le_antisymmₓ {f g : CauSeq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
  fg.resolve_left (not_lt_of_le gf)

theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f :=
  (trichotomy (g - f)).imp_right
    fun h =>
      h.imp (fun h => Setoidₓ.symm h)
        fun h =>
          by 
            rwa [neg_sub] at h

theorem le_totalₓ (f g : CauSeq α abs) : f ≤ g ∨ g ≤ f :=
  (Or.assoc.2 (lt_total f g)).imp_right Or.inl

theorem const_lt {x y : α} : const x < const y ↔ x < y :=
  show Pos _ ↔ _ by 
    rw [←const_sub, const_pos, sub_pos]

theorem const_le {x y : α} : const x ≤ const y ↔ x ≤ y :=
  by 
    rw [le_iff_lt_or_eqₓ] <;> exact or_congr const_lt const_equiv

theorem le_of_exists {f g : CauSeq α abs} (h : ∃ i, ∀ j _ : j ≥ i, f j ≤ g j) : f ≤ g :=
  let ⟨i, hi⟩ := h
  (Or.assoc.2 (CauSeq.lt_total f g)).elim id
    fun hgf =>
      False.elim
        (let ⟨K, hK0, j, hKj⟩ := hgf 
        not_lt_of_geₓ (hi (max i j) (le_max_leftₓ _ _)) (sub_pos.1 (lt_of_lt_of_leₓ hK0 (hKj _ (le_max_rightₓ _ _)))))

theorem exists_gt (f : CauSeq α abs) : ∃ a : α, f < const a :=
  let ⟨K, H⟩ := f.bounded
  ⟨K+1, 1, zero_lt_one, 0,
    fun i _ =>
      by 
        rw [sub_apply, const_apply, le_sub_iff_add_le', add_le_add_iff_right]
        exact le_of_ltₓ (abs_lt.1 (H _)).2⟩

theorem exists_lt (f : CauSeq α abs) : ∃ a : α, const a < f :=
  let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a,
    show Pos _ by 
      rwa [const_neg, sub_neg_eq_add, add_commₓ, ←sub_neg_eq_add]⟩

end Abs

end CauSeq

