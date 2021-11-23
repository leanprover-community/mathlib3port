import Mathbin.Algebra.Module.Basic 
import Mathbin.Algebra.Bounds 
import Mathbin.Algebra.Order.Archimedean 
import Mathbin.Algebra.Star.Basic 
import Mathbin.Data.Real.CauSeqCompletion 
import Mathbin.Order.ConditionallyCompleteLattice

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.
-/


open_locale Pointwise

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where of_cauchy :: 
  cauchy : @CauSeq.Completion.Cauchy ℚ _ _ _ abs _

notation "ℝ" => Real

attribute [pp_using_anonymous_constructor] Real

namespace Real

open CauSeq CauSeq.Completion

variable{x y : ℝ}

theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
| ⟨a⟩, ⟨b⟩ =>
  by 
    split  <;> cc

theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equiv_Cauchy : ℝ ≃ CauSeq.Completion.Cauchy :=
  ⟨Real.cauchy, Real.of_cauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩

@[irreducible]
private def zero : ℝ :=
  ⟨0⟩

@[irreducible]
private def one : ℝ :=
  ⟨1⟩

@[irreducible]
private def add : ℝ → ℝ → ℝ
| ⟨a⟩, ⟨b⟩ => ⟨a+b⟩

@[irreducible]
private def neg : ℝ → ℝ
| ⟨a⟩ => ⟨-a⟩

@[irreducible]
private def mul : ℝ → ℝ → ℝ
| ⟨a⟩, ⟨b⟩ => ⟨a*b⟩

instance  : HasZero ℝ :=
  ⟨zero⟩

instance  : HasOne ℝ :=
  ⟨one⟩

instance  : Add ℝ :=
  ⟨add⟩

instance  : Neg ℝ :=
  ⟨neg⟩

instance  : Mul ℝ :=
  ⟨mul⟩

theorem zero_cauchy : (⟨0⟩ : ℝ) = 0 :=
  show _ = zero by 
    rw [zero]

theorem one_cauchy : (⟨1⟩ : ℝ) = 1 :=
  show _ = one by 
    rw [one]

theorem add_cauchy {a b} : (⟨a⟩+⟨b⟩ : ℝ) = ⟨a+b⟩ :=
  show add _ _ = _ by 
    rw [add]

theorem neg_cauchy {a} : (-⟨a⟩ : ℝ) = ⟨-a⟩ :=
  show neg _ = _ by 
    rw [neg]

theorem mul_cauchy {a b} : (⟨a⟩*⟨b⟩ : ℝ) = ⟨a*b⟩ :=
  show mul _ _ = _ by 
    rw [mul]

instance  : CommRingₓ ℝ :=
  by 
    refineStruct
        { zero := (0 : ℝ), one := (1 : ℝ), mul := ·*·, add := ·+·, neg := @Neg.neg ℝ _, sub := fun a b => a+-b,
          npow := @npowRec ℝ ⟨1⟩ ⟨·*·⟩, nsmul := @nsmulRec ℝ ⟨0⟩ ⟨·+·⟩,
          zsmul := @zsmulRec ℝ ⟨0⟩ ⟨·+·⟩ ⟨@Neg.neg ℝ _⟩ } <;>
      repeat' 
          rintro ⟨_⟩ <;>
        try 
            rfl <;>
          simp [←zero_cauchy, ←one_cauchy, add_cauchy, neg_cauchy, mul_cauchy] <;>
            first |
              apply add_assocₓ|
              apply add_commₓ|
              apply mul_assocₓ|
              apply mul_commₓ|
              apply left_distrib|
              apply right_distrib|
              apply sub_eq_add_neg|
              skip

/-! Extra instances to short-circuit type class resolution.

 These short-circuits have an additional property of ensuring that a computable path is found; if
 `field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
 version of them. -/


instance  : Ringₓ ℝ :=
  by 
    infer_instance

instance  : CommSemiringₓ ℝ :=
  by 
    infer_instance

instance  : Semiringₓ ℝ :=
  by 
    infer_instance

instance  : CommMonoidWithZero ℝ :=
  by 
    infer_instance

instance  : MonoidWithZeroₓ ℝ :=
  by 
    infer_instance

instance  : AddCommGroupₓ ℝ :=
  by 
    infer_instance

instance  : AddGroupₓ ℝ :=
  by 
    infer_instance

instance  : AddCommMonoidₓ ℝ :=
  by 
    infer_instance

instance  : AddMonoidₓ ℝ :=
  by 
    infer_instance

instance  : AddLeftCancelSemigroup ℝ :=
  by 
    infer_instance

instance  : AddRightCancelSemigroup ℝ :=
  by 
    infer_instance

instance  : AddCommSemigroupₓ ℝ :=
  by 
    infer_instance

instance  : AddSemigroupₓ ℝ :=
  by 
    infer_instance

instance  : CommMonoidₓ ℝ :=
  by 
    infer_instance

instance  : Monoidₓ ℝ :=
  by 
    infer_instance

instance  : CommSemigroupₓ ℝ :=
  by 
    infer_instance

instance  : Semigroupₓ ℝ :=
  by 
    infer_instance

instance  : Sub ℝ :=
  by 
    infer_instance

instance  : Module ℝ ℝ :=
  by 
    infer_instance

instance  : Inhabited ℝ :=
  ⟨0⟩

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance  : StarRing ℝ :=
  starRingOfComm

/-- Coercion `ℚ` → `ℝ` as a `ring_hom`. Note that this
is `cau_seq.completion.of_rat`, not `rat.cast`. -/
def of_rat : ℚ →+* ℝ :=
  by 
    refineStruct { toFun := of_cauchy ∘ of_rat } <;>
      simp [of_rat_one, of_rat_zero, of_rat_mul, of_rat_add, one_cauchy, zero_cauchy, ←mul_cauchy, ←add_cauchy]

theorem of_rat_apply (x : ℚ) : of_rat x = of_cauchy (CauSeq.Completion.ofRat x) :=
  rfl

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : CauSeq ℚ abs) : ℝ :=
  ⟨CauSeq.Completion.mk x⟩

theorem mk_eq {f g : CauSeq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans mk_eq

@[irreducible]
private def lt : ℝ → ℝ → Prop
| ⟨x⟩, ⟨y⟩ =>
  Quotientₓ.liftOn₂ x y (· < ·)$
    fun f₁ g₁ f₂ g₂ hf hg =>
      propext$
        ⟨fun h => lt_of_eq_of_lt (Setoidₓ.symm hf) (lt_of_lt_of_eq h hg),
          fun h => lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoidₓ.symm hg))⟩

instance  : LT ℝ :=
  ⟨lt⟩

theorem lt_cauchy {f g} : (⟨«expr⟦ ⟧» f⟩ : ℝ) < ⟨«expr⟦ ⟧» g⟩ ↔ f < g :=
  show lt _ _ ↔ _ by 
    rw [lt] <;> rfl

@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy

theorem mk_zero : mk 0 = 0 :=
  by 
    rw [←zero_cauchy] <;> rfl

theorem mk_one : mk 1 = 1 :=
  by 
    rw [←one_cauchy] <;> rfl

theorem mk_add {f g : CauSeq ℚ abs} : mk (f+g) = mk f+mk g :=
  by 
    simp [mk, add_cauchy]

theorem mk_mul {f g : CauSeq ℚ abs} : mk (f*g) = mk f*mk g :=
  by 
    simp [mk, mul_cauchy]

theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f :=
  by 
    simp [mk, neg_cauchy]

@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f :=
  by 
    rw [←mk_zero, mk_lt] <;> exact iff_of_eq (congr_argₓ Pos (sub_zero f))

@[irreducible]
private def le (x y : ℝ) : Prop :=
  x < y ∨ x = y

instance  : LE ℝ :=
  ⟨le⟩

private theorem le_def {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  show le _ _ ↔ _ by 
    rw [le]

@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g :=
  by 
    simp [le_def, mk_eq] <;> rfl

@[elab_as_eliminator]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x :=
  by 
    cases' x with x 
    induction' x using Quot.induction_on with x 
    exact h x

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : ((c+a) < c+b) ↔ a < b :=
  by 
    induction a using Real.ind_mk 
    induction b using Real.ind_mk 
    induction c using Real.ind_mk 
    simp only [mk_lt, ←mk_add]
    show Pos _ ↔ Pos _ 
    rw [add_sub_add_left_eq_sub]

instance  : PartialOrderₓ ℝ :=
  { le := · ≤ ·, lt := · < ·,
    lt_iff_le_not_le :=
      fun a b =>
        Real.ind_mk a$
          fun a =>
            Real.ind_mk b$
              fun b =>
                by 
                  simpa using lt_iff_le_not_leₓ,
    le_refl :=
      fun a =>
        a.ind_mk
          (by 
            intro a <;> rw [mk_le]),
    le_trans :=
      fun a b c =>
        Real.ind_mk a$
          fun a =>
            Real.ind_mk b$
              fun b =>
                Real.ind_mk c$
                  fun c =>
                    by 
                      simpa using le_transₓ,
    lt_iff_le_not_le :=
      fun a b =>
        Real.ind_mk a$
          fun a =>
            Real.ind_mk b$
              fun b =>
                by 
                  simpa using lt_iff_le_not_leₓ,
    le_antisymm :=
      fun a b =>
        Real.ind_mk a$
          fun a =>
            Real.ind_mk b$
              fun b =>
                by 
                  simpa [mk_eq] using @CauSeq.le_antisymm _ _ a b }

instance  : Preorderₓ ℝ :=
  by 
    infer_instance

theorem of_rat_lt {x y : ℚ} : of_rat x < of_rat y ↔ x < y :=
  by 
    rw [mk_lt]
    exact const_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 :=
  by 
    convert of_rat_lt.2 zero_lt_one <;> simp 

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a*b :=
  by 
    induction' a using Real.ind_mk with a 
    induction' b using Real.ind_mk with b 
    simpa only [mk_lt, mk_pos, ←mk_mul] using CauSeq.mul_pos

instance  : OrderedCommRing ℝ :=
  { Real.commRing, Real.partialOrder, Real.semiring with
    add_le_add_left :=
      by 
        simp only [le_iff_eq_or_lt]
        rintro a b ⟨rfl, h⟩
        ·
          simp 
        ·
          exact fun c => Or.inr ((add_lt_add_iff_left c).2 ‹_›),
    zero_le_one := le_of_ltₓ Real.zero_lt_one, mul_pos := @Real.mul_pos }

instance  : OrderedRing ℝ :=
  by 
    infer_instance

instance  : OrderedSemiring ℝ :=
  by 
    infer_instance

instance  : OrderedAddCommGroup ℝ :=
  by 
    infer_instance

instance  : OrderedCancelAddCommMonoid ℝ :=
  by 
    infer_instance

instance  : OrderedAddCommMonoid ℝ :=
  by 
    infer_instance

instance  : Nontrivial ℝ :=
  ⟨⟨0, 1, ne_of_ltₓ Real.zero_lt_one⟩⟩

open_locale Classical

noncomputable instance  : LinearOrderₓ ℝ :=
  { Real.partialOrder with
    le_total :=
      by 
        intro a b 
        induction' a using Real.ind_mk with a 
        induction' b using Real.ind_mk with b 
        simpa using le_totalₓ a b,
    decidableLe :=
      by 
        infer_instance }

noncomputable instance  : LinearOrderedCommRing ℝ :=
  { Real.nontrivial, Real.orderedRing, Real.commRing, Real.linearOrder with  }

noncomputable instance  : LinearOrderedRing ℝ :=
  by 
    infer_instance

noncomputable instance  : LinearOrderedSemiring ℝ :=
  by 
    infer_instance

instance  : IsDomain ℝ :=
  { Real.nontrivial, Real.commRing, LinearOrderedRing.is_domain with  }

/-- The real numbers are an ordered `*`-ring, with the trivial `*`-structure. -/
instance  : StarOrderedRing ℝ :=
  { star_mul_self_nonneg := fun r => mul_self_nonneg r }

@[irreducible]
private noncomputable def inv' : ℝ → ℝ
| ⟨a⟩ => ⟨a⁻¹⟩

noncomputable instance  : HasInv ℝ :=
  ⟨inv'⟩

theorem inv_cauchy {f} : (⟨f⟩ : ℝ)⁻¹ = ⟨f⁻¹⟩ :=
  show inv' _ = _ by 
    rw [inv']

noncomputable instance  : LinearOrderedField ℝ :=
  { Real.linearOrderedCommRing with inv := HasInv.inv,
    mul_inv_cancel :=
      by 
        rintro ⟨a⟩ h 
        rw [mul_commₓ]
        simp only [inv_cauchy, mul_cauchy, ←one_cauchy, ←zero_cauchy, Ne.def] at *
        exact CauSeq.Completion.inv_mul_cancel h,
    inv_zero :=
      by 
        simp [←zero_cauchy, inv_cauchy] }

noncomputable instance  : LinearOrderedAddCommGroup ℝ :=
  by 
    infer_instance

noncomputable instance Field : Field ℝ :=
  by 
    infer_instance

noncomputable instance  : DivisionRing ℝ :=
  by 
    infer_instance

noncomputable instance  : DistribLattice ℝ :=
  by 
    infer_instance

noncomputable instance  : Lattice ℝ :=
  by 
    infer_instance

noncomputable instance  : SemilatticeInf ℝ :=
  by 
    infer_instance

noncomputable instance  : SemilatticeSup ℝ :=
  by 
    infer_instance

noncomputable instance  : HasInf ℝ :=
  by 
    infer_instance

noncomputable instance  : HasSup ℝ :=
  by 
    infer_instance

noncomputable instance decidable_lt (a b : ℝ) : Decidable (a < b) :=
  by 
    infer_instance

noncomputable instance decidable_le (a b : ℝ) : Decidable (a ≤ b) :=
  by 
    infer_instance

noncomputable instance DecidableEq (a b : ℝ) : Decidable (a = b) :=
  by 
    infer_instance

open Rat

@[simp]
theorem of_rat_eq_cast : ∀ x : ℚ, of_rat x = x :=
  of_rat.eq_rat_cast

-- error in Data.Real.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_mk_of_forall_le
{f : cau_seq exprℚ() abs} : «expr∃ , »((i), ∀ j «expr ≥ » i, «expr ≤ »(x, f j)) → «expr ≤ »(x, mk f) :=
begin
  intro [ident h],
  induction [expr x] ["using", ident real.ind_mk] ["with", ident x] [],
  apply [expr le_of_not_lt],
  rw [expr mk_lt] [],
  rintro ["⟨", ident K, ",", ident K0, ",", ident hK, "⟩"],
  obtain ["⟨", ident i, ",", ident H, "⟩", ":=", expr exists_forall_ge_and h (exists_forall_ge_and hK «expr $ »(f.cauchy₃, half_pos K0))],
  apply [expr not_lt_of_le (H _ (le_refl _)).1],
  rw ["<-", expr of_rat_eq_cast] [],
  rw ["[", expr mk_lt, "]"] [] { md := tactic.transparency.semireducible },
  refine [expr ⟨_, half_pos K0, i, λ j ij, _⟩],
  have [] [] [":=", expr add_le_add (H _ ij).2.1 (le_of_lt «expr $ »(abs_lt.1, (H _ (le_refl _)).2.2 _ ij).1)],
  rwa ["[", "<-", expr sub_eq_add_neg, ",", expr sub_self_div_two, ",", expr sub_apply, ",", expr sub_add_sub_cancel, "]"] ["at", ident this]
end

theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀ j _ : j ≥ i, (f j : ℝ) ≤ x) : mk f ≤ x :=
  by 
    cases' h with i H 
    rw [←neg_le_neg_iff, ←mk_neg]
    exact
      le_mk_of_forall_le
        ⟨i,
          fun j ij =>
            by 
              simp [H _ ij]⟩

theorem mk_near_of_forall_near {f : CauSeq ℚ abs} {x : ℝ} {ε : ℝ} (H : ∃ i, ∀ j _ : j ≥ i, |(f j : ℝ) - x| ≤ ε) :
  |mk f - x| ≤ ε :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add'.2$ mk_le_of_forall_le$ H.imp$ fun i h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1$ h j ij).1,
      sub_le.1$ le_mk_of_forall_le$ H.imp$ fun i h j ij => sub_le.1 (abs_sub_le_iff.1$ h j ij).2⟩

instance  : Archimedean ℝ :=
  archimedean_iff_rat_le.2$
    fun x =>
      Real.ind_mk x$
        fun f =>
          let ⟨M, M0, H⟩ := f.bounded' 0
          ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2$ le_of_ltₓ (abs_lt.1 (H i)).2⟩⟩

noncomputable instance  : FloorRing ℝ :=
  Archimedean.floorRing _

theorem is_cau_seq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) :=
  ⟨fun H ε ε0 =>
      let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
      (H _ δ0).imp$
        fun i hi j ij =>
          lt_transₓ
            (by 
              simpa using (@Rat.cast_lt ℝ _ _ _).2 (hi _ ij))
            δε,
    fun H ε ε0 =>
      (H _ (Rat.cast_pos.2 ε0)).imp$
        fun i hi j ij =>
          (@Rat.cast_lt ℝ _ _ _).1$
            by 
              simpa using hi _ ij⟩

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε _ : ε > 0, ∃ i, ∀ j _ : j ≥ i, |(f j : ℝ) - x| < ε) :
  ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨is_cau_seq_iff_lift.2 (of_near _ (const abs x) h),
    sub_eq_zero.1$
      abs_eq_zero.1$
        eq_of_le_of_forall_le_of_dense (abs_nonneg _)$
          fun ε ε0 => mk_near_of_forall_near$ (h _ ε0).imp fun i h j ij => le_of_ltₓ (h j ij)⟩

theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  Int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x
    ⟨n, fun z h' => Int.cast_le.1$ le_transₓ h'$ le_of_ltₓ hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x
    ⟨n, le_of_ltₓ hn⟩)

-- error in Data.Real.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_is_lub (S : set exprℝ()) (hne : S.nonempty) (hbdd : bdd_above S) : «expr∃ , »((x), is_lub S x) :=
begin
  rcases ["⟨", expr hne, ",", expr hbdd, "⟩", "with", "⟨", "⟨", ident L, ",", ident hL, "⟩", ",", "⟨", ident U, ",", ident hU, "⟩", "⟩"],
  have [] [":", expr ∀
   d : exprℕ(), bdd_above {m : exprℤ() | «expr∃ , »((y «expr ∈ » S), «expr ≤ »((m : exprℝ()), «expr * »(y, d)))}] [],
  { cases [expr exists_int_gt U] ["with", ident k, ident hk],
    refine [expr λ d, ⟨«expr * »(k, d), λ z h, _⟩],
    rcases [expr h, "with", "⟨", ident y, ",", ident yS, ",", ident hy, "⟩"],
    refine [expr int.cast_le.1 (hy.trans _)],
    push_cast [] [],
    exact [expr mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg] },
  choose [] [ident f] [ident hf] ["using", expr λ
   d : exprℕ(), int.exists_greatest_of_bdd (this d) ⟨«expr⌊ ⌋»(«expr * »(L, d)), L, hL, int.floor_le _⟩],
  have [ident hf₁] [":", expr ∀
   n «expr > » 0, «expr∃ , »((y «expr ∈ » S), «expr ≤ »(((«expr / »(f n, n) : exprℚ()) : exprℝ()), y))] [":=", expr λ
   n n0, let ⟨y, yS, hy⟩ := (hf n).1 in
   ⟨y, yS, by simpa [] [] [] [] [] ["using", expr (div_le_iff (nat.cast_pos.2 n0 : «expr < »((_ : exprℝ()), _))).2 hy]⟩],
  have [ident hf₂] [":", expr ∀
   (n «expr > » 0)
   (y «expr ∈ » S), «expr < »((«expr - »(y, «expr ⁻¹»((n : exprℕ()))) : exprℝ()), («expr / »(f n, n) : exprℚ()))] [],
  { intros [ident n, ident n0, ident y, ident yS],
    have [] [] [":=", expr (int.sub_one_lt_floor _).trans_le «expr $ »(int.cast_le.2, (hf n).2 _ ⟨y, yS, int.floor_le _⟩)],
    simp [] [] [] ["[", "-", ident sub_eq_add_neg, "]"] [] [],
    rwa ["[", expr lt_div_iff (nat.cast_pos.2 n0 : «expr < »((_ : exprℝ()), _)), ",", expr sub_mul, ",", expr _root_.inv_mul_cancel, "]"] [],
    exact [expr ne_of_gt (nat.cast_pos.2 n0)] },
  have [ident hg] [":", expr is_cau_seq abs (λ n, «expr / »(f n, n) : exprℕ() → exprℚ())] [],
  { intros [ident ε, ident ε0],
    suffices [] [":", expr ∀
     j k «expr ≥ » «expr⌈ ⌉₊»(«expr ⁻¹»(ε)), «expr < »((«expr - »(«expr / »(f j, j), «expr / »(f k, k)) : exprℚ()), ε)],
    { refine [expr ⟨_, λ j ij, abs_lt.2 ⟨_, this _ _ ij (le_refl _)⟩⟩],
      rw ["[", expr neg_lt, ",", expr neg_sub, "]"] [],
      exact [expr this _ _ (le_refl _) ij] },
    intros [ident j, ident k, ident ij, ident ik],
    replace [ident ij] [] [":=", expr le_trans (nat.le_ceil _) (nat.cast_le.2 ij)],
    replace [ident ik] [] [":=", expr le_trans (nat.le_ceil _) (nat.cast_le.2 ik)],
    have [ident j0] [] [":=", expr nat.cast_pos.1 (lt_of_lt_of_le (inv_pos.2 ε0) ij)],
    have [ident k0] [] [":=", expr nat.cast_pos.1 (lt_of_lt_of_le (inv_pos.2 ε0) ik)],
    rcases [expr hf₁ _ j0, "with", "⟨", ident y, ",", ident yS, ",", ident hy, "⟩"],
    refine [expr lt_of_lt_of_le ((@rat.cast_lt exprℝ() _ _ _).1 _) ((inv_le ε0 (nat.cast_pos.2 k0)).1 ik)],
    simpa [] [] [] [] [] ["using", expr sub_lt_iff_lt_add'.2 «expr $ »(lt_of_le_of_lt hy, «expr $ »(sub_lt_iff_lt_add.1, hf₂ _ k0 _ yS))] },
  let [ident g] [":", expr cau_seq exprℚ() abs] [":=", expr ⟨λ n, «expr / »(f n, n), hg⟩],
  refine [expr ⟨mk g, ⟨λ x xS, _, λ y h, _⟩⟩],
  { refine [expr le_of_forall_ge_of_dense (λ z xz, _)],
    cases [expr exists_nat_gt «expr ⁻¹»(«expr - »(x, z))] ["with", ident K, ident hK],
    refine [expr le_mk_of_forall_le ⟨K, λ n nK, _⟩],
    replace [ident xz] [] [":=", expr sub_pos.2 xz],
    replace [ident hK] [] [":=", expr le_trans (le_of_lt hK) (nat.cast_le.2 nK)],
    have [ident n0] [":", expr «expr < »(0, n)] [":=", expr nat.cast_pos.1 (lt_of_lt_of_le (inv_pos.2 xz) hK)],
    refine [expr le_trans _ «expr $ »(le_of_lt, hf₂ _ n0 _ xS)],
    rwa ["[", expr le_sub, ",", expr inv_le (nat.cast_pos.2 n0 : «expr < »((_ : exprℝ()), _)) xz, "]"] [] },
  { exact [expr mk_le_of_forall_le ⟨1, λ n n1, let ⟨x, xS, hx⟩ := hf₁ _ n1 in le_trans hx (h xS)⟩] }
end

noncomputable instance  : HasSupₓ ℝ :=
  ⟨fun S => if h : S.nonempty ∧ BddAbove S then Classical.some (exists_is_lub S h.1 h.2) else 0⟩

theorem Sup_def (S : Set ℝ) :
  Sup S = if h : S.nonempty ∧ BddAbove S then Classical.some (exists_is_lub S h.1 h.2) else 0 :=
  rfl

protected theorem is_lub_Sup (S : Set ℝ) (h₁ : S.nonempty) (h₂ : BddAbove S) : IsLub S (Sup S) :=
  by 
    simp only [Sup_def, dif_pos (And.intro h₁ h₂)]
    apply Classical.some_spec

noncomputable instance  : HasInfₓ ℝ :=
  ⟨fun S => -Sup (-S)⟩

theorem Inf_def (S : Set ℝ) : Inf S = -Sup (-S) :=
  rfl

protected theorem is_glb_Inf (S : Set ℝ) (h₁ : S.nonempty) (h₂ : BddBelow S) : IsGlb S (Inf S) :=
  by 
    rw [Inf_def, ←is_lub_neg', neg_negₓ]
    exact Real.is_lub_Sup _ h₁.neg h₂.neg

noncomputable instance  : ConditionallyCompleteLinearOrder ℝ :=
  { Real.linearOrder, Real.lattice with sup := HasSupₓ.sup, inf := HasInfₓ.inf,
    le_cSup := fun s a hs ha => (Real.is_lub_Sup s ⟨a, ha⟩ hs).1 ha,
    cSup_le := fun s a hs ha => (Real.is_lub_Sup s hs ⟨a, ha⟩).2 ha,
    cInf_le := fun s a hs ha => (Real.is_glb_Inf s ⟨a, ha⟩ hs).1 ha,
    le_cInf := fun s a hs ha => (Real.is_glb_Inf s hs ⟨a, ha⟩).2 ha }

theorem lt_Inf_add_pos {s : Set ℝ} (h : s.nonempty) {ε : ℝ} (hε : 0 < ε) : ∃ (a : _)(_ : a ∈ s), a < Inf s+ε :=
  exists_lt_of_cInf_lt h$ lt_add_of_pos_right _ hε

theorem add_neg_lt_Sup {s : Set ℝ} (h : s.nonempty) {ε : ℝ} (hε : ε < 0) : ∃ (a : _)(_ : a ∈ s), (Sup s+ε) < a :=
  exists_lt_of_lt_cSup h$ add_lt_iff_neg_left.2 hε

theorem Inf_le_iff {s : Set ℝ} (h : BddBelow s) (h' : s.nonempty) {a : ℝ} :
  Inf s ≤ a ↔ ∀ ε, 0 < ε → ∃ (x : _)(_ : x ∈ s), x < a+ε :=
  by 
    rw [le_iff_forall_pos_lt_add]
    split  <;> intro H ε ε_pos
    ·
      exact exists_lt_of_cInf_lt h' (H ε ε_pos)
    ·
      rcases H ε ε_pos with ⟨x, x_in, hx⟩
      exact cInf_lt_of_lt h x_in hx

theorem le_Sup_iff {s : Set ℝ} (h : BddAbove s) (h' : s.nonempty) {a : ℝ} :
  a ≤ Sup s ↔ ∀ ε, ε < 0 → ∃ (x : _)(_ : x ∈ s), (a+ε) < x :=
  by 
    rw [le_iff_forall_pos_lt_add]
    refine' ⟨fun H ε ε_neg => _, fun H ε ε_pos => _⟩
    ·
      exact exists_lt_of_lt_cSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
    ·
      rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
      exact sub_lt_iff_lt_add.mp (lt_cSup_of_lt h x_in hx)

@[simp]
theorem Sup_empty : Sup (∅ : Set ℝ) = 0 :=
  dif_neg$
    by 
      simp 

theorem Sup_of_not_bdd_above {s : Set ℝ} (hs : ¬BddAbove s) : Sup s = 0 :=
  dif_neg$ fun h => hs h.2

theorem Sup_univ : Sup (@Set.Univ ℝ) = 0 :=
  Real.Sup_of_not_bdd_above$ fun ⟨x, h⟩ => not_le_of_lt (lt_add_one _)$ h (Set.mem_univ _)

@[simp]
theorem Inf_empty : Inf (∅ : Set ℝ) = 0 :=
  by 
    simp [Inf_def, Sup_empty]

theorem Inf_of_not_bdd_below {s : Set ℝ} (hs : ¬BddBelow s) : Inf s = 0 :=
  neg_eq_zero.2$ Sup_of_not_bdd_above$ mt bdd_above_neg.1 hs

/--
As `0` is the default value for `real.Sup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem Sup_nonneg (S : Set ℝ) (hS : ∀ x _ : x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ Sup S :=
  by 
    rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    ·
      exact Sup_empty.ge
    ·
      apply dite _ (fun h => le_cSup_of_le h hy$ hS y hy) fun h => (Sup_of_not_bdd_above h).Ge

/--
As `0` is the default value for `real.Sup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `Sup S ≤ 0`.
-/
theorem Sup_nonpos (S : Set ℝ) (hS : ∀ x _ : x ∈ S, x ≤ (0 : ℝ)) : Sup S ≤ 0 :=
  by 
    rcases S.eq_empty_or_nonempty with (rfl | hS₂)
    exacts[Sup_empty.le, cSup_le hS₂ hS]

/--
As `0` is the default value for `real.Inf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem Inf_nonneg (S : Set ℝ) (hS : ∀ x _ : x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ Inf S :=
  by 
    rcases S.eq_empty_or_nonempty with (rfl | hS₂)
    exacts[Inf_empty.ge, le_cInf hS₂ hS]

/--
As `0` is the default value for `real.Inf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `Inf S ≤ 0`.
-/
theorem Inf_nonpos (S : Set ℝ) (hS : ∀ x _ : x ∈ S, x ≤ (0 : ℝ)) : Inf S ≤ 0 :=
  by 
    rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    ·
      exact Inf_empty.le
    ·
      apply dite _ (fun h => cInf_le_of_le h hy$ hS y hy) fun h => (Inf_of_not_bdd_below h).le

theorem Inf_le_Sup (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : Inf s ≤ Sup s :=
  by 
    rcases s.eq_empty_or_nonempty with (rfl | hne)
    ·
      rw [Inf_empty, Sup_empty]
    ·
      exact cInf_le_cSup h₁ h₂ hne

-- error in Data.Real.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cau_seq_converges (f : cau_seq exprℝ() abs) : «expr∃ , »((x), «expr ≈ »(f, const abs x)) :=
begin
  let [ident S] [] [":=", expr {x : exprℝ() | «expr < »(const abs x, f)}],
  have [ident lb] [":", expr «expr∃ , »((x), «expr ∈ »(x, S))] [":=", expr exists_lt f],
  have [ident ub'] [":", expr ∀
   x, «expr < »(f, const abs x) → ∀
   y «expr ∈ » S, «expr ≤ »(y, x)] [":=", expr λ
   x h y yS, «expr $ »(le_of_lt, «expr $ »(const_lt.1, cau_seq.lt_trans yS h))],
  have [ident ub] [":", expr «expr∃ , »((x), ∀ y «expr ∈ » S, «expr ≤ »(y, x))] [":=", expr (exists_gt f).imp ub'],
  refine [expr ⟨Sup S, ((lt_total _ _).resolve_left (λ h, _)).resolve_right (λ h, _)⟩],
  { rcases [expr h, "with", "⟨", ident ε, ",", ident ε0, ",", ident i, ",", ident ih, "⟩"],
    refine [expr (cSup_le lb (ub' _ _)).not_lt (sub_lt_self _ (half_pos ε0))],
    refine [expr ⟨_, half_pos ε0, i, λ j ij, _⟩],
    rw ["[", expr sub_apply, ",", expr const_apply, ",", expr sub_right_comm, ",", expr le_sub_iff_add_le, ",", expr add_halves, "]"] [],
    exact [expr ih _ ij] },
  { rcases [expr h, "with", "⟨", ident ε, ",", ident ε0, ",", ident i, ",", ident ih, "⟩"],
    refine [expr (le_cSup ub _).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0))],
    refine [expr ⟨_, half_pos ε0, i, λ j ij, _⟩],
    rw ["[", expr sub_apply, ",", expr const_apply, ",", expr add_comm, ",", "<-", expr sub_sub, ",", expr le_sub_iff_add_le, ",", expr add_halves, "]"] [],
    exact [expr ih _ ij] }
end

noncomputable instance  : CauSeq.IsComplete ℝ abs :=
  ⟨cau_seq_converges⟩

end Real

