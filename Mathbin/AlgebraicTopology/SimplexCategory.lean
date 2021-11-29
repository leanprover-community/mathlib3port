import Mathbin.CategoryTheory.Skeletal 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Data.Fintype.Sort 
import Mathbin.Order.Category.NonemptyFinLinOrd

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `fin (n+1)` to `fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `simplex_category` and `simplex_category.hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `simplex_category.mk` creates an object of `simplex_category` out of a natural number.
  Use the notation `[n]` in the `simplicial` locale.
2. `simplex_category.len` gives the "length" of an object of `simplex_category`, as a natural.
3. `simplex_category.hom.mk` makes a morphism out of a monotone map between `fin`'s.
4. `simplex_category.hom.to_preorder_hom` gives the underlying monotone map associated to a
  term of `simplex_category.hom`.

-/


universe u v

open CategoryTheory

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `fin (n+1) → fin (m+1)`
-/ @[derive #[expr inhabited], irreducible] def simplex_category :=
ulift.{u} exprℕ()

namespace SimplexCategory

section 

attribute [local semireducible] SimplexCategory

/-- Interpet a natural number as an object of the simplex category. -/
def mk (n : ℕ) : SimplexCategory.{u} :=
  Ulift.up n

localized [Simplicial] notation "[" n "]" => SimplexCategory.mk n

/-- The length of an object of `simplex_category`. -/
def len (n : SimplexCategory.{u}) : ℕ :=
  n.down

@[ext]
theorem ext (a b : SimplexCategory.{u}) : a.len = b.len → a = b :=
  Ulift.ext a b

@[simp]
theorem len_mk (n : ℕ) : [n].len = n :=
  rfl

@[simp]
theorem mk_len (n : SimplexCategory.{u}) : [n.len] = n :=
  by 
    cases n 
    rfl

/-- Morphisms in the simplex_category. -/
@[irreducible, nolint has_inhabited_instance]
protected def hom (a b : SimplexCategory.{u}) : Type u :=
  Ulift (Finₓ (a.len+1) →ₘ Finₓ (b.len+1))

namespace Hom

attribute [local semireducible] SimplexCategory.Hom

/-- Make a moprhism in `simplex_category` from a monotone map of fin's. -/
def mk {a b : SimplexCategory.{u}} (f : Finₓ (a.len+1) →ₘ Finₓ (b.len+1)) : SimplexCategory.Hom a b :=
  Ulift.up f

/-- Recover the monotone map from a morphism in the simplex category. -/
def to_preorder_hom {a b : SimplexCategory.{u}} (f : SimplexCategory.Hom a b) : Finₓ (a.len+1) →ₘ Finₓ (b.len+1) :=
  Ulift.down f

@[ext]
theorem ext {a b : SimplexCategory.{u}} (f g : SimplexCategory.Hom a b) :
  f.to_preorder_hom = g.to_preorder_hom → f = g :=
  Ulift.ext _ _

@[simp]
theorem mk_to_preorder_hom {a b : SimplexCategory.{u}} (f : SimplexCategory.Hom a b) : mk f.to_preorder_hom = f :=
  by 
    cases f 
    rfl

@[simp]
theorem to_preorder_hom_mk {a b : SimplexCategory.{u}} (f : Finₓ (a.len+1) →ₘ Finₓ (b.len+1)) :
  (mk f).toPreorderHom = f :=
  by 
    simp [to_preorder_hom, mk]

theorem mk_to_preorder_hom_apply {a b : SimplexCategory.{u}} (f : Finₓ (a.len+1) →ₘ Finₓ (b.len+1))
  (i : Finₓ (a.len+1)) : (mk f).toPreorderHom i = f i :=
  rfl

/-- Identity morphisms of `simplex_category`. -/
@[simp]
def id (a : SimplexCategory.{u}) : SimplexCategory.Hom a a :=
  mk PreorderHom.id

/-- Composition of morphisms of `simplex_category`. -/
@[simp]
def comp {a b c : SimplexCategory.{u}} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
  SimplexCategory.Hom a c :=
  mk$ f.to_preorder_hom.comp g.to_preorder_hom

end Hom

@[simps]
instance small_category : small_category.{u} SimplexCategory :=
  { Hom := fun n m => SimplexCategory.Hom n m, id := fun m => SimplexCategory.Hom.id _,
    comp := fun _ _ _ f g => SimplexCategory.Hom.comp g f }

/-- The constant morphism from [0]. -/
def const (x : SimplexCategory.{u}) (i : Finₓ (x.len+1)) : [0] ⟶ x :=
  hom.mk$
    ⟨fun _ => i,
      by 
        tauto⟩

@[simp]
theorem const_comp (x y : SimplexCategory.{u}) (i : Finₓ (x.len+1)) (f : x ⟶ y) :
  const x i ≫ f = const y (f.to_preorder_hom i) :=
  rfl

/--
Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms beetween `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mk_hom {n m : ℕ} (f : Finₓ (n+1) →ₘ Finₓ (m+1)) : [n] ⟶ [m] :=
  SimplexCategory.Hom.mk f

theorem hom_zero_zero (f : [0] ⟶ [0]) : f = 𝟙 _ :=
  by 
    ext : 2
    dsimp 
    apply Subsingleton.elimₓ

end 

open_locale Simplicial

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/


/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : Finₓ (n+2)) : [n] ⟶ [n+1] :=
  mk_hom (Finₓ.succAbove i).toPreorderHom

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : Finₓ (n+1)) : [n+1] ⟶ [n] :=
  mk_hom { toFun := Finₓ.predAbove i, monotone' := Finₓ.pred_above_right_monotone i }

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Finₓ (n+2)} (H : i ≤ j) : δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
  by 
    ext k 
    dsimp [δ, Finₓ.succAbove]
    simp only [OrderEmbedding.to_preorder_hom_coe, OrderEmbedding.coe_of_strict_mono, Function.comp_app,
      SimplexCategory.Hom.to_preorder_hom_mk, PreorderHom.comp_coe]
    rcases i with ⟨i, _⟩
    rcases j with ⟨j, _⟩
    rcases k with ⟨k, _⟩
    splitIfs <;>
      ·
        simp  at * <;> linarith

/-- The special case of the first simplicial identity -/
theorem δ_comp_δ_self {n} {i : Finₓ (n+2)} : δ i ≫ δ i.cast_succ = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_reflₓ i)).symm

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The second simplicial identity -/
theorem δ_comp_σ_of_le
{n}
{i : fin «expr + »(n, 2)}
{j : fin «expr + »(n, 1)}
(H : «expr ≤ »(i, j.cast_succ)) : «expr = »(«expr ≫ »(δ i.cast_succ, σ j.succ), «expr ≫ »(σ j, δ i)) :=
begin
  ext [] [ident k] [],
  suffices [] [":", expr «expr = »(ite «expr < »(j.succ.cast_succ, ite «expr < »(k, i) k.cast_succ k.succ) «expr - »(ite «expr < »(k, i) (k : exprℕ()) «expr + »(k, 1), 1) (ite «expr < »(k, i) k «expr + »(k, 1)), ite «expr < »((if h : «expr < »((j : exprℕ()), k) then k.pred (by { rintro [ident rfl],
         exact [expr nat.not_lt_zero _ h] }) else k.cast_lt (by { cases [expr j] [],
         cases [expr k] [],
         simp [] [] ["only"] ["[", expr len_mk, "]"] [] [],
         linarith [] [] [] })).cast_succ, i) (ite «expr < »(j.cast_succ, k) «expr - »(k, 1) k) «expr + »(ite «expr < »(j.cast_succ, k) «expr - »(k, 1) k, 1))],
  { dsimp [] ["[", expr δ, ",", expr σ, ",", expr fin.succ_above, ",", expr fin.pred_above, "]"] [] [],
    simpa [] [] [] ["[", expr fin.pred_above, "]"] ["with", ident push_cast] [] },
  rcases [expr i, "with", "⟨", ident i, ",", "_", "⟩"],
  rcases [expr j, "with", "⟨", ident j, ",", "_", "⟩"],
  rcases [expr k, "with", "⟨", ident k, ",", "_", "⟩"],
  simp [] [] ["only"] ["[", expr subtype.mk_le_mk, ",", expr fin.cast_succ_mk, "]"] [] ["at", ident H],
  dsimp [] [] [] [],
  simp [] [] ["only"] ["[", expr if_congr, ",", expr subtype.mk_lt_mk, ",", expr dif_ctx_congr, "]"] [] [],
  split_ifs [] [],
  swap 8,
  { exact [expr (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) «expr‹ ›»(_))).symm] },
  swap 7,
  { have [] [":", expr «expr ≤ »(k, i)] [":=", expr nat.le_of_pred_lt «expr‹ ›»(_)],
    linarith [] [] [] },
  all_goals { try { refl <|> simp [] [] [] [] [] ["at", "*"] }; linarith [] [] [] }
end

/-- The first part of the third simplicial identity -/
theorem δ_comp_σ_self {n} {i : Finₓ (n+1)} : δ i.cast_succ ≫ σ i = 𝟙 [n] :=
  by 
    ext j 
    suffices  :
      ite (Finₓ.castSucc i < ite (j < i) (Finₓ.castSucc j) j.succ) (ite (j < i) (j : ℕ) (j+1) - 1)
          (ite (j < i) j (j+1)) =
        j
    ·
      dsimp [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
      simpa [Finₓ.predAbove] with push_cast 
    rcases i with ⟨i, _⟩
    rcases j with ⟨j, _⟩
    dsimp 
    simp only [if_congr, Subtype.mk_lt_mk]
    splitIfs <;>
      ·
        simp  at * <;> linarith

/-- The second part of the third simplicial identity -/
theorem δ_comp_σ_succ {n} {i : Finₓ (n+1)} : δ i.succ ≫ σ i = 𝟙 [n] :=
  by 
    ext j 
    rcases i with ⟨i, _⟩
    rcases j with ⟨j, _⟩
    dsimp [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
    simp' [Finₓ.predAbove] with push_cast 
    splitIfs <;>
      ·
        simp  at * <;> linarith

/-- The fourth simplicial identity -/
theorem δ_comp_σ_of_gt {n} {i : Finₓ (n+2)} {j : Finₓ (n+1)} (H : j.cast_succ < i) :
  δ i.succ ≫ σ j.cast_succ = σ j ≫ δ i :=
  by 
    ext k 
    dsimp [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
    rcases i with ⟨i, _⟩
    rcases j with ⟨j, _⟩
    rcases k with ⟨k, _⟩
    simp only [Subtype.mk_lt_mk, Finₓ.cast_succ_mk] at H 
    suffices  : ite (_ < ite (k < i+1) _ _) _ _ = ite _ (ite (j < k) (k - 1) k) (ite (j < k) (k - 1) k+1)
    ·
      simpa [apply_dite Finₓ.castSucc, Finₓ.predAbove] with push_cast 
    splitIfs 
    swap 2
    ·
      simp only [Subtype.mk_lt_mk] at h_1 
      simp only [not_ltₓ] at h_2 
      simp only [self_eq_add_rightₓ, one_ne_zero]
      exact
        lt_irreflₓ (k - 1)
          (lt_of_lt_of_leₓ (Nat.pred_ltₓ (ne_of_ltₓ (lt_of_le_of_ltₓ (zero_le _) h_1)).symm)
            (le_transₓ (Nat.le_of_lt_succₓ h) h_2))
    swap 4
    ·
      simp only [Subtype.mk_lt_mk] at h_1 
      simp only [not_ltₓ] at h 
      simp only [Nat.add_succ_sub_one, add_zeroₓ]
      exfalso 
      exact lt_irreflₓ _ (lt_of_le_of_ltₓ (Nat.le_pred_of_lt (Nat.lt_of_succ_leₓ h)) h_3)
    swap 4
    ·
      simp only [Subtype.mk_lt_mk] at h_1 
      simp only [not_ltₓ] at h_3 
      simp only [Nat.add_succ_sub_one, add_zeroₓ]
      exact (Nat.succ_pred_eq_of_posₓ (lt_of_le_of_ltₓ (zero_le _) h_2)).symm 
    all_goals 
      simp  at h_1 h_2⊢ <;> linarith

attribute [local simp] Finₓ.pred_mk

/-- The fifth simplicial identity -/
theorem σ_comp_σ {n} {i j : Finₓ (n+1)} (H : i ≤ j) : σ i.cast_succ ≫ σ j = σ j.succ ≫ σ i :=
  by 
    ext k 
    dsimp [σ, Finₓ.predAbove]
    rcases i with ⟨i, _⟩
    rcases j with ⟨j, _⟩
    rcases k with ⟨k, _⟩
    simp only [Subtype.mk_le_mk] at H 
    suffices  : ite (_ < dite (i < k) _ _) _ _ = ite (_ < dite ((j+1) < k) _ _) _ _
    ·
      simpa [Finₓ.predAbove] with push_cast 
    splitIfs 
    swap 3
    ·
      simp only [not_ltₓ] at h_2 
      exact
        False.elim
          (lt_irreflₓ (k - 1)
            (lt_of_lt_of_leₓ (Nat.pred_ltₓ (id (ne_of_ltₓ (lt_of_le_of_ltₓ (zero_le i) h)).symm))
              (le_transₓ h_2 (Nat.succ_le_of_ltₓ h_1))))
    swap 3
    ·
      simp only [Subtype.mk_lt_mk, not_ltₓ] at h_1 
      exact False.elim (lt_irreflₓ j (lt_of_lt_of_leₓ (Nat.pred_lt_predₓ (Nat.succ_ne_zero j) h_2) h_1))
    all_goals 
      simp  at * <;> linarith

end Generators

section Skeleton

/-- The functor that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletal_functor : SimplexCategory.{u} ⥤ NonemptyFinLinOrdₓ.{v} :=
  { obj := fun a => NonemptyFinLinOrdₓ.of$ Ulift (Finₓ (a.len+1)),
    map := fun a b f => ⟨fun i => Ulift.up (f.to_preorder_hom i.down), fun i j h => f.to_preorder_hom.monotone h⟩,
    map_id' :=
      fun a =>
        by 
          ext 
          simp ,
    map_comp' :=
      fun a b c f g =>
        by 
          ext 
          simp  }

theorem skeletal : skeletal SimplexCategory.{u} :=
  fun X Y ⟨I⟩ =>
    by 
      suffices  : Fintype.card (Finₓ (X.len+1)) = Fintype.card (Finₓ (Y.len+1))
      ·
        ext 
        simpa
      ·
        apply Fintype.card_congr 
        refine' equiv.ulift.symm.trans (((skeletal_functor ⋙ forget _).mapIso I).toEquiv.trans _)
        apply Equiv.ulift

namespace SkeletalFunctor

instance : full skeletal_functor.{u, v} :=
  { Preimage := fun a b f => SimplexCategory.Hom.mk ⟨fun i => (f (Ulift.up i)).down, fun i j h => f.monotone h⟩,
    witness' :=
      by 
        intro m n f 
        dsimp  at *
        ext1 ⟨i⟩
        ext1 
        ext1 
        cases x 
        simp  }

instance : faithful skeletal_functor.{u, v} :=
  { map_injective' :=
      fun m n f g h =>
        by 
          ext1 
          ext1 
          ext1 i 
          apply Ulift.up.inj 
          change (skeletal_functor.map f) ⟨i⟩ = (skeletal_functor.map g) ⟨i⟩
          rw [h] }

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : ess_surj skeletal_functor.{u, v} :=
{ mem_ess_image := λ
  X, ⟨mk («expr - »(fintype.card X, 1) : exprℕ()), ⟨begin
      have [ident aux] [":", expr «expr = »(fintype.card X, «expr + »(«expr - »(fintype.card X, 1), 1))] [],
      { exact [expr «expr $ »(nat.succ_pred_eq_of_pos, fintype.card_pos_iff.mpr ⟨«expr⊥»()⟩).symm] },
      let [ident f] [] [":=", expr mono_equiv_of_fin X aux],
      have [ident hf] [] [":=", expr (finset.univ.order_emb_of_fin aux).strict_mono],
      refine [expr { hom := ⟨λ i, f i.down, _⟩, inv := ⟨λ i, ⟨f.symm i⟩, _⟩, hom_inv_id' := _, inv_hom_id' := _ }],
      { rintro ["⟨", ident i, "⟩", "⟨", ident j, "⟩", ident h],
        show [expr «expr ≤ »(f i, f j)],
        exact [expr hf.monotone h] },
      { intros [ident i, ident j, ident h],
        show [expr «expr ≤ »(f.symm i, f.symm j)],
        rw ["<-", expr hf.le_iff_le] [],
        show [expr «expr ≤ »(f (f.symm i), f (f.symm j))],
        simpa [] [] ["only"] ["[", expr order_iso.apply_symm_apply, "]"] [] [] },
      { ext1 [] [],
        ext1 [] ["⟨", ident i, "⟩"],
        ext1 [] [],
        exact [expr f.symm_apply_apply i] },
      { ext1 [] [],
        ext1 [] [ident i],
        exact [expr f.apply_symm_apply i] }
    end⟩⟩ }

noncomputable instance is_equivalence : is_equivalence skeletal_functor.{u, v} :=
  equivalence.of_fully_faithfully_ess_surj skeletal_functor

end SkeletalFunctor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletal_equivalence : SimplexCategory.{u} ≌ NonemptyFinLinOrdₓ.{v} :=
  functor.as_equivalence skeletal_functor

end Skeleton

/--
`simplex_category` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable def is_skeleton_of : is_skeleton_of NonemptyFinLinOrdₓ SimplexCategory skeletal_functor.{u, v} :=
  { skel := skeletal, eqv := skeletal_functor.is_equivalence }

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler small_category
/-- The truncated simplex category. -/ @[derive #[expr small_category]] def truncated (n : exprℕ()) :=
{a : simplex_category.{u} // «expr ≤ »(a.len, n)}

namespace Truncated

instance {n} : Inhabited (truncated n) :=
  ⟨⟨[0],
      by 
        simp ⟩⟩

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/--
The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
@[derive #["[", expr full, ",", expr faithful, "]"]]
def inclusion {n : exprℕ()} : «expr ⥤ »(simplex_category.truncated.{u} n, simplex_category.{u}) :=
full_subcategory_inclusion _

end Truncated

section Concrete

instance : concrete_category.{0} SimplexCategory.{u} :=
  { forget := { obj := fun i => Finₓ (i.len+1), map := fun i j f => f.to_preorder_hom }, forget_faithful := {  } }

end Concrete

section EpiMono

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A morphism in `simplex_category` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective
{n m : simplex_category.{u}}
{f : «expr ⟶ »(n, m)} : «expr ↔ »(mono f, function.injective f.to_preorder_hom) :=
begin
  split,
  { introsI [ident m, ident x, ident y, ident h],
    have [ident H] [":", expr «expr = »(«expr ≫ »(const n x, f), «expr ≫ »(const n y, f))] [],
    { dsimp [] [] [] [],
      rw [expr h] [] },
    change [expr «expr = »((n.const x).to_preorder_hom 0, (n.const y).to_preorder_hom 0)] [] [],
    rw [expr cancel_mono f] ["at", ident H],
    rw [expr H] [] },
  { exact [expr concrete_category.mono_of_injective f] }
end

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A morphism in `simplex_category` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective
{n m : simplex_category.{u}}
{f : «expr ⟶ »(n, m)} : «expr ↔ »(epi f, function.surjective f.to_preorder_hom) :=
begin
  split,
  { introsI [ident hyp_f_epi, ident x],
    by_contradiction [ident h_ab],
    rw [expr not_exists] ["at", ident h_ab],
    set [] [ident chi_1] [":", expr «expr ⟶ »(m, «expr[ ]»(1))] [":="] [expr hom.mk ⟨λ
      u, if «expr ≤ »(u, x) then 0 else 1, begin
        intros [ident a, ident b, ident h],
        dsimp ["only"] ["[", "]"] [] [],
        split_ifs [] ["with", ident h1, ident h2, ident h3],
        any_goals { exact [expr le_refl _] },
        { exact [expr bot_le] },
        { exact [expr false.elim (h1 (le_trans h h3))] }
      end⟩] [],
    set [] [ident chi_2] [":", expr «expr ⟶ »(m, «expr[ ]»(1))] [":="] [expr hom.mk ⟨λ
      u, if «expr < »(u, x) then 0 else 1, begin
        intros [ident a, ident b, ident h],
        dsimp ["only"] ["[", "]"] [] [],
        split_ifs [] ["with", ident h1, ident h2, ident h3],
        any_goals { exact [expr le_refl _] },
        { exact [expr bot_le] },
        { exact [expr false.elim (h1 (lt_of_le_of_lt h h3))] }
      end⟩] [],
    have [ident f_comp_chi_i] [":", expr «expr = »(«expr ≫ »(f, chi_1), «expr ≫ »(f, chi_2))] [],
    { dsimp [] [] [] [],
      ext [] [] [],
      simp [] [] [] ["[", expr le_iff_lt_or_eq, ",", expr h_ab x_1, "]"] [] [] },
    rw [expr category_theory.cancel_epi f] ["at", ident f_comp_chi_i],
    rename [ident f_comp_chi_i, ident eq_chi_i],
    apply_fun [expr λ e, e.to_preorder_hom x] ["at", ident eq_chi_i] [],
    suffices [] [":", expr «expr = »((0 : fin 2), 1)],
    by exact [expr bot_ne_top this],
    simpa [] [] [] [] [] ["using", expr eq_chi_i] },
  { exact [expr concrete_category.epi_of_surjective f] }
end

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A monomorphism in `simplex_category` must increase lengths-/
theorem len_le_of_mono {x y : simplex_category.{u}} {f : «expr ⟶ »(x, y)} : mono f → «expr ≤ »(x.len, y.len) :=
begin
  intro [ident hyp_f_mono],
  have [ident f_inj] [":", expr function.injective f.to_preorder_hom.to_fun] [],
  { exact [expr mono_iff_injective.elim_left hyp_f_mono] },
  simpa [] [] [] [] [] ["using", expr fintype.card_le_of_injective f.to_preorder_hom.to_fun f_inj]
end

theorem le_of_mono {n m : ℕ} {f : [n] ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono

-- error in AlgebraicTopology.SimplexCategory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An epimorphism in `simplex_category` must decrease lengths-/
theorem len_le_of_epi {x y : simplex_category.{u}} {f : «expr ⟶ »(x, y)} : epi f → «expr ≤ »(y.len, x.len) :=
begin
  intro [ident hyp_f_epi],
  have [ident f_surj] [":", expr function.surjective f.to_preorder_hom.to_fun] [],
  { exact [expr epi_iff_surjective.elim_left hyp_f_epi] },
  simpa [] [] [] [] [] ["using", expr fintype.card_le_of_surjective f.to_preorder_hom.to_fun f_surj]
end

theorem le_of_epi {n m : ℕ} {f : [n] ⟶ [m]} : epi f → m ≤ n :=
  len_le_of_epi

end EpiMono

end SimplexCategory

