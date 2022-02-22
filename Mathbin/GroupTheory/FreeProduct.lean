/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathbin.Algebra.FreeMonoid
import Mathbin.GroupTheory.Congruence
import Mathbin.GroupTheory.IsFreeGroup
import Mathbin.Data.List.Chain

/-!
# The free product of groups or monoids

Given an `ι`-indexed family `M` of monoids, we define their free product (categorical coproduct)
`free_product M`. When `ι` and all `M i` have decidable equality, the free product bijects with the
type `word M` of reduced words. This bijection is constructed by defining an action of
`free_product M` on `word M`.

When `M i` are all groups, `free_product M` is also a group (and the coproduct in the category of
groups).

## Main definitions

- `free_product M`: the free product, defined as a quotient of a free monoid.
- `free_product.of {i} : M i →* free_product M`.
- `free_product.lift : (Π {i}, M i →* N) ≃ (free_product M →* N)`: the universal property.
- `free_product.word M`: the type of reduced words.
- `free_product.word.equiv M : free_product M ≃ word M`.

## Remarks

There are many answers to the question "what is the free product of a family `M` of monoids?", and
they are all equivalent but not obviously equivalent. We provide two answers. The first, almost
tautological answer is given by `free_product M`, which is a quotient of the type of words in the
alphabet `Σ i, M i`. It's straightforward to define and easy to prove its universal property. But
this answer is not completely satisfactory, because it's difficult to tell when two elements
`x y : free_product M` are distinct since `free_product M` is defined as a quotient.

The second, maximally efficient answer is given by `word M`. An element of `word M` is a word in the
alphabet `Σ i, M i`, where the letter `⟨i, 1⟩` doesn't occur and no adjacent letters share an index
`i`. Since we only work with reduced words, there is no need for quotienting, and it is easy to tell
when two elements are distinct. However it's not obvious that this is even a monoid!

We prove that every element of `free_product M` can be represented by a unique reduced word, i.e.
`free_product M` and `word M` are equivalent types. This means that `word M` can be given a monoid
structure, and it lets us tell when two elements of `free_product M` are distinct.

There is also a completely tautological, maximally inefficient answer given by
`algebra.category.Mon.colimits`. Whereas `free_product M` at least ensures that (any instance of)
associativity holds by reflexivity, in this answer associativity holds because of quotienting. Yet
another answer, which is constructively more satisfying, could be obtained by showing that
`free_product.rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/


variable {ι : Type _} (M : ∀ i : ι, Type _) [∀ i, Monoidₓ (M i)]

/-- A relation on the free monoid on alphabet `Σ i, M i`, relating `⟨i, 1⟩` with `1` and
`⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
inductive FreeProduct.Rel : FreeMonoid (Σi, M i) → FreeMonoid (Σi, M i) → Prop
  | of_one (i : ι) : FreeProduct.Rel (FreeMonoid.of ⟨i, 1⟩) 1
  | of_mul {i : ι} (x y : M i) :
    FreeProduct.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)

/-- The free product (categorical coproduct) of an indexed family of monoids. -/
def FreeProduct : Type _ :=
  (conGen (FreeProduct.Rel M)).Quotient deriving Monoidₓ, Inhabited

namespace FreeProduct

/-- The type of reduced words. A reduced word cannot contain a letter `1`, and no two adjacent
letters can come from the same summand. -/
@[ext]
structure Word where
  toList : List (Σi, M i)
  ne_one : ∀, ∀ l ∈ to_list, ∀, Sigma.snd l ≠ 1
  chain_ne : to_list.Chain' fun l l' => Sigma.fst l ≠ Sigma.fst l'

variable {M}

/-- The inclusion of a summand into the free product. -/
def of {i : ι} : M i →* FreeProduct M where
  toFun := fun x => Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (FreeProduct.Rel.of_one i))
  map_mul' := fun x y => Eq.symm <| (Con.eq _).mpr (ConGen.Rel.of _ _ (FreeProduct.Rel.of_mul x y))

theorem of_apply {i} (m : M i) : of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m) :=
  rfl

variable {N : Type _} [Monoidₓ N]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem ext_hom (f g : FreeProduct M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← of_apply, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply, h]

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, charaterizing it as a categorical coproduct. -/
@[simps symmApply]
def lift : (∀ i, M i →* N) ≃ (FreeProduct M →* N) where
  toFun := fun fi =>
    Con.lift _ (FreeMonoid.lift fun p : Σi, M i => fi p.fst p.snd) <|
      Con.con_gen_le
        (by
          simp_rw [Con.rel_eq_coe, Con.ker_rel]
          rintro _ _ (i | ⟨i, x, y⟩)
          · change FreeMonoid.lift _ (FreeMonoid.of _) = FreeMonoid.lift _ 1
            simp only [MonoidHom.map_one, FreeMonoid.lift_eval_of]
            
          · change FreeMonoid.lift _ (FreeMonoid.of _ * FreeMonoid.of _) = FreeMonoid.lift _ (FreeMonoid.of _)
            simp only [MonoidHom.map_mul, FreeMonoid.lift_eval_of]
            )
  invFun := fun f i => f.comp of
  left_inv := by
    intro fi
    ext i x
    rw [MonoidHom.comp_apply, of_apply, Con.lift_mk', FreeMonoid.lift_eval_of]
  right_inv := by
    intro f
    ext i x
    simp only [MonoidHom.comp_apply, of_apply, Con.lift_mk', FreeMonoid.lift_eval_of]

@[simp]
theorem lift_of {N} [Monoidₓ N] (fi : ∀ i, M i →* N) {i} (m : M i) : lift fi (of m) = fi i m := by
  conv_rhs => rw [← lift.symm_apply_apply fi, lift_symm_apply, MonoidHom.comp_apply]

@[elab_as_eliminator]
theorem induction_on {C : FreeProduct M → Prop} (m : FreeProduct M) (h_one : C 1) (h_of : ∀ i m : M i, C (of m))
    (h_mul : ∀ x y, C x → C y → C (x * y)) : C m := by
  let S : Submonoid (FreeProduct M) := ⟨SetOf C, h_one, h_mul⟩
  convert Subtype.prop (lift (fun i => of.cod_mrestrict S (h_of i)) m)
  change MonoidHom.id _ m = S.subtype.comp _ m
  congr
  ext
  simp [MonoidHom.codMrestrict]

theorem of_left_inverse [DecidableEq ι] (i : ι) :
    Function.LeftInverse (lift <| Function.update 1 i (MonoidHom.id (M i))) of := fun x => by
  simp only [lift_of, Function.update_same, MonoidHom.id_apply]

theorem of_injective (i : ι) : Function.Injective ⇑(of : M i →* _) := by
  classical
  exact (of_left_inverse i).Injective

section Groupₓ

variable (G : ι → Type _) [∀ i, Groupₓ (G i)]

instance : Inv (FreeProduct G) where
  inv := MulOpposite.unop ∘ lift fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom

theorem inv_def (x : FreeProduct G) :
    x⁻¹ = MulOpposite.unop (lift (fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom) x) :=
  rfl

instance : Groupₓ (FreeProduct G) :=
  { FreeProduct.hasInv G, FreeProduct.monoid G with
    mul_left_inv := by
      intro m
      rw [inv_def]
      apply m.induction_on
      · rw [MonoidHom.map_one, MulOpposite.unop_one, one_mulₓ]
        
      · intro i m
        change of m⁻¹ * of m = 1
        rw [← of.map_mul, mul_left_invₓ, of.map_one]
        
      · intro x y hx hy
        rw [MonoidHom.map_mul, MulOpposite.unop_mul, mul_assoc, ← mul_assoc _ x y, hx, one_mulₓ, hy]
         }

end Groupₓ

namespace Word

/-- The empty reduced word. -/
def empty : Word M where
  toList := []
  ne_one := fun _ => False.elim
  chain_ne := List.chain'_nil

instance : Inhabited (Word M) :=
  ⟨empty⟩

/-- A reduced word determines an element of the free product, given by multiplication. -/
def prod (w : Word M) : FreeProduct M :=
  List.prod (w.toList.map fun l => of l.snd)

@[simp]
theorem prod_nil : prod (empty : Word M) = 1 :=
  rfl

/-- `fst_idx w` is `some i` if the first letter of `w` is `⟨i, m⟩` with `m : M i`. If `w` is empty
then it's `none`. -/
def fstIdx (w : Word M) : Option ι :=
  w.toList.head'.map Sigma.fst

theorem fst_idx_ne_iff {w : Word M} {i} : fstIdx w ≠ some i ↔ ∀, ∀ l ∈ w.toList.head', ∀, i ≠ Sigma.fst l :=
  not_iff_not.mp <| by
    simp [fst_idx]

variable (M)

/-- Given an index `i : ι`, `pair M i` is the type of pairs `(head, tail)` where `head : M i` and
`tail : word M`, subject to the constraint that first letter of `tail` can't be `⟨i, m⟩`.
By prepending `head` to `tail`, one obtains a new word. We'll show that any word can be uniquely
obtained in this way. -/
@[ext]
structure Pair (i : ι) where
  head : M i
  tail : Word M
  fst_idx_ne : fstIdx tail ≠ some i

instance (i : ι) : Inhabited (Pair M i) :=
  ⟨⟨1, empty, by
      tauto⟩⟩

variable {M}

variable [∀ i, DecidableEq (M i)]

/-- Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, except if `head`
is `1 : M i` then we have to just return `word` since we need the result to be reduced. -/
def rcons {i} (p : Pair M i) : Word M :=
  if h : p.head = 1 then p.tail
  else
    { toList := ⟨i, p.head⟩ :: p.tail.toList,
      ne_one := by
        rintro l (rfl | hl)
        exact h
        exact p.tail.ne_one l hl,
      chain_ne := p.tail.chain_ne.cons' (fst_idx_ne_iff.mp p.fst_idx_ne) }

/-- Given a word of the form `⟨l :: ls, h1, h2⟩`, we can form a word of the form `⟨ls, _, _⟩`,
dropping the first letter. -/
private def mk_aux {l} (ls : List (Σi, M i)) (h1 : ∀, ∀ l' ∈ l :: ls, ∀, Sigma.snd l' ≠ 1) (h2 : (l :: ls).Chain' _) :
    Word M :=
  ⟨ls, fun l' hl => h1 _ (List.mem_cons_of_memₓ _ hl), h2.tail⟩

theorem cons_eq_rcons {i} {m : M i} {ls h1 h2} :
    Word.mk (⟨i, m⟩ :: ls) h1 h2 = rcons ⟨m, mkAux ls h1 h2, fst_idx_ne_iff.mpr h2.rel_head'⟩ := by
  rw [rcons, dif_neg]
  rfl
  exact h1 ⟨i, m⟩ (ls.mem_cons_self _)

@[simp]
theorem prod_rcons {i} (p : Pair M i) : prod (rcons p) = of p.head * prod p.tail :=
  if hm : p.head = 1 then by
    rw [rcons, dif_pos hm, hm, MonoidHom.map_one, one_mulₓ]
  else by
    rw [rcons, dif_neg hm, Prod, List.map_cons, List.prod_cons, Prod]

theorem rcons_inj {i} : Function.Injective (rcons : Pair M i → Word M) := by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  by_cases' hm : m = 1 <;> by_cases' hm' : m' = 1
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    cc
    
  · exfalso
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    rw [he] at h
    exact h rfl
    
  · exfalso
    simp only [rcons, dif_pos hm', dif_neg hm] at he
    rw [← he] at h'
    exact h' rfl
    
  · have : m = m' ∧ w.to_list = w'.to_list := by
      simpa only [rcons, dif_neg hm, dif_neg hm', true_andₓ, eq_self_iff_true, Subtype.mk_eq_mk, heq_iff_eq, ←
        Subtype.ext_iff_val] using he
    rcases this with ⟨rfl, h⟩
    congr
    exact word.ext _ _ h
    

variable [DecidableEq ι]

/-- Given `i : ι`, any reduced word can be decomposed into a pair `p` such that `w = rcons p`. -/
-- This definition is computable but not very nice to look at. Thankfully we don't have to inspect
-- it, since `rcons` is known to be injective.
private def equiv_pair_aux i : ∀ w : Word M, { p : Pair M i // rcons p = w }
  | w@⟨[], _, _⟩ =>
    ⟨⟨1, w, by
        rintro ⟨⟩⟩,
      dif_pos rfl⟩
  | w@⟨⟨j, m⟩ :: ls, h1, h2⟩ =>
    if ij : i = j then
      { val :=
          { head := ij.symm.rec m, tail := mkAux ls h1 h2,
            fst_idx_ne := by
              cases ij <;> exact fst_idx_ne_iff.mpr h2.rel_head' },
        property := by
          cases ij <;> exact cons_eq_rcons.symm }
    else ⟨⟨1, w, (Option.some_injective _).Ne (Ne.symm ij)⟩, dif_pos rfl⟩

/-- The equivalence between words and pairs. Given a word, it decomposes it as a pair by removing
the first letter if it comes from `M i`. Given a pair, it prepends the head to the tail. -/
def equivPair i : Word M ≃ Pair M i where
  toFun := fun w => (equivPairAux i w).val
  invFun := rcons
  left_inv := fun w => (equivPairAux i w).property
  right_inv := fun p => rcons_inj (equivPairAux i _).property

theorem equiv_pair_symm i (p : Pair M i) : (equivPair i).symm p = rcons p :=
  rfl

theorem equiv_pair_eq_of_fst_idx_ne {i} {w : Word M} (h : fstIdx w ≠ some i) : equivPair i w = ⟨1, w, h⟩ :=
  (equivPair i).apply_eq_iff_eq_symm_apply.mpr <| Eq.symm (dif_pos rfl)

instance summandAction i : MulAction (M i) (Word M) where
  smul := fun m w => rcons { equivPair i w with head := m * (equivPair i w).head }
  one_smul := fun w => by
    simp_rw [one_mulₓ]
    apply (equiv_pair i).symm_apply_eq.mpr
    ext <;> rfl
  mul_smul := fun m m' w => by
    simp only [mul_assoc, ← equiv_pair_symm, Equivₓ.apply_symm_apply]

instance : MulAction (FreeProduct M) (Word M) :=
  MulAction.ofEndHom (lift fun i => MulAction.toEndHom)

theorem of_smul_def i (w : Word M) (m : M i) :
    of m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl

theorem cons_eq_smul {i} {m : M i} {ls h1 h2} : Word.mk (⟨i, m⟩ :: ls) h1 h2 = of m • mkAux ls h1 h2 := by
  rw [cons_eq_rcons, of_smul_def, equiv_pair_eq_of_fst_idx_ne _] <;> simp only [mul_oneₓ]

theorem smul_induction {C : Word M → Prop} (h_empty : C empty) (h_smul : ∀ i m : M i w, C w → C (of m • w))
    (w : Word M) : C w := by
  cases' w with ls h1 h2
  induction' ls with l ls ih
  · exact h_empty
    
  cases' l with i m
  rw [cons_eq_smul]
  exact h_smul _ _ _ (ih _ _)

@[simp]
theorem prod_smul m : ∀ w : Word M, prod (m • w) = m * prod w := by
  apply m.induction_on
  · intro
    rw [one_smul, one_mulₓ]
    
  · intros
    rw [of_smul_def, prod_rcons, of.map_mul, mul_assoc, ← prod_rcons, ← equiv_pair_symm, Equivₓ.symm_apply_apply]
    
  · intro x y hx hy w
    rw [mul_smul, hx, hy, mul_assoc]
    

/-- Each element of the free product corresponds to a unique reduced word. -/
def equiv : FreeProduct M ≃ Word M where
  toFun := fun m => m • Empty
  invFun := fun w => prod w
  left_inv := fun m => by
    dsimp only <;> rw [prod_smul, prod_nil, mul_oneₓ]
  right_inv := by
    apply smul_induction
    · dsimp only
      rw [prod_nil, one_smul]
      
    · dsimp only
      intro i m w ih
      rw [prod_smul, mul_smul, ih]
      

instance : DecidableEq (Word M) :=
  Function.Injective.decidableEq Word.ext

instance : DecidableEq (FreeProduct M) :=
  Word.equiv.DecidableEq

end Word

/-- The free product of free groups is itself a free group -/
@[simps]
instance {ι : Type _} (G : ι → Type _) [∀ i, Groupₓ (G i)] [hG : ∀ i, IsFreeGroup (G i)] :
    IsFreeGroup (FreeProduct G) where
  Generators := Σi, IsFreeGroup.Generators (G i)
  of := fun x => FreeProduct.of (IsFreeGroup.of x.2)
  unique_lift' := by
    intros X _ f
    refine' ⟨FreeProduct.lift fun i => IsFreeGroup.lift fun x => f ⟨i, x⟩, _⟩
    constructor
    · simp
      
    · intro g hfg
      ext i x
      simpa using hfg ⟨i, x⟩
      

end FreeProduct

