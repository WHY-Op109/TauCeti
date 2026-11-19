/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Subquotient hulls and the endomorphism algebra of a fibre functor

Let `C` be an abelian category and `ω : C ⥤ ModuleCat R` an exact additive functor.
For an object `X` of `C`, the *subquotient hull* `⟨X⟩` is the full subcategory of quotients of
subobjects of the finite direct sums `Xⁿ = X ⊞ ⋯ ⊞ X`. Following Deligne–Milne, the algebra
`A_X ⊆ End_R (ω X)` consists of the endomorphisms `f` such that, for every `n` and every
subobject `Y ↪ Xⁿ`, the diagonal endomorphism `f ⊕ ⋯ ⊕ f` of `ω (Xⁿ)` preserves the fibre
`ω Y`. Preservation of the fibres of subobjects of `X` alone would not suffice: the subobjects of
the powers `Xⁿ` encode the morphisms between objects of `⟨X⟩`.

The main result identifies `A_X` with the algebra of natural endomorphisms of the restriction of
`ω` to `⟨X⟩`: evaluation at `X` is an `R`-algebra isomorphism. In particular every element of
`A_X` acts on the fibre of every object of `⟨X⟩`, compatibly with all morphisms of `⟨X⟩`, and acts
on `ω (Xⁿ)` diagonally. This is the finite-dimensional algebra through which neutral Tannaka
reconstruction describes `⟨X⟩` as a module category.

No faithfulness of `ω` is needed, and the coefficients form an arbitrary commutative ring.

## Main definitions

* `TauCeti.Tannaka.subquotientHull X`: the subquotient hull `⟨X⟩`, as a property of objects.
* `TauCeti.Tannaka.diagonalFiberEnd ω X n`: the diagonal algebra map
  `End_R (ω X) → End_R (ω (Xⁿ))`.
* `TauCeti.Tannaka.fiberEndSubalgebra ω X`: the algebra `A_X`.

## Main results

* `TauCeti.Tannaka.subquotientHull` contains `X`, its finite powers and the zero objects, and is
  closed under subobjects and quotients.
* `TauCeti.Tannaka.endSubquotientHullAlgEquiv`: the natural endomorphisms of `ω` restricted to
  `⟨X⟩` form an algebra isomorphic to `A_X`, by evaluation at `X`.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, §2, Lemma 2.13 and its proof.
-/

public section

open CategoryTheory Limits

namespace TauCeti.Tannaka

universe v u w u'

variable {C : Type u} [Category.{v} C]

section Hull

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- The subquotient hull `⟨X⟩` of an object `X`: the objects `Z` which are quotients of a
subobject of a finite direct sum `Xⁿ` of copies of `X`. -/
def subquotientHull (X : C) : ObjectProperty C :=
  fun Z => ∃ (n : ℕ) (Y : C) (i : Y ⟶ ⨁ fun _ : Fin n => X) (p : Y ⟶ Z), Mono i ∧ Epi p

variable {X : C}

/-- Membership in the subquotient hull, unfolded. -/
lemma subquotientHull_iff {Z : C} :
    subquotientHull X Z ↔
      ∃ (n : ℕ) (Y : C) (i : Y ⟶ ⨁ fun _ : Fin n => X) (p : Y ⟶ Z), Mono i ∧ Epi p :=
  Iff.rfl

/-- A quotient of a subobject of `Xⁿ` lies in the subquotient hull of `X`. -/
lemma subquotientHull_of_mono_of_epi {n : ℕ} {Y Z : C} (i : Y ⟶ ⨁ fun _ : Fin n => X)
    (p : Y ⟶ Z) [Mono i] [Epi p] : subquotientHull X Z :=
  ⟨n, Y, i, p, inferInstance, inferInstance⟩

/-- A subobject of `Xⁿ` lies in the subquotient hull of `X`. -/
lemma subquotientHull_of_mono {n : ℕ} {Y : C} (i : Y ⟶ ⨁ fun _ : Fin n => X) [Mono i] :
    subquotientHull X Y :=
  subquotientHull_of_mono_of_epi i (𝟙 Y)

/-- The finite powers `Xⁿ` lie in the subquotient hull of `X`. -/
lemma subquotientHull_biproduct (n : ℕ) : subquotientHull X (⨁ fun _ : Fin n => X) :=
  subquotientHull_of_mono (𝟙 _)

/-- An object lies in its own subquotient hull. -/
lemma subquotientHull_self : subquotientHull X X :=
  subquotientHull_of_mono (biproduct.ι (fun _ : Fin 1 => X) 0)

/-- A quotient of an object of `⟨X⟩` lies in `⟨X⟩`. -/
instance : (subquotientHull X).IsClosedUnderQuotients where
  prop_of_epi q _ := by
    rintro ⟨n, Y, i, p, _, _⟩
    exact subquotientHull_of_mono_of_epi i (p ≫ q)

/-- Every zero object lies in the subquotient hull of `X`. -/
lemma subquotientHull_of_isZero {Z : C} (hZ : IsZero Z) : subquotientHull X Z :=
  have : Mono (hZ.to_ (⨁ fun _ : Fin 0 => X)) := ⟨fun _ _ _ => hZ.eq_of_tgt _ _⟩
  subquotientHull_of_mono (hZ.to_ (⨁ fun _ : Fin 0 => X))

instance : (subquotientHull X).ContainsZero where
  exists_zero := ⟨_, (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j => j.elim0),
    subquotientHull_biproduct 0⟩

/-- The subquotient hull of a zero object consists of the zero objects. -/
lemma subquotientHull_iff_isZero (hX : IsZero X) {Z : C} : subquotientHull X Z ↔ IsZero Z := by
  refine ⟨fun ⟨n, Y, i, p, _, _⟩ => ?_, subquotientHull_of_isZero⟩
  have hXn : IsZero (⨁ fun _ : Fin n => X) :=
    (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j => hX.eq_of_tgt _ _)
  exact IsZero.of_epi p (IsZero.of_mono i hXn)

end Hull

section Abelian

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] {X : C}

/-- In an abelian category, a subobject of an object of `⟨X⟩` lies in `⟨X⟩`. -/
instance : (subquotientHull X).IsClosedUnderSubobjects where
  prop_of_mono {Z' Z} j _ := by
    rintro ⟨n, Y, i, p, _, _⟩
    exact subquotientHull_of_mono_of_epi (pullback.fst p j ≫ i) (pullback.snd p j)

end Abelian

section Diagonal

variable [Preadditive C] [HasFiniteBiproducts C]
variable {R : Type u'} [CommRing R] (ω : C ⥤ ModuleCat.{w} R) [ω.Additive]

omit [HasFiniteBiproducts C] in
/-- The images under `ω` of the biproduct projections are jointly injective. -/
private lemma fiber_biproduct_ext {J : Type*} [Finite J] {Xs : J → C} [HasBiproduct Xs]
    {u v : ω.obj (⨁ Xs)}
    (h : ∀ k, (ω.map (biproduct.π Xs k)).hom u = (ω.map (biproduct.π Xs k)).hom v) :
    u = v := by
  have := Fintype.ofFinite J
  have key (y : ω.obj (⨁ Xs)) :
      ∑ k, (ω.map (biproduct.ι Xs k)).hom ((ω.map (biproduct.π Xs k)).hom y) = y := by
    have := congrArg (fun φ => (ω.map φ).hom y) (biproduct.total (f := Xs))
    simp only [ω.map_sum, ω.map_comp, ModuleCat.hom_sum, ModuleCat.hom_comp, LinearMap.sum_apply,
      LinearMap.comp_apply, ω.map_id, ModuleCat.hom_id, LinearMap.id_apply] at this
    exact this
  rw [← key u, ← key v]
  simp_rw [h]

variable (X : C) (n : ℕ)

/-- The diagonal endomorphism `f ⊕ ⋯ ⊕ f` of `ω (Xⁿ)`, as a morphism of modules. -/
private noncomputable def diagonalAux (f : Module.End R (ω.obj X)) :
    ω.obj (⨁ fun _ : Fin n => X) ⟶ ω.obj (⨁ fun _ : Fin n => X) :=
  ∑ k, ω.map (biproduct.π (fun _ : Fin n => X) k) ≫ ModuleCat.ofHom f ≫
    ω.map (biproduct.ι (fun _ : Fin n => X) k)

private lemma diagonalAux_comp_map_π (f : Module.End R (ω.obj X)) (k : Fin n) :
    diagonalAux ω X n f ≫ ω.map (biproduct.π (fun _ : Fin n => X) k) =
      ω.map (biproduct.π (fun _ : Fin n => X) k) ≫ ModuleCat.ofHom f := by
  rw [diagonalAux, Preadditive.sum_comp, Finset.sum_eq_single k]
  · simp [← ω.map_comp]
  · intro j _ hj
    simp [← ω.map_comp, biproduct.ι_π_ne _ hj]
  · simp

private lemma map_π_diagonalAux_apply (f : Module.End R (ω.obj X)) (k : Fin n)
    (x : ω.obj (⨁ fun _ : Fin n => X)) :
    (ω.map (biproduct.π (fun _ : Fin n => X) k)).hom ((diagonalAux ω X n f).hom x) =
      f ((ω.map (biproduct.π (fun _ : Fin n => X) k)).hom x) :=
  congrArg (fun φ => φ.hom x) (diagonalAux_comp_map_π ω X n f k)

/-- The diagonal algebra map `End_R (ω X) → End_R (ω (Xⁿ))`, sending `f` to the endomorphism
`f ⊕ ⋯ ⊕ f` of `ω (Xⁿ)`; it is characterised by `map_π_diagonalFiberEnd_apply`. -/
noncomputable def diagonalFiberEnd :
    Module.End R (ω.obj X) →ₐ[R] Module.End R (ω.obj (⨁ fun _ : Fin n => X)) where
  toFun f := (diagonalAux ω X n f).hom
  map_one' := LinearMap.ext fun x => fiber_biproduct_ext ω fun k => by
    simp [map_π_diagonalAux_apply]
  map_mul' f g := LinearMap.ext fun x => fiber_biproduct_ext ω fun k => by
    simp [map_π_diagonalAux_apply]
  map_zero' := LinearMap.ext fun x => fiber_biproduct_ext ω fun k => by
    simp [map_π_diagonalAux_apply]
  map_add' f g := LinearMap.ext fun x => fiber_biproduct_ext ω fun k => by
    simp [map_π_diagonalAux_apply]
  commutes' r := LinearMap.ext fun x => fiber_biproduct_ext ω fun k => by
    simp [map_π_diagonalAux_apply]

variable {X n}

/-- The diagonal endomorphism `f ⊕ ⋯ ⊕ f` acts by `f` on each component of `ω (Xⁿ)`. -/
@[simp]
lemma map_π_diagonalFiberEnd_apply (f : Module.End R (ω.obj X)) (k : Fin n)
    (x : ω.obj (⨁ fun _ : Fin n => X)) :
    (ω.map (biproduct.π (fun _ : Fin n => X) k)).hom (diagonalFiberEnd ω X n f x) =
      f ((ω.map (biproduct.π (fun _ : Fin n => X) k)).hom x) :=
  map_π_diagonalAux_apply ω X n f k x

/-- An endomorphism of `ω (Xⁿ)` is the diagonal endomorphism of `f` if and only if it commutes
with the projections `ω (Xⁿ) → ω X`. -/
lemma eq_diagonalFiberEnd_iff {f : Module.End R (ω.obj X)}
    {φ : Module.End R (ω.obj (⨁ fun _ : Fin n => X))} :
    φ = diagonalFiberEnd ω X n f ↔
      ∀ k x, (ω.map (biproduct.π (fun _ : Fin n => X) k)).hom (φ x) =
        f ((ω.map (biproduct.π (fun _ : Fin n => X) k)).hom x) := by
  refine ⟨?_, fun h => LinearMap.ext fun x => fiber_biproduct_ext ω fun k => by simp [h]⟩
  rintro rfl k x
  exact map_π_diagonalFiberEnd_apply ω f k x

variable (X)

/-- The algebra `A_X ⊆ End_R (ω X)` of Deligne–Milne: the endomorphisms `f` whose diagonal
endomorphism `f ⊕ ⋯ ⊕ f` of `ω (Xⁿ)` preserves the fibre of every subobject of `Xⁿ`, for
every `n`. -/
noncomputable def fiberEndSubalgebra : Subalgebra R (Module.End R (ω.obj X)) where
  carrier := {f | ∀ (n : ℕ) (Y : C) (i : Y ⟶ ⨁ fun _ : Fin n => X), Mono i →
    LinearMap.range (ω.map i).hom ∈ (diagonalFiberEnd ω X n f).invtSubmodule}
  mul_mem' {f g} hf hg n Y i hi := by
    rw [map_mul, Module.End.mul_eq_comp]
    exact Module.End.invtSubmodule.comp _ (hf n Y i hi) (hg n Y i hi)
  add_mem' {f g} hf hg n Y i hi := by
    rw [map_add]
    exact Module.End.invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add _ _
      ⟨hf n Y i hi, hg n Y i hi⟩
  algebraMap_mem' r n Y i _ := by
    rw [AlgHom.commutes, Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    simpa using Submodule.smul_mem _ r hx

variable {X}

/-- Membership in `A_X`, unfolded. -/
lemma mem_fiberEndSubalgebra_iff {f : Module.End R (ω.obj X)} :
    f ∈ fiberEndSubalgebra ω X ↔
      ∀ (n : ℕ) (Y : C) (i : Y ⟶ ⨁ fun _ : Fin n => X), Mono i →
        LinearMap.range (ω.map i).hom ∈ (diagonalFiberEnd ω X n f).invtSubmodule :=
  Iff.rfl

/-- An element of `A_X` lifts the diagonal action on `ω (Xⁿ)` along the fibre of every
subobject of `Xⁿ`. -/
lemma exists_map_eq_diagonalFiberEnd {f : Module.End R (ω.obj X)}
    (hf : f ∈ fiberEndSubalgebra ω X) {n : ℕ} {Y : C} (i : Y ⟶ ⨁ fun _ : Fin n => X) [Mono i]
    (y : ω.obj Y) : ∃ y₁, (ω.map i).hom y₁ = diagonalFiberEnd ω X n f ((ω.map i).hom y) :=
  ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 (hf n Y i inferInstance) _
    ⟨y, rfl⟩ : _ ∈ LinearMap.range _)

/-- Over a Noetherian ring, `A_X` is a finite module when the fibre `ω X` is; in particular it
is finite-dimensional over a field when `ω X` is. -/
instance [IsNoetherianRing R] [Module.Finite R (ω.obj X)] :
    Module.Finite R (fiberEndSubalgebra ω X) :=
  Module.Finite.of_injective (fiberEndSubalgebra ω X).val.toLinearMap Subtype.val_injective

end Diagonal

section EndAlgEquiv

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] {R : Type u'} [CommRing R] (ω : C ⥤ ModuleCat.{w} R) [ω.Additive]
  [PreservesFiniteLimits ω] [PreservesFiniteColimits ω] {X : C}

private lemma injective_map {Y Z : C} (i : Y ⟶ Z) [Mono i] : Function.Injective (ω.map i).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

private lemma surjective_map {Y Z : C} (p : Y ⟶ Z) [Epi p] :
    Function.Surjective (ω.map p).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- An element of the kernel of `ω p` comes from the fibre of the kernel of `p`. -/
private lemma exists_map_kernelι_eq {Y Z : C} (p : Y ⟶ Z) (y : ω.obj Y)
    (hy : (ω.map p).hom y = 0) : ∃ u, (ω.map (kernel.ι p)).hom u = y :=
  (ShortComplex.moduleCat_exact_iff _).1
    ((ShortComplex.exact_of_f_is_kernel (ShortComplex.mk _ _ (kernel.condition p))
      (kernelIsKernel p)).map ω) y hy

/-- `ψ` is the endomorphism of `ω Z` induced by `f` through the subquotient presentation
`Y ↪ Xⁿ`, `Y ↠ Z`. -/
private def IsInduced (f : Module.End R (ω.obj X)) {n : ℕ} {Y Z : C}
    (i : Y ⟶ ⨁ fun _ : Fin n => X) (p : Y ⟶ Z) (ψ : Module.End R (ω.obj Z)) : Prop :=
  ∀ y y₁, (ω.map i).hom y₁ = diagonalFiberEnd ω X n f ((ω.map i).hom y) →
    ψ ((ω.map p).hom y) = (ω.map p).hom y₁

/-- The endomorphisms induced by an element of `A_X` through presentations of two objects of the
subquotient hull commute with every morphism between them. The proof compares both
presentations through the pullback of `Y ↠ Z → Z'` and `Y' ↠ Z'`, a subobject of `Xⁿ⁺ᵐ`. -/
private lemma isInduced_comm {f : Module.End R (ω.obj X)} (hf : f ∈ fiberEndSubalgebra ω X)
    {n m : ℕ} {Y Y' Z Z' : C} {i : Y ⟶ ⨁ fun _ : Fin n => X} {p : Y ⟶ Z}
    {i' : Y' ⟶ ⨁ fun _ : Fin m => X} {p' : Y' ⟶ Z'} [Mono i] [Epi p] [Mono i'] [Epi p']
    {ψ : Module.End R (ω.obj Z)} {ψ' : Module.End R (ω.obj Z')}
    (hψ : IsInduced ω f i p ψ) (hψ' : IsInduced ω f i' p' ψ') (g : Z ⟶ Z') (z : ω.obj Z) :
    (ω.map g).hom (ψ z) = ψ' ((ω.map g).hom z) := by
  let a := pullback.fst (p ≫ g) p'
  let b := pullback.snd (p ≫ g) p'
  let L : pullback (p ≫ g) p' ⟶ ⨁ fun _ : Fin (n + m) => X :=
    biproduct.lift (Fin.addCases (fun k => a ≫ i ≫ biproduct.π _ k)
      (fun k => b ≫ i' ≫ biproduct.π _ k))
  have hLa (k : Fin n) : L ≫ biproduct.π _ (Fin.castAdd m k) = a ≫ i ≫ biproduct.π _ k := by
    simp [L]
  have hLb (k : Fin m) : L ≫ biproduct.π _ (Fin.natAdd n k) = b ≫ i' ≫ biproduct.π _ k := by
    simp [L]
  have hLa' (k : Fin n) (x : ω.obj (pullback (p ≫ g) p')) :
      (ω.map (biproduct.π _ (Fin.castAdd m k))).hom ((ω.map L).hom x) =
        (ω.map (biproduct.π _ k)).hom ((ω.map i).hom ((ω.map a).hom x)) := by
    simpa using congrArg (fun φ => (ω.map φ).hom x) (hLa k)
  have hLb' (k : Fin m) (x : ω.obj (pullback (p ≫ g) p')) :
      (ω.map (biproduct.π _ (Fin.natAdd n k))).hom ((ω.map L).hom x) =
        (ω.map (biproduct.π _ k)).hom ((ω.map i').hom ((ω.map b).hom x)) := by
    simpa using congrArg (fun φ => (ω.map φ).hom x) (hLb k)
  have : Mono L := ⟨fun u v huv => pullback.hom_ext
    ((cancel_mono i).1 (biproduct.hom_ext _ _ fun k => by
      simpa [hLa] using congrArg (· ≫ biproduct.π _ (Fin.castAdd m k)) huv))
    ((cancel_mono i').1 (biproduct.hom_ext _ _ fun k => by
      simpa [hLb] using congrArg (· ≫ biproduct.π _ (Fin.natAdd n k)) huv))⟩
  obtain ⟨y, rfl⟩ := surjective_map ω p z
  obtain ⟨w, rfl⟩ := surjective_map ω a y
  obtain ⟨w₁, hw₁⟩ := exists_map_eq_diagonalFiberEnd ω hf L w
  have h₁ : (ω.map i).hom ((ω.map a).hom w₁) =
      diagonalFiberEnd ω X n f ((ω.map i).hom ((ω.map a).hom w)) :=
    fiber_biproduct_ext ω fun k => by
      simpa [hLa'] using
        congrArg (ω.map (biproduct.π _ (Fin.castAdd m k))).hom hw₁
  have h₂ : (ω.map i').hom ((ω.map b).hom w₁) =
      diagonalFiberEnd ω X m f ((ω.map i').hom ((ω.map b).hom w)) :=
    fiber_biproduct_ext ω fun k => by
      simpa [hLb'] using
        congrArg (ω.map (biproduct.π _ (Fin.natAdd n k))).hom hw₁
  have hc (x : ω.obj (pullback (p ≫ g) p')) :
      (ω.map g).hom ((ω.map p).hom ((ω.map a).hom x)) = (ω.map p').hom ((ω.map b).hom x) := by
    simpa using congrArg (fun φ => (ω.map φ).hom x) (pullback.condition (f := p ≫ g) (g := p'))
  rw [hψ _ _ h₁, hc, hc, hψ' _ _ h₂]

/-- Every element of `A_X` induces an endomorphism of the fibre of each subquotient of `Xⁿ`. -/
private lemma exists_isInduced {f : Module.End R (ω.obj X)} (hf : f ∈ fiberEndSubalgebra ω X)
    {n : ℕ} {Y Z : C} (i : Y ⟶ ⨁ fun _ : Fin n => X) (p : Y ⟶ Z) [Mono i] [Epi p] :
    ∃ ψ, IsInduced ω f i p ψ := by
  let e := LinearEquiv.ofInjective _ (injective_map ω i)
  let ρ : Module.End R (ω.obj Y) := e.symm.toLinearMap ∘ₗ
    (diagonalFiberEnd ω X n f ∘ₗ (ω.map i).hom).codRestrict _
      fun y => exists_map_eq_diagonalFiberEnd ω hf i y
  have hρ (y : ω.obj Y) : (ω.map i).hom (ρ y) = diagonalFiberEnd ω X n f ((ω.map i).hom y) := by
    rw [← LinearEquiv.ofInjective_apply (h := injective_map ω i)]
    simp only [ρ, e, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact LinearMap.codRestrict_apply _ _ y
  have hker : LinearMap.ker (ω.map p).hom ≤ LinearMap.ker ((ω.map p).hom ∘ₗ ρ) := by
    intro y hy
    obtain ⟨u, rfl⟩ := exists_map_kernelι_eq ω p y hy
    obtain ⟨u₁, hu₁⟩ := exists_map_eq_diagonalFiberEnd ω hf (kernel.ι p ≫ i) u
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hu₁
    have : ρ ((ω.map (kernel.ι p)).hom u) = (ω.map (kernel.ι p)).hom u₁ :=
      injective_map ω i (by rw [hρ, hu₁])
    rw [LinearMap.mem_ker, LinearMap.comp_apply, this, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, ← ω.map_comp, kernel.condition, ω.map_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply]
  refine ⟨(ω.map p).hom.liftOfSurjective (surjective_map ω p) ⟨_, hker⟩, fun y y₁ hy => ?_⟩
  rw [LinearMap.equivOfSurjective_apply, LinearMap.comp_apply,
    injective_map ω i ((hρ y).trans hy.symm)]

private lemma isInduced_unique {f : Module.End R (ω.obj X)} (hf : f ∈ fiberEndSubalgebra ω X)
    {n m : ℕ} {Y Y' Z : C} {i : Y ⟶ ⨁ fun _ : Fin n => X} {p : Y ⟶ Z}
    {i' : Y' ⟶ ⨁ fun _ : Fin m => X} {p' : Y' ⟶ Z} [Mono i] [Epi p] [Mono i'] [Epi p']
    {ψ ψ' : Module.End R (ω.obj Z)} (hψ : IsInduced ω f i p ψ) (hψ' : IsInduced ω f i' p' ψ') :
    ψ = ψ' :=
  LinearMap.ext fun z => by simpa using isInduced_comm ω hf hψ hψ' (𝟙 Z) z

variable (X) in
/-- The evaluation at `X` of natural endomorphisms of `ω` restricted to `⟨X⟩`. -/
private noncomputable def evalSelf :
    End ((subquotientHull X).ι ⋙ ω) →ₐ[R] Module.End R (ω.obj X) where
  toFun η := (η.asHom.app ⟨X, subquotientHull_self⟩).hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

omit [ω.Additive] [PreservesFiniteLimits ω] [PreservesFiniteColimits ω] in
private lemma evalSelf_apply (η : End ((subquotientHull X).ι ⋙ ω)) :
    evalSelf ω X η = (η.asHom.app ⟨X, subquotientHull_self⟩).hom :=
  rfl

omit [ω.Additive] [PreservesFiniteLimits ω] [PreservesFiniteColimits ω] in
private lemma app_naturality_apply (η : End ((subquotientHull X).ι ⋙ ω))
    (Z Z' : (subquotientHull X).FullSubcategory) (g : Z.obj ⟶ Z'.obj) (x : ω.obj Z.obj) :
    (ω.map g).hom ((η.asHom.app Z).hom x) = (η.asHom.app Z').hom ((ω.map g).hom x) := by
  simpa using (congrArg (fun φ => φ.hom x) (η.asHom.naturality (ObjectProperty.homMk g))).symm

omit [PreservesFiniteLimits ω] [PreservesFiniteColimits ω] in
/-- A natural endomorphism of `ω` restricted to `⟨X⟩` acts on `ω (Xⁿ)` diagonally. -/
private lemma app_biproduct_eq (η : End ((subquotientHull X).ι ⋙ ω)) (n : ℕ) :
    (η.asHom.app ⟨_, subquotientHull_biproduct n⟩).hom = diagonalFiberEnd ω X n (evalSelf ω X η) :=
  (eq_diagonalFiberEnd_iff ω).2 fun k x => by
    simpa [evalSelf_apply] using app_naturality_apply ω η ⟨_, subquotientHull_biproduct n⟩
      ⟨X, subquotientHull_self⟩ (biproduct.π _ k) x

omit [PreservesFiniteLimits ω] [PreservesFiniteColimits ω] in
private lemma evalSelf_mem (η : End ((subquotientHull X).ι ⋙ ω)) :
    evalSelf ω X η ∈ fiberEndSubalgebra ω X := by
  intro n Y i _
  rw [← app_biproduct_eq, Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  rintro _ ⟨y, rfl⟩
  exact ⟨_, app_naturality_apply ω η ⟨Y, subquotientHull_of_mono i⟩
    ⟨_, subquotientHull_biproduct n⟩ i y⟩

/-- A natural endomorphism of `ω` restricted to `⟨X⟩` acts on each object of `⟨X⟩` by the
endomorphism its value at `X` induces through any subquotient presentation. -/
private lemma isInduced_app (η : End ((subquotientHull X).ι ⋙ ω)) {n : ℕ} {Y Z : C}
    (i : Y ⟶ ⨁ fun _ : Fin n => X) (p : Y ⟶ Z) [Mono i] [Epi p] :
    IsInduced ω (evalSelf ω X η) i p
      (η.asHom.app ⟨Z, subquotientHull_of_mono_of_epi i p⟩).hom := by
  intro y y₁ hy
  rw [← app_biproduct_eq, ← app_naturality_apply ω η ⟨Y, subquotientHull_of_mono i⟩
    ⟨_, subquotientHull_biproduct n⟩ i] at hy
  rw [← app_naturality_apply ω η ⟨Y, subquotientHull_of_mono i⟩
    ⟨Z, subquotientHull_of_mono_of_epi i p⟩ p, injective_map ω i hy]

private lemma evalSelf_injective : Function.Injective (evalSelf ω X) := by
  intro η η' h
  refine End.ext (NatTrans.ext (funext fun Z => ModuleCat.hom_ext ?_))
  obtain ⟨n, Y, i, p, _, _⟩ := Z.property
  exact isInduced_unique ω (evalSelf_mem ω η) (isInduced_app ω η i p)
    (h ▸ isInduced_app ω η' i p)

private lemma exists_evalSelf_eq {f : Module.End R (ω.obj X)}
    (hf : f ∈ fiberEndSubalgebra ω X) : ∃ η, evalSelf ω X η = f := by
  have key (Z : (subquotientHull X).FullSubcategory) :
      ∃ ψ : Module.End R (ω.obj Z.obj), ∀ (n : ℕ) (Y : C) (i : Y ⟶ ⨁ fun _ : Fin n => X)
        (p : Y ⟶ Z.obj), Mono i → Epi p → IsInduced ω f i p ψ := by
    obtain ⟨n, Y, i, p, _, _⟩ := Z.property
    obtain ⟨ψ, hψ⟩ := exists_isInduced ω hf i p
    refine ⟨ψ, fun n' Y' i' p' _ _ => ?_⟩
    obtain ⟨ψ', hψ'⟩ := exists_isInduced ω hf i' p'
    rwa [isInduced_unique ω hf hψ hψ']
  choose ψ hψ using key
  refine ⟨End.of
    { app Z := ModuleCat.ofHom (ψ Z)
      naturality Z Z' g := by
        obtain ⟨n, Y, i, p, _, _⟩ := Z.property
        obtain ⟨n', Y', i', p', _, _⟩ := Z'.property
        ext x
        exact (isInduced_comm ω hf (hψ Z n Y i p inferInstance inferInstance)
          (hψ Z' n' Y' i' p' inferInstance inferInstance) g.hom x).symm }, ?_⟩
  have hι (z : ω.obj X) : (ω.map (biproduct.π (fun _ : Fin 1 => X) 0)).hom
      ((ω.map (biproduct.ι (fun _ : Fin 1 => X) 0)).hom z) = z := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← ω.map_comp, biproduct.ι_π_self,
      ω.map_id, ModuleCat.hom_id, LinearMap.id_apply]
  refine LinearMap.ext fun y => ?_
  simpa [evalSelf_apply] using hψ ⟨X, subquotientHull_self⟩ 1 X
    (biproduct.ι (fun _ : Fin 1 => X) 0) (𝟙 X) inferInstance inferInstance y (f y)
    (fiber_biproduct_ext ω fun k => by
      rw [Fin.fin_one_eq_zero k, map_π_diagonalFiberEnd_apply, hι, hι])

private lemma evalSelf_codRestrict_bijective :
    Function.Bijective ((evalSelf ω X).codRestrict _ (evalSelf_mem ω)) :=
  ⟨fun _ _ h => evalSelf_injective ω (congrArg Subtype.val h),
    fun f => (exists_evalSelf_eq ω f.2).imp fun _ h => Subtype.ext h⟩

variable (X) in
/-- Evaluation at `X` identifies the natural endomorphisms of the restriction of `ω` to the
subquotient hull `⟨X⟩` with the algebra `A_X ⊆ End_R (ω X)`. -/
noncomputable def endSubquotientHullAlgEquiv :
    End ((subquotientHull X).ι ⋙ ω) ≃ₐ[R] fiberEndSubalgebra ω X :=
  AlgEquiv.ofBijective _ (evalSelf_codRestrict_bijective ω)

/-- The algebra isomorphism `endSubquotientHullAlgEquiv` is evaluation at `X`. -/
@[simp]
lemma endSubquotientHullAlgEquiv_apply (η : End ((subquotientHull X).ι ⋙ ω)) :
    (endSubquotientHullAlgEquiv ω X η : Module.End R (ω.obj X)) =
      (η.asHom.app ⟨X, subquotientHull_self⟩).hom := by
  rw [endSubquotientHullAlgEquiv, AlgEquiv.ofBijective_apply, AlgHom.coe_codRestrict,
    evalSelf_apply]

private lemma evalSelf_symm (f : fiberEndSubalgebra ω X) :
    evalSelf ω X ((endSubquotientHullAlgEquiv ω X).symm f) = f := by
  rw [evalSelf_apply, ← endSubquotientHullAlgEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The natural endomorphism of `ω` restricted to `⟨X⟩` determined by an element `f` of `A_X`
acts on `ω (Xⁿ)` by the diagonal endomorphism `f ⊕ ⋯ ⊕ f`. -/
@[simp]
lemma endSubquotientHullAlgEquiv_symm_app_biproduct (f : fiberEndSubalgebra ω X) (n : ℕ) :
    (((endSubquotientHullAlgEquiv ω X).symm f).asHom.app
      ⟨_, subquotientHull_biproduct n⟩).hom = diagonalFiberEnd ω X n f := by
  rw [app_biproduct_eq, evalSelf_symm]

/-- The natural endomorphism of `ω` restricted to `⟨X⟩` determined by an element `f` of `A_X`
acts on a quotient `Y ↠ Z` of a subobject `Y ↪ Xⁿ` through the restriction of
`f ⊕ ⋯ ⊕ f` to `ω Y`. -/
lemma endSubquotientHullAlgEquiv_symm_app_map_apply (f : fiberEndSubalgebra ω X) {n : ℕ}
    {Y Z : C} (i : Y ⟶ ⨁ fun _ : Fin n => X) (p : Y ⟶ Z) [Mono i] [Epi p] {y y₁ : ω.obj Y}
    (h : (ω.map i).hom y₁ = diagonalFiberEnd ω X n f ((ω.map i).hom y)) :
    (((endSubquotientHullAlgEquiv ω X).symm f).asHom.app
      ⟨Z, subquotientHull_of_mono_of_epi i p⟩).hom ((ω.map p).hom y) = (ω.map p).hom y₁ := by
  refine isInduced_app ω _ i p y y₁ ?_
  rw [h, evalSelf_symm]

end EndAlgEquiv

end TauCeti.Tannaka
