/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Action
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# Torsors under a group scheme over a base scheme

Let `G` be a group scheme over a scheme `S`, that is a group object of `Over S`, and let `J` be a
subcanonical topology on schemes, such as the fppf, étale or fpqc topology. The functor of points
`T ↦ Hom_S(T, G)` is a sheaf of groups on the big site `(Over S, J.over S)`, the sheaf of points
of `G`. Torsors under `G` are compared here with torsors under this sheaf of groups, in the sense
of `CategoryTheory.Sheaf.Torsor`, whose isomorphism classes form `Sheaf.NonabelianH1`.

A scheme `P` over `S` with an action of `G` is a `G`-torsor for `J` (Stacks, Definition 78.9.3
(04TY), for schemes in place of algebraic spaces; Poonen, *Rational Points on Varieties*,
§6.5.1) when

* it is a pseudo-torsor: `(g, p) ↦ (g • p, p)` is an isomorphism `G ×_S P ≅ P ×_S P`, and
* it has sections `J`-locally on `S`: the maps `T ⟶ S` which lift to `P` form a `J`-covering
  sieve of `S`.

Over any `T` with a point `p : T ⟶ P`, the torsor becomes trivial,
`G ×_S T ≅ P ×_S T` (`TauCeti.isIso_lift_fst_smul_snd`), so the second condition says that `P`
is `J`-locally trivial.

## Main declarations

* `TauCeti.GroupScheme.pointsSheaf J G`: the sheaf of groups of points of `G` on `Over S`, and
  `TauCeti.GroupScheme.pointsSheafFunctor`, its functoriality in group homomorphisms, which is
  fully faithful.
* `TauCeti.GroupScheme.IsTorsor J G P`: `P` is a `G`-torsor for `J`.
* `TauCeti.GroupScheme.IsTorsor.of_section`: a pseudo-torsor with a section over `S` is a
  torsor; in particular `G` acting on itself is a torsor (`isTorsor_self`).
* `TauCeti.GroupScheme.IsTorsor.of_flat`: a pseudo-torsor which is flat, surjective and locally of
  finite presentation over `S` is an fppf torsor.
* `TauCeti.GroupScheme.IsTorsor.toTorsor`: the functor of points of a `G`-torsor is a torsor
  under the sheaf of points of `G`.
* `TauCeti.GroupScheme.IsTorsor.isIso_of_isModHom`: every equivariant morphism from a torsor to
  a pseudo-torsor is an isomorphism.
* `TauCeti.GroupScheme.IsTorsor.mk_eq_mk_iff`: two torsors have the same class in
  `Sheaf.NonabelianH1 (pointsSheaf J G)` if and only if there is an equivariant morphism between
  them, so passing to the sheaf torsor loses no information on isomorphism classes.
* `TauCeti.GroupScheme.IsTorsor.mk_eq_one_iff`: the class of a torsor is the base point if and
  only if the torsor has a section over `S`.

## References

* [The Stacks project, Definition 78.9.3 (04TY)](https://stacks.math.columbia.edu/tag/04TY)
* [The Stacks project, Lemma 21.4.2 (03AI)](https://stacks.math.columbia.edu/tag/03AI)
* B. Poonen, *Rational Points on Varieties*, Section 6.5.
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj ModObj
open AlgebraicGeometry

namespace TauCeti.GroupScheme

universe u

variable {S : Scheme.{u}} (J : GrothendieckTopology Scheme.{u})

section PointsSheaf

variable [J.Subcanonical] (G : Over S) [GrpObj G]

/-- The sheaf of groups of points of a group scheme `G` over `S` on the big site `Over S`: its
group of sections over `T` is the group of morphisms `T ⟶ G` over `S`, with the group law of `G`.
It is a sheaf because `J` is subcanonical.

The body is exposed because the sections of the sheaf of points are, by definition, morphisms
to `G`: the action of a group scheme on a scheme acts on them through Mathlib's
`CategoryTheory.Hom.mulAction`. -/
@[expose] noncomputable def pointsSheaf : Sheaf (J.over S) GrpCat.{u} where
  obj := yonedaGrpObj G
  property := Presheaf.isSheaf_of_isSheaf_comp _ _ (forget GrpCat.{u})
    ((J.over S).yoneda.obj G).property

lemma pointsSheaf_obj_obj (T : (Over S)ᵒᵖ) :
    (pointsSheaf J G).obj.obj T = GrpCat.of (unop T ⟶ G) :=
  rfl

@[simp]
lemma pointsSheaf_obj_map_apply {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (g : unop T ⟶ G) :
    (pointsSheaf J G).obj.map f g = f.unop ≫ g :=
  rfl

/-- The sheaf of points as a functor from group schemes over `S`: a homomorphism of group schemes
acts on points by composition. The body is exposed, as that of `pointsSheaf`, because the
sections of the image of a group scheme are its points. -/
@[expose] noncomputable def pointsSheafFunctor : Grp (Over S) ⥤ Sheaf (J.over S) GrpCat.{u} :=
  ObjectProperty.lift _ yonedaGrp fun G ↦ (pointsSheaf J G.X).property

lemma pointsSheafFunctor_obj (G : Grp (Over S)) :
    (pointsSheafFunctor J).obj G = pointsSheaf J G.X :=
  rfl

@[simp]
lemma pointsSheafFunctor_map_hom_app_apply {G H : Grp (Over S)} (φ : G ⟶ H) (T : (Over S)ᵒᵖ)
    (g : unop T ⟶ G.X) :
    ((pointsSheafFunctor J).map φ).hom.app T g = g ≫ φ.hom.hom :=
  rfl

/-- The sheaf of points functor is fully faithful: homomorphisms of group schemes over `S` are
the morphisms of their sheaves of points. -/
noncomputable def fullyFaithfulPointsSheafFunctor : (pointsSheafFunctor J (S := S)).FullyFaithful :=
  .ofCompFaithful (G := sheafToPresheaf _ _) yonedaGrpFullyFaithful

end PointsSheaf

section Torsor

variable (G : Over S) [GrpObj G] (P : Over S) [ModObj G P]

/-- A scheme `P` over `S` with an action of the group scheme `G` is a `G`-torsor for the
topology `J` (Stacks, Definition 78.9.3 (04TY)) if `(g, p) ↦ (g • p, p)` is an isomorphism
`G ×_S P ≅ P ×_S P` and `P` has sections `J`-locally on `S`. -/
structure IsTorsor : Prop where
  /-- `P` is a pseudo-torsor: `(g, p) ↦ (g • p, p)` is an isomorphism. -/
  isIso_leftSMul : IsIso (leftSMul G P)
  /-- `P` has sections `J`-locally on `S`: the morphisms to `S` which factor through `P` form a
  `J`-covering sieve of `S`. -/
  generate_singleton_mem : Sieve.generate (Presieve.singleton P.hom) ∈ J S

variable {J G P}

namespace IsTorsor

/-- A pseudo-torsor with a section over `S` is a torsor, for every topology. -/
lemma of_section [IsIso (leftSMul G P)] (x : 𝟙_ (Over S) ⟶ P) : IsTorsor J G P where
  isIso_leftSMul := inferInstance
  generate_singleton_mem := by
    refine J.superset_covering (fun Z f _ ↦ ⟨_, f ≫ x.left, P.hom, ⟨⟩, ?_⟩) (J.top_mem S)
    simp [Over.w x]

/-- A pseudo-torsor which receives a morphism from a torsor is a torsor: it inherits the local
sections. -/
lemma of_hom (h : IsTorsor J G P) {Q : Over S} [ModObj G Q] [IsIso (leftSMul G Q)] (f : P ⟶ Q) :
    IsTorsor J G Q where
  isIso_leftSMul := inferInstance
  generate_singleton_mem := by
    refine J.superset_covering ?_ h.generate_singleton_mem
    rintro Z _ ⟨W, g, -, ⟨⟩, rfl⟩
    exact ⟨_, g ≫ f.left, Q.hom, ⟨⟩, by simp [Over.w f]⟩

/-- A torsor for a topology is a torsor for every finer topology; for instance an étale torsor is
an fppf torsor. -/
lemma of_le (h : IsTorsor J G P) {K : GrothendieckTopology Scheme.{u}} (hJK : J ≤ K) :
    IsTorsor K G P where
  isIso_leftSMul := h.isIso_leftSMul
  generate_singleton_mem := hJK _ h.generate_singleton_mem

/-- A pseudo-torsor which is flat, surjective and locally of finite presentation over `S` is an
fppf torsor: it trivializes itself. -/
lemma of_flat [IsIso (leftSMul G P)] [Flat P.hom] [Surjective P.hom]
    [LocallyOfFinitePresentation P.hom] : IsTorsor Scheme.fppfTopology G P where
  isIso_leftSMul := inferInstance
  generate_singleton_mem :=
    Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage P.hom)

/-- The objects of `Over S` with a morphism to a torsor `P` cover the big site. -/
lemma coversTop (h : IsTorsor J G P) :
    (J.over S).CoversTop fun T : {T : Over S // Nonempty (T ⟶ P)} ↦ T.1 := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ isTerminalTensorUnit,
    GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ h.generate_singleton_mem
  rintro Z f ⟨W, g, -, ⟨⟩, rfl⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨⟨_, ⟨Over.homMk g⟩⟩, ⟨𝟙 _⟩⟩

variable [J.Subcanonical]

/-- The functor of points of a `G`-torsor `P` is a torsor under the sheaf of points of `G`: its
sheaf of sets is the representable sheaf of `P`, on which morphisms to `G` act through the action
of `G` on `P`.

The body is exposed because the sections of this torsor are, by definition, the points of `P`:
statements about its morphisms apply them to morphisms of schemes. -/
@[expose] noncomputable def toTorsor (h : IsTorsor J G P) : Sheaf.Torsor (pointsSheaf J G) where
  sheaf := (J.over S).yoneda.obj P
  mulAction U := Hom.mulAction (M := G) (X := P) (unop U)
  map_smul _ _ f g p := ModObj.comp_smul f.unop g p
  coversTop := h.coversTop
  bijective U := by
    have := h.isIso_leftSMul
    refine ⟨fun ⟨g, p⟩ ⟨g', p'⟩ hgp ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨hg, rfl : p = p'⟩ := Prod.ext_iff.1 hgp
      exact Prod.ext ((smul_left_bijective_of_isIso_leftSMul G p).1 hg) rfl
    · obtain ⟨g, hg⟩ := (smul_left_bijective_of_isIso_leftSMul G y.2).2 y.1
      exact ⟨(g, y.2), Prod.ext hg rfl⟩

@[simp]
lemma toTorsor_sheaf (h : IsTorsor J G P) : h.toTorsor.sheaf = (J.over S).yoneda.obj P :=
  rfl

/-- An equivariant morphism of `G`-torsors induces a morphism of the associated torsors under the
sheaf of points of `G`. -/
noncomputable def toTorsorHom {Q : Over S} [ModObj G Q] (hP : IsTorsor J G P) (hQ : IsTorsor J G Q)
    (f : P ⟶ Q) [IsModHom G f] : hP.toTorsor ⟶ hQ.toTorsor where
  hom := (J.over S).yoneda.map f
  map_smul _ g p := IsModHom.map_smul f g p

@[simp]
lemma toTorsorHom_hom {Q : Over S} [ModObj G Q] (hP : IsTorsor J G P) (hQ : IsTorsor J G Q)
    (f : P ⟶ Q) [IsModHom G f] : (toTorsorHom hP hQ f).hom = (J.over S).yoneda.map f :=
  (rfl)

/-- Every equivariant morphism from a `G`-torsor to a pseudo-torsor under `G` is an
isomorphism. -/
theorem isIso_of_isModHom (h : IsTorsor J G P) {Q : Over S} [ModObj G Q] [IsIso (leftSMul G Q)]
    (f : P ⟶ Q) [IsModHom G f] : IsIso f := by
  have : IsIso ((J.over S).yoneda.map f) := Sheaf.Torsor.isIso_hom (toTorsorHom h (h.of_hom f) f)
  exact isIso_of_fully_faithful (J.over S).yoneda f

/-- A morphism of the torsors under the sheaf of points of `G` associated with two `G`-torsors is
induced by an equivariant morphism of schemes. -/
lemma isModHom_preimage {Q : Over S} [ModObj G Q] {hP : IsTorsor J G P} {hQ : IsTorsor J G Q}
    (φ : hP.toTorsor ⟶ hQ.toTorsor) :
    IsModHom G ((J.over S).yonedaFullyFaithful.preimage φ.hom) where
  smul_hom := by
    set f := (J.over S).yonedaFullyFaithful.preimage φ.hom
    have hf (T : Over S) (p : T ⟶ P) : φ.hom.hom.app (op T) p = p ≫ f := by
      rw [← (J.over S).yonedaFullyFaithful.map_preimage φ.hom]
      rfl
    have key : (fst G P • snd G P) ≫ f = fst G P • (snd G P ≫ f) :=
      (hf _ _).symm.trans ((φ.map_smul _ (fst G P) (snd G P)).trans (congrArg _ (hf _ _)))
    simpa [Hom.smul_def, ← lift_whiskerLeft] using key

/-- Two `G`-torsors have the same class in `Sheaf.NonabelianH1` of the sheaf of points of `G` if
and only if there is an equivariant morphism between them; such a morphism is an isomorphism
(`isIso_of_isModHom`). -/
theorem mk_eq_mk_iff {Q : Over S} [ModObj G Q] (hP : IsTorsor J G P) (hQ : IsTorsor J G Q) :
    Sheaf.NonabelianH1.mk hP.toTorsor = Sheaf.NonabelianH1.mk hQ.toTorsor ↔
      ∃ f : P ⟶ Q, IsModHom G f := by
  refine ⟨fun h ↦ ?_, fun ⟨f, _⟩ ↦ Sheaf.NonabelianH1.mk_eq_mk_of_hom (toTorsorHom hP hQ f)⟩
  obtain ⟨e⟩ := Sheaf.NonabelianH1.mk_eq_mk_iff.1 h
  exact ⟨_, isModHom_preimage e.hom⟩

/-- The class of a `G`-torsor is the base point of `Sheaf.NonabelianH1` of the sheaf of points of
`G` if and only if the torsor has a section over `S`. This is Stacks, Lemma 21.4.2 (03AI), for the
sheaf torsor of points of `P`, whose global sections are the sections of `P` over `S`. -/
theorem mk_eq_one_iff (h : IsTorsor J G P) :
    Sheaf.NonabelianH1.mk h.toTorsor = 1 ↔ Nonempty (𝟙_ (Over S) ⟶ P) := by
  rw [Sheaf.NonabelianH1.mk_eq_one_iff]
  refine ⟨fun ⟨s, _⟩ ↦ ⟨s (op (𝟙_ (Over S)))⟩, fun ⟨x⟩ ↦ ⟨fun U ↦ toUnit (unop U) ≫ x, ?_⟩⟩
  intro U V f
  exact (Category.assoc f.unop _ x).symm.trans (by rw [comp_toUnit])

end IsTorsor

attribute [local instance] ModObj.regular in
/-- A group scheme acting on itself by left multiplication is a torsor, the trivial torsor. -/
lemma isTorsor_self (G : Over S) [GrpObj G] : IsTorsor J G G :=
  have : IsIso (leftSMul G G) := (isIso_leftSMul_iff (M := G) (X := G)).2 fun T x y ↦
    ⟨y * x⁻¹, by simp, fun g hg ↦ by rw [← hg]; simp⟩
  .of_section (P := G) η[G]

end Torsor

end TauCeti.GroupScheme
