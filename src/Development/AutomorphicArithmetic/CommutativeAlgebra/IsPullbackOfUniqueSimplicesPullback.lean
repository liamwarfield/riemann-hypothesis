module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isPullback_of_unique_simplices_pullback :
    ∀ {P A B C : Spc} (t : P ⟶ A) (l : P ⟶ B) (r : A ⟶ C) (u : B ⟶ C), t ≫ r = l ≫ u →
        (∀ (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u → ∃! z : Sx P k T, z.map t = x ∧ z.map l = y) →
        IsPullback t l r u := by
  intro P A B C t l r u hw h
  refine IsPullback.of_forall_isPullback_app (fun n => ?_)
  refine IsPullback.of_forall_isPullback_app (fun T => ?_)
  obtain ⟨⟨k⟩⟩ := n
  obtain ⟨T⟩ := T
  have hw' : ∀ x : Sx P k T, Sx.map r (Sx.map t x) = Sx.map u (Sx.map l x) := by
    intro x
    have := congrArg (fun f : P ⟶ C => (f.app (op ⟨k⟩)).app (op T) x) hw
    simpa [Sx.map] using this
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact hw' x
  · rintro x y ⟨h1, h2⟩
    obtain ⟨z, -, hz⟩ := h k T (Sx.map t (x : Sx P k T)) (Sx.map l (x : Sx P k T)) (hw' x)
    have hx := hz x ⟨rfl, rfl⟩
    have hy := hz y ⟨h1.symm, h2.symm⟩
    exact hx.trans hy.symm
  · intro a b hab
    obtain ⟨z, ⟨h1, h2⟩, -⟩ := h k T a b hab
    exact ⟨z, h1, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.mono_of_injective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Injective (fun x : Sx S k T => x.map f)) → Mono f := by
  intro S S' f hf
  have hm : ∀ n : SimplexCategoryᵒᵖ, Mono (f.app n) := by
    intro n
    have hm' : ∀ T : Schemeᵒᵖ, Mono ((f.app n).app T) := by
      intro T
      rw [mono_iff_injective]
      exact hf n.unop.len T.unop
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app f
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isIso_of_bijective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Bijective (fun x : Sx S k T => x.map f)) → IsIso f := by
  intro S S' f h
  haveI : ∀ n : SimplexCategoryᵒᵖ, IsIso (f.app n) := by
    intro n
    haveI : ∀ T : Schemeᵒᵖ, IsIso ((f.app n).app T) := by
      intro T
      obtain ⟨⟨k⟩⟩ := n
      obtain ⟨T⟩ := T
      rw [isIso_iff_bijective]
      exact h k T
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.simplices_pullback_existsUnique_of_map_eq :
    ∀ {A B C : Spc} (r : A ⟶ C) (u : B ⟶ C) (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u →
        ∃! z : Sx (pullback r u) k T, z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y := by
  intro A B C r u k T x y h
  let F : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk k)) ⋙ (evaluation _ _).obj (op T)
  have hc := isLimitOfHasPullbackOfPreservesLimit F r u
  let e : Sx (pullback r u) k T ≃ Types.PullbackObj (F.map r) (F.map u) :=
    PullbackCone.IsLimit.equivPullbackObj hc
  have e1 : ∀ z : Sx (pullback r u) k T, (e z).1.1 = z.map (pullback.fst r u) := fun z =>
    PullbackCone.IsLimit.equivPullbackObj_apply_fst hc z
  have e2 : ∀ z : Sx (pullback r u) k T, (e z).1.2 = z.map (pullback.snd r u) := fun z =>
    PullbackCone.IsLimit.equivPullbackObj_apply_snd hc z
  have key : ∀ z : Sx (pullback r u) k T,
      z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y ↔ e z = ⟨(x, y), h⟩ := by
    intro z
    constructor
    · rintro ⟨h1, h2⟩
      apply Subtype.ext
      apply Prod.ext
      · exact (e1 z).trans h1
      · exact (e2 z).trans h2
    · intro hz
      refine ⟨(e1 z).symm.trans ?_, (e2 z).symm.trans ?_⟩
      · rw [hz]
      · rw [hz]
  refine ⟨e.symm ⟨(x, y), h⟩, (key _).2 (e.apply_symm_apply _), ?_⟩
  intro z hz
  rw [← (key z).1 hz, e.symm_apply_apply]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Bc

abbrev prodW (W : Scheme.{0}) : Scheme.{0} ⥤ Scheme.{0} := prod.functor.obj W

set_option backward.isDefEq.respectTransparency false in
theorem prodW_compatible (W : Scheme.{0}) :
    CompatiblePreserving Scheme.etaleTopology.{0} (prodW W) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  have hfst : f₁ ≫ prod.fst = f₂ ≫ prod.fst := by
    have h := congrArg (· ≫ (prod.fst : W ⨯ Z ⟶ W)) e
    simpa using h
  have hsnd : (f₁ ≫ prod.snd) ≫ g₁ = (f₂ ≫ prod.snd) ≫ g₂ := by
    have h := congrArg (· ≫ (prod.snd : W ⨯ Z ⟶ Z)) e
    simpa using h
  let u : X ⟶ (prodW W).obj X := prod.lift (f₁ ≫ prod.fst) (𝟙 X)
  have k₁ : f₁ = u ≫ (prodW W).map (f₁ ≫ prod.snd) := by
    apply prod.hom_ext <;> simp [u]
  have k₂ : f₂ = u ≫ (prodW W).map (f₂ ≫ prod.snd) := by
    apply prod.hom_ext <;> simp [u, hfst]
  have hc := hx (f₁ ≫ prod.snd) (f₂ ≫ prod.snd) hg₁ hg₂ hsnd
  calc ℱ.obj.map f₁.op (x g₁ hg₁)
      = ℱ.obj.map u.op (ℱ.obj.map ((prodW W).map (f₁ ≫ prod.snd)).op (x g₁ hg₁)) := by
        rw [← Functor.map_comp_apply, ← op_comp, ← k₁]
    _ = ℱ.obj.map u.op (ℱ.obj.map ((prodW W).map (f₂ ≫ prod.snd)).op (x g₂ hg₂)) :=
        congrArg _ hc
    _ = ℱ.obj.map f₂.op (x g₂ hg₂) := by
        rw [← Functor.map_comp_apply, ← op_comp, ← k₂]

set_option backward.isDefEq.respectTransparency false in
theorem prodW_cover (W : Scheme.{0}) :
    CoverPreserving Scheme.etaleTopology.{0} Scheme.etaleTopology.{0} (prodW W) := by
  constructor
  intro U S hS
  rw [GlobalTheory.T.mem_etale_covering_sieves_iff_points]
  intro u
  obtain ⟨V, j, v, hj, hv, hS'⟩ := (GlobalTheory.T.mem_etale_covering_sieves_iff_points U S).1 hS ((prod.snd : W ⨯ U ⟶ U) u)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := (prod.snd : W ⨯ U ⟶ U)) (g := j) u v hv.symm
  haveI := hj
  refine ⟨pullback (prod.snd : W ⨯ U ⟶ U) j, pullback.fst _ _, z, ?_, hz1, ?_⟩
  · exact MorphismProperty.pullback_fst _ _ hj
  refine ⟨V, j, prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _), hS', ?_⟩
  apply Limits.prod.hom_ext
  · simp
  · simp [pullback.condition]

instance prodW_cont (W : Scheme.{0}) :
    (prodW W).IsContinuous Scheme.etaleTopology.{0} Scheme.etaleTopology.{0} :=
  Functor.isContinuous_of_coverPreserving (prodW_compatible W) (prodW_cover W)

variable (R : Type) [CommRing R]

def pw (W : Scheme.{0}) : Shv R ⥤ Shv R :=
  (prodW W).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) Scheme.etaleTopology.{0} Scheme.etaleTopology.{0}

instance (W : Scheme.{0}) : (pw R W).Additive where
  map_add {F G} {f g} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

variable {R}

abbrev Bc (W : Scheme.{0}) (I : Cx R) : Cx R := ((pw R W).mapHomologicalComplex _).obj I

def Supp (Q : Scheme.{0} → Prop) (P : PSh) : Prop := ∀ U : Scheme.{0}, Nonempty (P.obj (op U)) → Q U

def Acy (Q : Scheme.{0} → Prop) (F : Shv ℤ) : Prop :=
  ∀ P : PSh, Supp Q P → ∀ n : ℤ, 0 < n → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n)

def cl {M F : Shv ℤ} (f : M ⟶ F) : HK ℤ (sgl M) F 0 :=
  CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))

end UpperTheory.Bc
end
end
