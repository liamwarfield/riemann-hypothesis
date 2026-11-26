module

public import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
public import Development.EtaleCohomology.EtaleSheaves.FiltrationLevelBase

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SepClosedPointFilteredEtaleColimit
open CategoryTheory Limits TensorProduct

noncomputable section

namespace UpperTheory.Cb.FilteredPoints

structure Pt (R Ω : Type) [CommRing R] [Field Ω] [Algebra R Ω] where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) R)
  et : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ I)
  ψ : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] Ω

variable {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]

abbrev Pt.A (X : Pt R Ω) : Type := MvPolynomial (Fin X.n) R ⧸ X.I

instance (X : Pt R Ω) : Algebra.Etale R X.A := X.et

theorem exists_pt (E : Type) [CommRing E] [Algebra R E] [Algebra.Etale R E] (ψ : E →ₐ[R] Ω) :
    ∃ (X : Pt R Ω) (e : E ≃ₐ[R] X.A), ∀ x, X.ψ (e x) = ψ x := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType R E)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have het : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ RingHom.ker f) :=
    Algebra.Etale.of_equiv e.symm
  refine ⟨⟨n, RingHom.ker f, het, ψ.comp e.toAlgHom⟩, e.symm, fun x => ?_⟩
  simp

instance : SmallCategory (Pt R Ω) where
  Hom X Y := {f : X.A →ₐ[R] Y.A // ∀ x, Y.ψ (f x) = X.ψ x}
  id X := ⟨AlgHom.id R _, fun _ => rfl⟩
  comp f g := ⟨g.1.comp f.1, fun x => by simp [g.2, f.2]⟩
  id_comp _ := Subtype.ext (AlgHom.ext fun _ => rfl)
  comp_id _ := Subtype.ext (AlgHom.ext fun _ => rfl)
  assoc _ _ _ := Subtype.ext (AlgHom.ext fun _ => rfl)

theorem upper (X Y : Pt R Ω) : ∃ (Z : Pt R Ω) (_ : X ⟶ Z) (_ : Y ⟶ Z), True := by
  have h1 : Algebra.Etale X.A (X.A ⊗[R] Y.A) := Algebra.Etale.baseChange R Y.A X.A
  have h2 : Algebra.Etale R (X.A ⊗[R] Y.A) := Algebra.Etale.comp R X.A _
  obtain ⟨Z, e, he⟩ := exists_pt (X.A ⊗[R] Y.A)
    (Algebra.TensorProduct.lift X.ψ Y.ψ (fun _ _ => Commute.all _ _))
  refine ⟨Z, ⟨e.toAlgHom.comp Algebra.TensorProduct.includeLeft, fun x => ?_⟩,
    ⟨e.toAlgHom.comp Algebra.TensorProduct.includeRight, fun x => ?_⟩, trivial⟩
  · simp [he]
  · simp [he]

theorem coeq {X Y : Pt R Ω} (f g : X ⟶ Y) : ∃ (Z : Pt R Ω) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := X.A)).1
    inferInstance
  let L : X.A ⊗[R] X.A →ₐ[R] Y.A := Algebra.TensorProduct.lift f.1 g.1 (fun _ _ => Commute.all _ _)
  have hcomp : Y.ψ.comp L = X.ψ.comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext
    · ext x; simp [L, f.2]
    · ext x; simp [L, g.2]
  have hs : Y.ψ (L t) = 1 := by
    have := congrArg (fun φ => φ t) hcomp
    simpa [ht1] using this
  have hs' : ∀ x, (g.1 x - f.1 x) * L t = 0 := fun x => by
    have := congrArg L (ht x)
    simpa [L, map_mul, map_sub] using this
  let B := Localization.Away (L t)
  have h1 : Algebra.Etale Y.A B := Algebra.Etale.of_isLocalizationAway (L t)
  have h2 : Algebra.Etale R B := Algebra.Etale.comp R Y.A B
  let ψB : B →ₐ[R] Ω := IsLocalization.Away.liftAlgHom (L t) (f := Y.ψ) (by rw [hs]; exact isUnit_one)
  have hψB : ∀ y, ψB (algebraMap Y.A B y) = Y.ψ y := fun y => by
    simp [ψB]
  obtain ⟨Z, e, he⟩ := exists_pt B ψB
  refine ⟨Z, ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R Y.A B), fun y => ?_⟩, ?_⟩
  · simp [he, hψB]
  · apply Subtype.ext
    apply AlgHom.ext
    intro x
    have hu : IsUnit (algebraMap Y.A B (L t)) := IsLocalization.Away.algebraMap_isUnit (L t)
    have h0 : algebraMap Y.A B (g.1 x - f.1 x) = 0 := by
      apply hu.mul_left_injective
      simp only [zero_mul, ← map_mul, hs' x, map_zero]
    have h3 : algebraMap Y.A B (f.1 x) = algebraMap Y.A B (g.1 x) := by
      have h0' : algebraMap Y.A B (g.1 x) - algebraMap Y.A B (f.1 x) = 0 := by
        rw [← (algebraMap Y.A B).map_sub]
        exact h0
      exact (sub_eq_zero.mp h0').symm
    show e (algebraMap Y.A B (f.1 x)) = e (algebraMap Y.A B (g.1 x))
    rw [h3]

instance : IsFilteredOrEmpty (Pt R Ω) := ⟨upper, fun _ _ => coeq⟩

instance : IsFiltered (Pt R Ω) where
  nonempty := by
    obtain ⟨X, -, -⟩ := exists_pt (R := R) (Ω := Ω) R (Algebra.ofId R Ω)
    exact ⟨X⟩

def D : Pt R Ω ⥤ CommRingCat.{0} where
  obj X := CommRingCat.of X.A
  map f := CommRingCat.ofHom f.1.toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

def tc : Cocone (D (R := R) (Ω := Ω)) where
  pt := CommRingCat.of Ω
  ι :=
    { app := fun X => CommRingCat.ofHom X.ψ.toRingHom
      naturality := fun X Y f => by
        ext x
        exact f.2 x }

theorem cof_step (X : Pt R Ω) (E : Type) [CommRing E] [Algebra X.A E] [Algebra.Etale X.A E]
    (ψ : E →+* Ω) (h : ψ.comp (algebraMap X.A E) = X.ψ.toRingHom) :
    ∃ (Y : Pt R Ω) (g : X ⟶ Y) (φ : E →+* Y.A),
      φ.comp (algebraMap X.A E) = g.1.toRingHom ∧ Y.ψ.toRingHom.comp φ = ψ := by
  letI : Algebra R E := ((algebraMap X.A E).comp (algebraMap R X.A)).toAlgebra
  haveI : IsScalarTower R X.A E := .of_algebraMap_eq' rfl
  haveI : Algebra.Etale R E := Algebra.Etale.comp R X.A E
  let ψ' : E →ₐ[R] Ω :=
    { ψ with
      commutes' := fun r => by
        have := RingHom.congr_fun h (algebraMap R X.A r)
        simpa [IsScalarTower.algebraMap_apply R X.A E] using this }
  obtain ⟨Y, e, he⟩ := exists_pt E ψ'
  refine ⟨Y, ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R X.A E), fun x => ?_⟩,
    e.toAlgHom.toRingHom, rfl, ?_⟩
  · have := RingHom.congr_fun h x
    simpa [he, ψ'] using this
  · ext x
    exact he x

theorem sys (R : CommRingCat.{0}) (p : PrimeSpectrum R) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] (hk : RingHom.ker (algebraMap R Ω) = p.asIdeal) :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
      (u : ∀ j, R ⟶ D.obj j),
      (∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j') ∧ (∀ j, (u j).hom.Etale) ∧
      (∀ j, ∃ q : PrimeSpectrum (D.obj j), q.comap (u j).hom = p) ∧
      ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ LateralTheory.E.LeafSHSysPf.Cof D c := by
  refine ⟨Pt R Ω, inferInstance, inferInstance, D,
    fun X => CommRingCat.ofHom (algebraMap R X.A), ?_, ?_, ?_,
    colimit.cocone D, ⟨colimit.isColimit D⟩, ?_⟩
  · intro j j' g
    ext x
    exact g.1.commutes x
  · intro j
    exact (RingHom.etale_algebraMap (R := R) (S := j.A)).2 j.et
  · intro X
    refine ⟨⟨RingHom.ker X.ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    rw [← hk]
    show X.ψ (algebraMap R X.A x) = 0 ↔ algebraMap R Ω x = 0
    rw [X.ψ.commutes]
  · let ω : (colimit.cocone (D (R := R) (Ω := Ω))).pt →+* Ω := ((colimit.isColimit D).desc tc).hom
    have hω : ∀ X : Pt R Ω, ω.comp ((colimit.cocone D).ι.app X).hom = X.ψ.toRingHom := fun X => by
      have := (colimit.isColimit (D (R := R) (Ω := Ω))).fac tc X
      exact congrArg CommRingCat.Hom.hom this
    refine ⟨Ω, inferInstance, inferInstance, ω, ?_⟩
    intro j E i1 i2 i3 ψ h
    obtain ⟨Y, g, φ, h1, h2⟩ := @cof_step R Ω _ _ _ j E i1 i2 i3 ψ (h.trans (hω j))
    refine ⟨Y, g, φ, h1, ?_⟩
    ext x
    exact (RingHom.congr_fun (hω Y) (φ x)).trans (RingHom.congr_fun h2 x)

theorem closure_inj (K : Type) [Field K] : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
  (algebraMap K (AlgebraicClosure K)).injective

end UpperTheory.Cb.FilteredPoints

theorem UpperTheory.Cb.sepClosed_point_filtered_etale_colimit :
    LateralTheory.E.LeafSHSysPf.LeafRingSys := by
  intro R p
  refine UpperTheory.Cb.FilteredPoints.sys R p (AlgebraicClosure p.asIdeal.ResidueField) ?_
  rw [IsScalarTower.algebraMap_eq R p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField),
    RingHom.ker_comp_of_injective _ (UpperTheory.Cb.FilteredPoints.closure_inj _)]
  exact Ideal.ker_algebraMap_residueField p.asIdeal
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProperGluingExistence
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf
  LateralTheory.E.LeafGlueIsProperPf

namespace UpperTheory.Cb

private lemma ringLift {Q R K : Type} [CommRing Q] [CommRing R] [CommRing K] (j : R →+* K)
    (hj : Function.Injective j) (ψ : Q →+* K) (h : ∀ q, ψ q ∈ j.range) :
    ∃ g : Q →+* R, j.comp g = ψ := by
  let e : R ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b hab => hj (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict j.range h), ?_⟩
  ext q
  change ((e (e.symm (ψ.codRestrict j.range h q)) : j.range) : K) = ψ q
  rw [e.apply_symm_apply]
  rfl

private lemma compat {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (w : CommRingCat.of Ω ⟶ CommRingCat.of S.R) (hw : Spec.map w = S.i₂) :
    ψ.comp (algebraMap Ω Q) = (algebraMap S.R S.K).comp w.hom := by
  have h1 := S.commSq.w
  rw [← hψ, ← hw, Category.assoc, hc, ← Spec.map_comp, ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  ext a
  have h3 := congrArg (fun f => f.hom a) h2
  simpa using h3

private lemma closeSq {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (hR : ∀ q, ψ q ∈ (algebraMap S.R S.K).range) : S.commSq.HasLift := by
  have hinj : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective S.R S.K
  obtain ⟨g, hg⟩ := ringLift (algebraMap S.R S.K) hinj ψ hR
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c i hc S ψ hψ (Spec.preimage S.i₂) hw
  have hgψ : CommRingCat.ofHom g ≫ CommRingCat.ofHom (algebraMap S.R S.K) = CommRingCat.ofHom ψ := by
    rw [← CommRingCat.ofHom_comp, hg]
  refine ⟨⟨⟨Spec.map (CommRingCat.ofHom g) ≫ i, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, ← Spec.map_comp, hgψ, hψ]
  · rw [Category.assoc, hc, ← Spec.map_comp, ← hw]
    congr 1
    ext a
    apply hinj
    have h1 := congrArg (fun f => f a) hcomp
    have h2 := congrArg (fun f => f (algebraMap Ω Q a)) hg
    simp only [RingHom.comp_apply] at h1 h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [h2, h1]

private lemma closedCase {Ω P R K : Type} [Field Ω] [CommRing P] [IsDomain P] [Algebra Ω P]
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (ψ : P →+* K)
    (hω : ψ.comp (algebraMap Ω P) = (algebraMap R K).comp ω)
    (hker : ¬ Function.Injective ψ) (q : P) : ψ q ∈ (algebraMap R K).range := by
  haveI hdim : Ring.KrullDimLE 1 P := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hne : RingHom.ker ψ ≠ ⊥ := fun h => hker ((RingHom.injective_iff_ker_eq_bot ψ).mpr h)
  haveI : (RingHom.ker ψ).IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hne
  letI : Field (P ⧸ RingHom.ker ψ) := Ideal.Quotient.field _
  haveI : Module.Finite Ω (P ⧸ RingHom.ker ψ) :=
    finite_of_finite_type_of_isJacobsonRing Ω (P ⧸ RingHom.ker ψ)
  obtain ⟨p, hmon, hp⟩ : IsIntegral Ω (Ideal.Quotient.mk (RingHom.ker ψ) q) :=
    Algebra.IsIntegral.isIntegral _
  have hpq : Polynomial.aeval q p ∈ RingHom.ker ψ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk Ω,
      ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def]
    exact hp
  rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂, hω,
    ← Polynomial.eval₂_map] at hpq
  have hi : IsIntegral R (ψ q) := ⟨p.map ω, hmon.map ω, hpq⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact ⟨y, hy⟩

private lemma genericVal {Ω L R K : Type} [Field Ω] [Field L] [Algebra Ω L] [CommRing R] [IsDomain R]
    [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (f : L →+* K)
    (h : f.comp (algebraMap Ω L) = (algebraMap R K).comp ω) :
    ∃ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) ∧
      ∀ x ∈ V, f x ∈ (algebraMap R K).range := by
  let V : ValuationSubring L :=
    { (algebraMap R K).range.comap f with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger R (f x) with hx | hx
        · left
          obtain ⟨y, hy⟩ := hx
          exact ⟨y, hy⟩
        · right
          obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          change algebraMap R K y = f x⁻¹
          rw [map_inv₀]
          exact hy }
  refine ⟨V, fun a => ?_, fun x hx => hx⟩
  refine ⟨ω a, ?_⟩
  have h1 := congrArg (fun g => g a) h
  simp only [RingHom.comp_apply] at h1
  exact h1.symm

private lemma chart {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {X : Scheme.{0}}
    (c : X ⟶ Sp Ω) (P Q : Subalgebra Ω L) (iP : Sp P ⟶ X) (iQ : Sp Q ⟶ X)
    (hP : iP ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω P)))
    (hQ : iQ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [IsFractionRing P L]
    (hV : ∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) →
      (P : Set L) ⊆ V ∨ (Q : Set L) ⊆ V)
    (hag : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap P L))) ≫ iP =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ)
    (S : ValuativeCommSq c) (φ : P →+* S.K)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ iP = S.i₁) : S.commSq.HasLift := by
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c iP hP S φ hφ (Spec.preimage S.i₂) hw
  by_cases hinj : Function.Injective φ
  · let f : L →+* S.K := IsFractionRing.lift hinj
    have hf : f.comp (algebraMap P L) = φ :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    have hfΩ : f.comp (algebraMap Ω L) =
        (algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom := by
      rw [IsScalarTower.algebraMap_eq Ω P L, ← RingHom.comp_assoc, hf, hcomp]
    obtain ⟨V, hΩV, hVR⟩ := genericVal (Spec.preimage S.i₂).hom f hfΩ
    rcases hV V hΩV with hPV | hQV
    · refine closeSq c iP hP S φ hφ fun q => ?_
      rw [← hf]
      exact hVR _ (hPV q.2)
    · have hψ : Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ = S.i₁ := by
        rw [← hag S.K f, hf, hφ]
      exact closeSq c iQ hQ S _ hψ fun q => hVR _ (hQV q.2)
  · exact closeSq c iP hP S φ hφ (closedCase hd (Spec.preimage S.i₂).hom φ hcomp hinj)

end UpperTheory.Cb

open UpperTheory.Cb in
theorem UpperTheory.Cb.properGluing_existence :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueExistence := by
  intro Ω L _ _ _ A B u h G S
  obtain ⟨-, -, -, hfA, hfB, -, -, hdA, hdB, hFA, hFB, hadj, hV⟩ := h
  haveI := hfA
  haveI := hfB
  haveI := hFA
  haveI := hFB
  haveI := G.hiA
  haveI := G.hiB
  have hagA : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap A L))) ≫ G.iA =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap B L))) ≫ G.iB := by
    intro K _ f
    have eA : f.comp (algebraMap A L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_A A u)).toRingHom := by
      ext x
      rfl
    have eB : f.comp (algebraMap B L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom := by
      ext x
      rfl
    rw [eA, eB]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, G.agree]
  obtain ⟨x0⟩ : Nonempty (Spec (CommRingCat.of S.K)) := inferInstance
  have hx : S.i₁ x0 ∈ Set.range G.iA ∪ Set.range G.iB := by
    rw [G.cover]
    trivial
  rcases hx with hA | hB
  · have hr : Set.range S.i₁ ⊆ Set.range G.iA := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iA S.i₁ hr
    refine chart G.c0 A B G.iA G.iB G.hcA G.hcB hdA hV hagA S
      (Spec.preimage (IsOpenImmersion.lift G.iA S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
  · have hr : Set.range S.i₁ ⊆ Set.range G.iB := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iB S.i₁ hr
    refine chart G.c0 B A G.iB G.iA G.hcB G.hcA hdB (fun V hV' => (hV V hV').symm)
      (fun K _ f => (hagA K f).symm) S
      (Spec.preimage (IsOpenImmersion.lift G.iB S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SimplicialChainsDegreeZeroInjective
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace UpperTheory.Cb.ConeApexLifts

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

private def top (K : CochainComplex C ℤ) (k : ℤ) (hK : IsZero (K.X (k + 1))) :
    (singleFunctor C k).obj (K.X k) ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) (fun j hj => by
    obtain rfl : j = k + 1 := by simpa using hj.symm
    exact hK.eq_of_tgt _ _)

private lemma top_f (K : CochainComplex C ℤ) (k : ℤ) (hK : IsZero (K.X (k + 1))) :
    (top K k hK).f k = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k (K.X k)).hom := by
  simp only [top, HomologicalComplex.mkHomFromSingle_f, Category.comp_id]

private lemma top_comm {K L : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) :
    (singleFunctor C k).map (φ.f k) ≫ top L k hL = top K k hK ≫ φ := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, top_f, top_f]
  change ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k)).f k ≫ _ = _
  simp only [HomologicalComplex.single_map_f_self, Category.assoc, Iso.cancel_iso_hom_left]
  simp

private lemma ofHom_top_comp {K I : CochainComplex C ℤ} (k : ℤ) (hK : IsZero (K.X (k + 1))) {m q : ℤ}
    (hq : k + m = q) (x : Cochain K I m) :
    (Cochain.ofHom (top K k hK)).comp x (zero_add m) = Cochain.fromSingleMk (x.v k q hq) hq := by
  ext p q' hpq
  by_cases hp : p = k
  · subst hp
    obtain rfl : q' = q := by omega
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.fromSingleMk_v, top_f]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

private def coneTop {K L : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) :
    mappingCone ((singleFunctor C k).map (φ.f k)) ⟶ mappingCone φ :=
  mappingCone.map _ _ (top K k hK) (top L k hL) (top_comm φ k hK hL)

private lemma inl_coneTop {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) {n : ℤ} (z : Cochain (mappingCone φ) I n) :
    (mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp
        ((Cochain.ofHom (coneTop φ k hK hL)).comp z (zero_add n)) (show -1 + n = n - 1 by omega) =
      Cochain.fromSingleMk (((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v k (k + (n - 1)) rfl) rfl := by
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, coneTop, mappingCone.map, mappingCone.inl_desc,
    Cochain.comp_assoc_of_first_is_zero_cochain, ofHom_top_comp k hK rfl]

private lemma inr_coneTop {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) {n : ℤ} (z : Cochain (mappingCone φ) I n) :
    (Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp
        ((Cochain.ofHom (coneTop φ k hK hL)).comp z (zero_add n)) (zero_add n) =
      Cochain.fromSingleMk (((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v k (k + n) rfl) rfl := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, coneTop, mappingCone.map,
    mappingCone.inr_desc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ofHom_top_comp k hL rfl]

open LateralTheory.E.FiltGenPf in
private lemma lift_of_top {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hK : ∀ p, k < p → IsZero (K.X p)) (hL : ∀ p, k < p → IsZero (L.X p))
    (z : Cochain (mappingCone φ) I n)
    (c₀ : Cochain (mappingCone ((singleFunctor C k).map (φ.f k))) I (n - 1))
    (h : (Cochain.ofHom (coneTop φ k (hK _ (by omega)) (hL _ (by omega)))).comp z (zero_add n) =
      δ (n - 1) n c₀) :
    ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (k - 1) n (z - δ (n - 1) n c) := by
  obtain ⟨a, ha⟩ := Cochain.fromSingleMk_surjective
    ((mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp c₀ (show -1 + (n - 1) = n - 1 - 1 by omega))
    (k + (n - 1 - 1)) rfl
  obtain ⟨b, hb⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp c₀ (zero_add (n - 1)))
    (k + (n - 1)) rfl
  have hc : δ (n - 1) n c₀ = mappingCone.descCochain ((singleFunctor C k).map (φ.f k))
      (Cochain.fromSingleMk (a ≫ I.d (k + (n - 1 - 1)) (k + (n - 1)) + n.negOnePow • (φ.f k ≫ b))
        (show k + (n - 1) = k + (n - 1) from rfl))
      (Cochain.fromSingleMk (b ≫ I.d (k + (n - 1)) (k + n)) (show k + n = k + n from rfl)) (by omega) := by
    rw [desc_eta ((singleFunctor C k).map (φ.f k)) (show n - 1 - 1 + 1 = n - 1 by omega) c₀, ← ha, ← hb]
    exact δ_desc_fromSingle k (φ.f k) (show n - 1 + 1 = n by omega) a b (by omega) rfl rfl
  have e1 := inl_coneTop φ k (hK _ (by omega)) (hL _ (by omega)) z
  rw [h, hc, mappingCone.inl_descCochain] at e1
  have e2 := inr_coneTop φ k (hK _ (by omega)) (hL _ (by omega)) z
  rw [h, hc, mappingCone.inr_descCochain] at e2
  have f1 := congrArg (Cochain.fromSingleEquiv (show k + (n - 1) = k + (n - 1) from rfl)) e1
  have f2 := congrArg (Cochain.fromSingleEquiv (show k + n = k + n from rfl)) e2
  simp only [Cochain.fromSingleEquiv_fromSingleMk] at f1 f2
  refine ⟨mappingCone.descCochain φ (Cochain.single a (n - 1 - 1)) (Cochain.single b (n - 1)) (by omega), ?_, ?_⟩
  · intro p q hpq hp
    rcases eq_or_lt_of_le (show k ≤ p by omega) with rfl | hkp
    · obtain rfl : q = k + (n - 1) := by omega
      rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inl_descCochain,
        Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v,
        δ_v (n - 1 - 1) (n - 1) (by omega) _ k (k + (n - 1)) hpq (k + (n - 1 - 1)) (k + 1) (by omega) rfl,
        Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
        Cochain.single_v_eq_zero a _ (k + 1) _ _ (by omega), Cochain.single_v, Cochain.single_v, ← f1]
      simp
    · exact (hK p hkp).eq_of_src _ _
  · intro p q hpq hp
    rcases eq_or_lt_of_le (show k ≤ p by omega) with rfl | hkp
    · obtain rfl : q = k + n := by omega
      rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inr_descCochain,
        Cochain.sub_v,
        δ_v (n - 1) n (by omega) _ k (k + n) hpq (k + (n - 1)) (k + 1) (by omega) rfl,
        Cochain.single_v_eq_zero b _ (k + 1) _ _ (by omega), Cochain.single_v, ← f2]
      simp
    · exact (hL p hkp).eq_of_src _ _

section Host

open AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC LateralTheory.E.DiscLvlPf

variable (R : Type) [CommRing R]

private lemma pull_cone_injective {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (u : K₁ ⟶ K₂) (v : L₁ ⟶ L₂)
    [IsIso u] [IsIso v] (c : φ₁ ≫ v = u ≫ φ₂) (F : Shv R) (n : ℤ) :
    Function.Injective (HK.pull R (mappingCone.map φ₁ φ₂ u v c) F n) := by
  have c' : φ₂ ≫ inv v = inv u ≫ φ₁ := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hT : mappingCone.map φ₂ φ₁ (inv u) (inv v) c' ≫ mappingCone.map φ₁ φ₂ u v c = 𝟙 _ := by
    rw [← mappingCone.map_comp, cone_map_congr R φ₂ φ₂ _ (by rw [Category.id_comp, Category.comp_id])
      (IsIso.inv_hom_id u) (IsIso.inv_hom_id v)]
    exact mappingCone.map_id φ₂
  intro x y hxy
  have := congrArg (HK.pull R (mappingCone.map φ₂ φ₁ (inv u) (inv v) c') F n) hxy
  rwa [← pull_comp', ← pull_comp', hT, pull_id', pull_id'] at this

private def lvl {Z : PSh} {X : Spc} (a : disc.obj Z ⟶ X) : (free R).obj Z ⟶ ((chains R).obj X).X 0 :=
  (e0d R Z).inv ≫ ((chains R).map a).f 0

private lemma lvl_isIso {Z : PSh} {X : Spc} (a : disc.obj Z ⟶ X) (ha : IsIso (a.app (op ⦋0⦌))) :
    IsIso (lvl R a) := by
  have e : lvl R a ≫ (e0 R X).hom = (free R).map (a.app (op ⦋0⦌)) := by
    have := etale_discrete_chains_degree_zero_iso_free_naturality R a
    simp only [lvl, Category.assoc, this]
    exact Iso.inv_hom_id_assoc (e0d R Z) _
  have : IsIso (lvl R a ≫ (e0 R X).hom) := by rw [e]; infer_instance
  exact IsIso.of_isIso_comp_right _ (e0 R X).hom

private lemma lvl_comm {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X) (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X)
    (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g) :
    (free R).map h ≫ lvl R a = lvl R b ≫ ((chains R).map g).f 0 := by
  have e : (free R).map h ≫ (e0d R Z).inv = (e0d R Z').inv ≫ ((chains R).map (disc.map h)).f 0 := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← etale_discrete_simplicial_chains_degree_zero_iso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [lvl, Category.assoc]
  rw [← Category.assoc, e, Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp, comm,
    Functor.map_comp, HomologicalComplex.comp_f]

private lemma sec_chains {Z : PSh} {X : Spc} (a : disc.obj Z ⟶ X) (hX : IsZero (((chains R).obj X).X (0 + 1))) :
    sec R Z ≫ (chains R).map a =
      (singleFunctor (Shv R) 0).map (lvl R a) ≫ top ((chains R).obj X) 0 hX := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, top_f]
  change _ = ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (lvl R a)).f 0 ≫ _
  simp only [sec, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end Host

end UpperTheory.Cb.ConeApexLifts

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
  LateralTheory.E.LeafGhostCut LateralTheory.E.DiscLvlPf UpperTheory.Cb.ConeApexLifts in
theorem UpperTheory.Cb.simplicial_chains_degree_zero_injective :
    LateralTheory.E.t_E3Cut.Coprod → LateralTheory.E.FiltrationLevelBase.Step0 := by
  intro _ R _ F n Z' Z X' X g h a b comm ha hb z hz
  have hK : ∀ p : ℤ, 0 < p → IsZero (((chains R).obj X').X p) := LateralTheory.E.CechFiltPf.chains_isZero R X'
  have hL : ∀ p : ℤ, 0 < p → IsZero (((chains R).obj X).X p) := LateralTheory.E.CechFiltPf.chains_isZero R X
  have hK1 := hK (0 + 1) (by omega)
  have hL1 := hL (0 + 1) (by omega)
  have := lvl_isIso R a ha
  have := lvl_isIso R b hb
  have cT : (singleFunctor (Shv R) 0).map ((free R).map h) ≫ (singleFunctor (Shv R) 0).map (lvl R a) =
      (singleFunctor (Shv R) 0).map (lvl R b) ≫ (singleFunctor (Shv R) 0).map (((chains R).map g).f 0) := by
    rw [← Functor.map_comp, ← Functor.map_comp, lvl_comm R g h a b comm]
  have hsq : mappingCone.map _ _ (sec R Z') (sec R Z) (sec_comm R h) ≫ rmap R g (disc.map h) b a comm =
      mappingCone.map _ _ _ _ cT ≫ coneTop ((chains R).map g) 0 hK1 hL1 := by
    rw [rmap, coneTop, ← mappingCone.map_comp, ← mappingCone.map_comp]
    exact cone_map_congr R _ _ _ _ (sec_chains R b hK1) (sec_chains R a hL1)
  have hz' : HK.pull R (rmap R g (disc.map h) b a comm) F n (CohomologyClass.mk z) = 0 := hz
  have h1 : HK.pull R (coneTop ((chains R).map g) 0 hK1 hL1) F n (CohomologyClass.mk z) = 0 := by
    have h2 := (pull_comp' R (mappingCone.map _ _ (sec R Z') (sec R Z) (sec_comm R h))
      (rmap R g (disc.map h) b a comm) F n (CohomologyClass.mk z)).trans
        ((congrArg _ hz').trans (map_zero _))
    apply pull_cone_injective R _ _ _ _ cT F n
    rw [map_zero]
    exact (pull_comp' R _ _ F n _).symm.trans
      ((congrArg (fun t => HK.pull R t F n (CohomologyClass.mk z)) hsq.symm).trans h2)
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (coneTop ((chains R).map g) 0 hK1 hL1)) z (zero_add n)) = 0 at h1
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨c₀, hc₀⟩ := h1
  obtain ⟨c, hc⟩ := lift_of_top ((chains R).map g) 0 n hK hL
    (z : Cochain (mappingCone ((chains R).map g)) (res R F) n) c₀ hc₀.symm
  have e : (0 : ℤ) - 1 = -1 := by norm_num
  rw [e] at hc
  exact ⟨c, hc⟩
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLineChartsOfHenselianFinite
noncomputable section
open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

namespace UpperTheory.Cb.ChartsOfProjectiveLine

section General

variable {σ : Type*} {R : Type} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem fromSpec_fac {f : R} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.isAffineOpen_basicOpen 𝒜 f hf hm).fromSpec =
      Spec.map (Proj.awayToSection 𝒜 f) ≫ Proj.awayι 𝒜 f hf hm := by
  have h : (Proj.basicOpenIsoSpec 𝒜 f hf hm).hom =
      (Proj.isAffineOpen_basicOpen 𝒜 f hf hm).isoSpec.hom ≫ Spec.map (Proj.awayToSection 𝒜 f) := by
    rw [IsAffineOpen.isoSpec_hom, Proj.basicOpenIsoSpec_hom]
    rfl
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc, ← h,
    Iso.hom_inv_id, Category.id_comp]

private theorem basicOpen_section {f g : R} {m e : ℕ} (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 e) (hm : 0 < m)
    (he : 0 < e) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  have hU := Proj.isAffineOpen_basicOpen 𝒜 f hf hm
  have h1 : hU.fromSpec ⁻¹ᵁ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      hU.fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    rw [hU.fromSpec_preimage_basicOpen, show hU.fromSpec = _ from fromSpec_fac 𝒜 hf hm,
      Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 hf hm hg he,
      SpecMap_preimage_basicOpen]
  have key := congrArg (fun W => hU.fromSpec ''ᵁ W) h1
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, hU.opensRange_fromSpec] at key
  rw [← key]
  exact (inf_eq_right.mpr (Scheme.basicOpen_le _ _)).symm

private theorem res_inf {X : Scheme.{0}} {U V W : X.Opens} (hU : W ≤ U) (hV : W ≤ V) (hW : W = U ⊓ V)
    (x : Γ(X, U)) (y : Γ(X, V))
    (h : X.presheaf.map (homOfLE hU).op x * X.presheaf.map (homOfLE hV).op y = 1) :
    X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op y = 1 := by
  subst hW
  exact h

private theorem away_mul_one {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    awayMap 𝒜 hg (rfl : f * g = f * g) (Away.isLocalizationElem hf hg) *
      awayMap 𝒜 hf (mul_comm f g : f * g = g * f) (Away.isLocalizationElem hg hf) = 1 := by
  rw [awayMap_mk, awayMap_mk]
  apply val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, val_one, Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

private theorem sections_mul_one {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    (Proj 𝒜).presheaf.map (homOfLE (inf_le_left :
        Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)).op
        (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) *
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_right :
        Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 g)).op
        (Proj.awayToSection 𝒜 g (Away.isLocalizationElem hg hf)) = 1 := by
  have e1 := congrArg (fun φ => φ.hom (Away.isLocalizationElem hf hg))
    (Proj.awayMap_awayToSection 𝒜 hg (rfl : f * g = f * g))
  have e2 := congrArg (fun φ => φ.hom (Away.isLocalizationElem hg hf))
    (Proj.awayMap_awayToSection 𝒜 hf (mul_comm f g : f * g = g * f))
  refine res_inf (Proj.basicOpen_mono 𝒜 _ _ ⟨_, rfl⟩)
    (Proj.basicOpen_mono 𝒜 _ _ ⟨_, mul_comm f g⟩) (Proj.basicOpen_mul 𝒜 f g) _ _ ?_
  have e3 := congrArg (Proj.awayToSection 𝒜 (f * g)) (away_mul_one 𝒜 hf hg)
  rw [map_mul, map_one] at e3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  refine Eq.trans ?_ e3
  exact congrArg₂ _ e1.symm e2.symm

private theorem section_surjective {f g : R} {m e : ℕ} (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 e) (hm : 0 < m)
    (h : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 f))
      (Away.isLocalizationElem hf hg))) :
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, Proj.basicOpen 𝒜 f))
      (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg))) := by
  intro y
  obtain ⟨p, hp⟩ := h ((Proj.basicOpenIsoAway 𝒜 f hf hm).inv y)
  refine ⟨p, ?_⟩
  have hy : Proj.awayToSection 𝒜 f ((Proj.basicOpenIsoAway 𝒜 f hf hm).inv y) = y :=
    (Proj.basicOpenIsoAway 𝒜 f hf hm).inv_hom_id_apply y
  rw [← hy, ← hp]
  simp only [Polynomial.coe_eval₂RingHom]
  have := Polynomial.hom_eval₂ p (Int.castRingHom (Away 𝒜 f)) (Proj.awayToSection 𝒜 f).hom
    (Away.isLocalizationElem hf hg)
  rw [show ((Proj.awayToSection 𝒜 f).hom).comp (Int.castRingHom (Away 𝒜 f)) = Int.castRingHom _ from
    RingHom.ext_int _ _] at this
  exact this.symm

private theorem charts_gen {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hcov : Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g = ⊤)
    (h1 : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 f))
      (Away.isLocalizationElem hf hg)))
    (h2 : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 g))
      (Away.isLocalizationElem hg hf))) :
    ∃ (U V : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)) (s' : Γ(Proj 𝒜, V)), IsAffineOpen U ∧ IsAffineOpen V ∧
      U ⊔ V = ⊤ ∧ (Proj 𝒜).basicOpen s = U ⊓ V ∧ (Proj 𝒜).basicOpen s' = U ⊓ V ∧
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
        (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
      Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, U)) s) ∧
      Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, V)) s') :=
  ⟨_, _, Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg),
    Proj.awayToSection 𝒜 g (Away.isLocalizationElem hg hf),
    Proj.isAffineOpen_basicOpen 𝒜 f hf one_pos, Proj.isAffineOpen_basicOpen 𝒜 g hg one_pos, hcov,
    basicOpen_section 𝒜 hf hg one_pos one_pos,
    (basicOpen_section 𝒜 hg hf one_pos one_pos).trans (inf_comm _ _),
    sections_mul_one 𝒜 hf hg, section_surjective 𝒜 hf hg one_pos h1,
    section_surjective 𝒜 hg hf one_pos h2⟩

end General

section Line

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem scale {S : Type} [CommRing S] (φ ψ : MvPolynomial (Fin 2) ℤ →+* S) (c : S)
    (h : ∀ k, ψ (X k) = c * φ (X k)) {n : ℕ} {a : MvPolynomial (Fin 2) ℤ} (ha : a.IsHomogeneous n) :
    ψ a = c ^ n * φ a := by
  have hC : ∀ r : ℤ, ψ (C r) = φ (C r) := fun r => by
    rw [show (C r : MvPolynomial (Fin 2) ℤ) = (r : MvPolynomial (Fin 2) ℤ) from eq_intCast C r,
      map_intCast, map_intCast]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [a.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    by_contra hne
    exact (mem_support_iff.mp hd) (ha.coeff_eq_zero hne)
  rw [monomial_eq, map_mul, map_mul, hC, Finsupp.prod, map_prod, map_prod]
  simp only [map_pow, h, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private abbrev G : ℕ → Submodule ℤ (MvPolynomial (Fin 2) ℤ) := homogeneousSubmodule (Fin 2) ℤ

private theorem X_mem (i : Fin 2) : (X i : MvPolynomial (Fin 2) ℤ) ∈ G 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℤ i)

private theorem surj_away {i j : Fin 2} (hij : j ≠ i) :
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away G (X i)))
      (Away.isLocalizationElem (X_mem i) (X_mem j))) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G (X_mem i) z
  have ha' : a.IsHomogeneous n := by
    have := (mem_homogeneousSubmodule _ _).mp ha
    simpa using this
  let q := Polynomial.eval₂RingHom (Int.castRingHom (Away G (X i)))
    (Away.isLocalizationElem (X_mem i) (X_mem j))
  let D : MvPolynomial (Fin 2) ℤ →+* Polynomial ℤ :=
    (aeval (fun k => if k = i then (1 : Polynomial ℤ) else Polynomial.X)).toRingHom
  let ι : Away G (X i) →+* Localization.Away (X i : MvPolynomial (Fin 2) ℤ) := algebraMap _ _
  let α : MvPolynomial (Fin 2) ℤ →+* Localization.Away (X i : MvPolynomial (Fin 2) ℤ) := algebraMap _ _
  have hX : ∀ k, α (X k) = α (X i) * (ι.comp (q.comp D)) (X k) := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp [D]
    · have hkj : k = j := by omega
      subst hkj
      have hD : D (X k) = Polynomial.X := by simp [D, hk]
      have hq : (ι.comp (q.comp D)) (X k) = ι (Away.isLocalizationElem (X_mem i) (X_mem k)) := by
        simp [hD, q]
      have hsp := IsLocalization.mk'_spec' (Localization.Away (X i : MvPolynomial (Fin 2) ℤ))
        (X k ^ 1 : MvPolynomial (Fin 2) ℤ)
        (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i : MvPolynomial (Fin 2) ℤ))
      have hι : ι (Away.isLocalizationElem (X_mem i) (X_mem k)) =
          IsLocalization.mk' (Localization.Away (X i : MvPolynomial (Fin 2) ℤ))
            (X k ^ 1 : MvPolynomial (Fin 2) ℤ)
            (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i : MvPolynomial (Fin 2) ℤ)) := by
        rw [← Localization.mk_eq_mk']
        rfl
      rw [hq, hι, ← pow_one (α (X k)), ← pow_one (α (X i)), ← map_pow, ← map_pow]
      exact hsp.symm
  have hs := scale (ι.comp (q.comp D)) α (α (X i)) hX ha'
  refine ⟨D a, ?_⟩
  apply val_injective
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  change ι (q (D a)) * α (X i ^ n) = α a
  rw [hs, map_pow, mul_comm]
  rfl

private theorem cover : Proj.basicOpen G (X 0) ⊔ Proj.basicOpen G (X 1) = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top' G (X : Fin 2 → MvPolynomial (Fin 2) ℤ)
    (fun i => ⟨1, X_mem i⟩) (by
      rw [eq_top_iff]
      intro p _
      induction p using MvPolynomial.induction_on with
      | C a => exact Subalgebra.algebraMap_mem _ (⟨C a, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ a)⟩ : G 0)
      | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
      | mul_X p i hp => exact mul_mem (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩))
  rw [eq_top_iff, ← h]
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem intersectionNumber_baseChange : LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated :=
  charts_gen G (X_mem 0) (X_mem 1) cover (surj_away (by decide)) (surj_away (by decide))

end Line

end UpperTheory.Cb.ChartsOfProjectiveLine

theorem UpperTheory.Cb.projectiveLineCharts_of_henselianFinite :
    LateralTheory.E.LZProperCut.LZHensFinite → LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated := fun _ =>
  UpperTheory.Cb.ChartsOfProjectiveLine.intersectionNumber_baseChange
end
end
