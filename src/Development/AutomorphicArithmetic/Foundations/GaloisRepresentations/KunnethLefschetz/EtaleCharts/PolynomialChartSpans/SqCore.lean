module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ProjProd
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsHomogeneousGeneratorsIdealSheafClosedImmer
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsBlowupAffineChartCoverOfSpanEq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowOfBl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowBC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.RestrictMemNonZeroDivisorsOfIsAffineOpen
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen :
    ∀ {W : Scheme.{0}} {V O : W.Opens}, IsAffineOpen V → ∀ (h : O ≤ V) (t : Γ(W, V)), t ∈ nonZeroDivisors Γ(W, V) →
        W.presheaf.map (homOfLE h).op t ∈ nonZeroDivisors Γ(W, O) := by
  intro W V O hV h t ht
  rw [mem_nonZeroDivisors_iff_right] at ht ⊢
  intro s hs
  refine TopCat.Presheaf.section_ext W.sheaf O s 0 (fun x hx => ?_)
  rw [map_zero]
  have hxV : x ∈ V := h hx
  algebraize [(W.presheaf.germ V x hxV).hom]
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have hloc := IsLocalization.nonZeroDivisors_le_comap (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (W.presheaf.stalk x) (mem_nonZeroDivisors_iff_right.mpr ht)
  rw [Submonoid.mem_comap, RingHom.algebraMap_toAlgebra, mem_nonZeroDivisors_iff_right] at hloc
  apply hloc
  have e := congrArg (W.presheaf.germ O x hx).hom hs
  rw [map_mul, map_zero, TopCat.Presheaf.germ_res_apply] at e
  exact e
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.IsUnitChartCoordAndHomogeneousChartTransition
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projective_chart_overlap {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N)
    (O : W.Opens) (a b : Fin (N + 1))
    (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))
    (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b))
    (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F ∈ grading R N (n • 1)) :
    h.appLE _ O ha (chartHom a F) *
        h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
      h.appLE _ O hb (chartHom b F) := by
  have hO : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b * X a) := by
    rw [Proj.basicOpen_mul]
    exact fun x hx => ⟨hb hx, ha hx⟩
  have e1 : h.appLE _ O ha =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_right a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have e2 : h.appLE _ O hb =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_left a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have hF' : F ∈ grading R N n := by simpa using hF
  rw [e1, e2]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [chartHom_of_mem a hF']
  exact map_mul_pow_eq _ _ (chart_identity a b hF)

theorem UpperTheory.isUnit_chart_coord_and_homogeneous_chart_transition :
    ∀ {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N) (O : W.Opens) (a b : Fin (N + 1))
        (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b)),
        IsUnit (h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R))) ∧
        ∀ (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R), F.IsHomogeneous n →
          h.appLE _ O ha (chartHom a F) * h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
            h.appLE _ O hb (chartHom b F) := by
  intro R _ N W h O a b ha hb
  refine ⟨?_, fun n F hF => projective_chart_overlap h O a b ha hb n F ?_⟩
  · have key := projective_chart_overlap h O a b ha hb 1 (X b) (by simpa using X_mem b)
    rw [pow_one, chartHom_X_self, map_one] at key
    exact IsUnit.of_mul_eq_one_right _ key
  · have : F ∈ grading R N n := hF
    simpa using this
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.SectionsGeneratedOverAffineProductCover
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem UpperTheory.sections_generated_over_affine_product_cover :
    ∀ {S Z P W : Scheme.{0}} [IsAffine S] (p : Z ⟶ S) (q : P ⟶ S) (π : W ⟶ Z) (f : W ⟶ P)
        (h : π ≫ p = f ≫ q) {α β : Type} (U : α → Z.Opens) (D : β → P.Opens),
        (∀ a, IsAffineOpen (U a)) → (∀ b, IsAffineOpen (D b)) → iSup U = ⊤ → iSup D = ⊤ →
        ∀ (V : α → β → W.Opens), (∀ a b, IsAffineOpen (V a b)) →
        ∀ (eV : ∀ a b, V a b = π ⁻¹ᵁ U a ⊓ f ⁻¹ᵁ D b),
        (∀ a b (s : Γ(W, V a b)), s ∈ Subring.closure
          (Set.range (π.appLE (U a) (V a b) ((eV a b).le.trans inf_le_left)).hom ∪
           Set.range (f.appLE (D b) (V a b) ((eV a b).le.trans inf_le_right)).hom)) →
        IsClosedImmersion (pullback.lift π f h : W ⟶ pullback p q) := by
  intro S Z P W _ p q π f h α β U D hU hD hUc hDc V hV eV hgen
  set L : W ⟶ pullback p q := pullback.lift π f h with hL
  let Wt : α × β → (pullback p q).Opens := fun i =>
    pullback.fst p q ⁻¹ᵁ U i.1 ⊓ pullback.snd p q ⁻¹ᵁ D i.2
  have hcov : iSup Wt = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx1 : pullback.fst p q x ∈ iSup U := by rw [hUc]; trivial
    have hx2 : pullback.snd p q x ∈ iSup D := by rw [hDc]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx1
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hx2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(a, b), ⟨ha, hb⟩⟩
  have hWt : ∀ i, IsAffineOpen (Wt i) := by
    intro i
    haveI : IsAffine (U i.1) := hU i.1
    haveI : IsAffine (D i.2) := hD i.2
    let m := pullback.map ((U i.1).ι ≫ p) ((D i.2).ι ≫ q) p q (U i.1).ι (D i.2).ι (𝟙 S)
      (by simp) (by simp)
    have hm : m.opensRange = Wt i := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      rfl
    rw [← hm]
    exact isAffineOpen_opensRange m
  have hpre : ∀ i, L ⁻¹ᵁ Wt i = V i.1 i.2 := by
    intro i
    rw [eV, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hL,
      pullback.lift_fst, pullback.lift_snd]
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) Wt hcov]
  rintro ⟨a, b⟩
  have aux : ∀ (Vo : W.Opens) (h1 : Vo ≤ π ⁻¹ᵁ U a) (h2 : Vo ≤ f ⁻¹ᵁ D b), Vo = V a b →
      ∀ s : Γ(W, Vo), s ∈ Subring.closure (Set.range (π.appLE (U a) Vo h1).hom ∪
        Set.range (f.appLE (D b) Vo h2).hom) := by
    rintro Vo h1 h2 rfl s
    exact hgen a b s
  have e1 : L ⁻¹ᵁ Wt (a, b) ≤ π ⁻¹ᵁ U a := by
    rw [hpre (a, b)]; exact (eV a b).le.trans inf_le_left
  have e2 : L ⁻¹ᵁ Wt (a, b) ≤ f ⁻¹ᵁ D b := by
    rw [hpre (a, b)]; exact (eV a b).le.trans inf_le_right
  have hsurj : Function.Surjective (L.app (Wt (a, b))) := by
    intro y
    have hy := aux _ e1 e2 (hpre (a, b)) y
    have hle : Set.range (π.appLE (U a) _ e1).hom ∪ Set.range (f.appLE (D b) _ e2).hom ⊆
        ((L.app (Wt (a, b))).hom.range : Set _) := by
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · refine ⟨(pullback.fst p q).appLE (U a) (Wt (a, b)) inf_le_left x, ?_⟩
        rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        simp only [hL, pullback.lift_fst]
      · refine ⟨(pullback.snd p q).appLE (D b) (Wt (a, b)) inf_le_right x, ?_⟩
        rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        simp only [hL, pullback.lift_snd]
    exact (Subring.closure_le.mpr hle) hy
  haveI : IsAffine (Wt (a, b)) := hWt (a, b)
  have hA : IsAffineOpen (L ⁻¹ᵁ Wt (a, b)) := by rw [hpre (a, b)]; exact hV a b
  haveI : IsAffine (L ⁻¹ᵁ Wt (a, b)) := hA
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [morphismRestrict_appTop]
  have hs2 : Function.Surjective (L.app ((Wt (a, b)).ι ''ᵁ ⊤)) := by
    rw [Scheme.Opens.ι_image_top]
    exact hsurj
  have comp_surj : ∀ {A B C : CommRingCat} (u : A ⟶ B) (v : B ⟶ C) [IsIso v],
      Function.Surjective u → Function.Surjective (u ≫ v) := by
    intro A B C u v _ hu y
    obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso v).2 y
    obtain ⟨w, rfl⟩ := hu z
    exact ⟨w, by simp⟩
  have isoE : ∀ {A B : W.Opens} (e : A = B), IsIso (W.presheaf.map (eqToHom e).op) := by
    intro A B e
    subst e
    rw [eqToHom_refl, op_id, W.presheaf.map_id]
    infer_instance
  refine @comp_surj _ _ _ _ _ (isoE _) hs2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.OKDvr
theorem UpperTheory.Gal.KunnethLefschetz.G.oKDvr :
    UpperTheory.Gal.KunnethLefschetz.G.OKDvr := by
  intro l _ K _
  have hK : (CrystallineSemistableComparison.OK l K) = (integralClosure ℤ_[l] K).toSubring := by
    ext x
    constructor
    · intro hx
      have h1 : ‖(x : PadicAlgCl l)‖ ≤ 1 := hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := UpperTheory.V.Lib.Small.isIntegral_of_norm_le h1
      exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 h2
    · intro hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := IsIntegral.map (K.val.restrictScalars ℤ_[l]) hx
      exact UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l _ h2
  rw [hK]
  exact (IsIntegralClosure.isNoetherianRing ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SubstXZero
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Etale)
    (σ : Type) : (MvPolynomial.map (σ := σ) φ).Etale := by
  algebraize [φ]
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := A) (S := B)
  have h : Algebra.IsPushout A (MvPolynomial σ A) B (MvPolynomial σ B) := inferInstance
  haveI := h.symm
  exact RingHom.Etale.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) hφ

private theorem etale_open {R : Type} [CommRing R] (U : (Spec (CommRingCat.of R)).Opens)
    (hU : IsAffineOpen U) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of R))) ⊤ U le_top).hom.Etale := by
  have h0 : (Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of R))) ⊤ U le_top).hom.Etale :=
    HasRingHomProperty.appLE @Etale (𝟙 _) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  exact RingHom.Etale.respectsIso.right _
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h0

private def subst (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    MvPolynomial (Fin (D + 1)) O →+* MvPolynomial (Fin D) O :=
  (MvPolynomial.aeval (Fin.cons (MvPolynomial.C ϖ) MvPolynomial.X :
    Fin (D + 1) → MvPolynomial (Fin D) O)).toRingHom

private theorem subst_C (O : Type) [CommRing O] (ϖ : O) (D : ℕ) (r : O) :
    subst O ϖ D (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [subst]

private theorem subst_X_zero (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    subst O ϖ D (MvPolynomial.X 0) = MvPolynomial.C ϖ := by
  simp [subst]

private theorem subst_X_succ (O : Type) [CommRing O] (ϖ : O) (D : ℕ) (i : Fin D) :
    subst O ϖ D (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [subst]

private theorem prod_first (O : Type) [CommRing O] (D : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1), MvPolynomial.X i) =
      (MvPolynomial.X 0 : MvPolynomial (Fin (D + 1)) O) := by
  have h : Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1) = {0} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact Fin.ext (by simp only [Fin.val_zero]; omega)
    · rintro rfl
      exact ⟨Finset.mem_univ _, by simp only [Fin.val_zero]; omega⟩
  rw [h, Finset.prod_singleton]

private def modelEquiv (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    (MvPolynomial (Fin (D + 1)) O ⧸ Ideal.span (Set.singleton
      ((∏ i ∈ Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1),
        MvPolynomial.X i) - MvPolynomial.C ϖ))) ≃+* MvPolynomial (Fin D) O :=
  RingEquiv.ofRingHom
    (Ideal.Quotient.lift _ (subst O ϖ D) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [prod_first, map_mul, map_sub, subst_X_zero, subst_C, sub_self, mul_zero]))
    ((Ideal.Quotient.mk _).comp (MvPolynomial.rename Fin.succ).toRingHom)
    (by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [subst_C]
      · simp [subst_X_succ])
    (by
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
      · simp [subst_C]
      · refine Fin.cases ?_ (fun j => ?_) i
        · simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, subst_X_zero, RingHom.id_apply]
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_C]
          refine (Ideal.Quotient.eq.mpr ?_).symm
          rw [prod_first]
          exact Ideal.mem_span_singleton_self _
        · simp [subst_X_succ])

theorem smSst : SmSst := by
  intro O _ ϖ X p _ x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth p x
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  have hf := etale_open (R := O) U hU
  refine ⟨V, hV, hx, n + 1, 1, le_rfl, by omega,
    (g.comp (MvPolynomial.map ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top).hom)).comp
        (modelEquiv O ϖ n).toRingHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (modelEquiv O ϖ n).bijective)
      (RingHom.Etale.stableUnderComposition _ _ (etale_map _ hf _) hg)
  · refine RingHom.ext fun r => ?_
    have e1 : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top ≫
        Scheme.Hom.appLE p U V e = Scheme.Hom.appLE p ⊤ V le_top := by
      refine (Scheme.Hom.appLE_comp_appLE p (𝟙 _) ⊤ U V le_top e).trans ?_
      simp
    have e2 := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom r)) e1
    have e3 := RingHom.congr_fun hgC (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top).hom r)
    have e4 : (modelEquiv O ϖ n) (algebraMap O _ r) = MvPolynomial.C r := subst_C O ϖ n r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e4, MvPolynomial.map_C]
    exact e3.trans e2

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpTop
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CrossOfRel
noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.Gal.KunnethLefschetz.G

private lemma cross_of_rel {A : Type*} [CommRing A] {T T' b Cl Ck Dl Dk : A} (hT : T ∈ nonZeroDivisors A)
    (hT' : T' ∈ nonZeroDivisors A) (hb : IsUnit b) {n : ℕ}
    (hl : T * Cl * b ^ n = T' * Dl) (hk : T * Ck * b ^ n = T' * Dk) :
    Cl * Dk = Ck * Dl := by
  have h0 : (Cl * Dk - Ck * Dl) * (T * T' * b ^ n) = 0 := by
    linear_combination (T' * Dk) * hl - (T' * Dl) * hk
  have hu : T * T' * b ^ n ∈ nonZeroDivisors A :=
    mul_mem (mul_mem hT hT') (hb.pow n).mem_nonZeroDivisors
  exact sub_eq_zero.1 ((mul_right_mem_nonZeroDivisors_eq_zero_iff hu).1 h0)

theorem blEmb : BlowUpEmbedding := by
  intro R _ _ Z W p hp I π hπ
  obtain ⟨N, i, hi, rfl⟩ := hp
  obtain ⟨n, M, F, hF, hgen⟩ := UpperTheory.exists_homogeneous_generators_idealSheaf_closedImmersion i I
  have hU : ∀ a : Fin (N + 1), IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :=
    fun a => (isAffineOpen_stdOpen a).preimage i
  let U : Fin (N + 1) → Z.affineOpens := fun a => ⟨_, hU a⟩
  let g : ∀ a, Fin (M + 1) → Γ(Z, (U a).1) := fun a m => i.appLE _ _ le_rfl (chartHom a (F m))
  choose V le c hVa hVc hc1 hc2 hc3 hc4 hc5 using
    fun a => UpperTheory.exists_blowup_affine_chart_cover_of_span_eq I π hπ (U a) (g a) (hgen a (hU a))
  have hle : ∀ a m, V a m ≤ (π ≫ i) ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) := le
  have key : ∀ a m (O : W.Opens) (hO : O ≤ V a m) l,
      W.presheaf.map (homOfLE hO).op (π.appLE _ _ (le a m) (g a l)) =
        (π ≫ i).appLE _ O (hO.trans (hle a m)) (chartHom a (F l)) := by
    intro a m O hO l
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    simp only [g]
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hcross : ∀ (x y : Fin (N + 1) × Fin (M + 1)) (l k : Fin (M + 1)),
      W.presheaf.map (homOfLE (inf_le_left : V x.1 x.2 ⊓ V y.1 y.2 ≤ V x.1 x.2)).op (c x.1 x.2 l) *
        W.presheaf.map (homOfLE (inf_le_right : V x.1 x.2 ⊓ V y.1 y.2 ≤ V y.1 y.2)).op (c y.1 y.2 k) =
      W.presheaf.map (homOfLE (inf_le_left : V x.1 x.2 ⊓ V y.1 y.2 ≤ V x.1 x.2)).op (c x.1 x.2 k) *
        W.presheaf.map (homOfLE (inf_le_right : V x.1 x.2 ⊓ V y.1 y.2 ≤ V y.1 y.2)).op (c y.1 y.2 l) := by
    rintro ⟨a, m⟩ ⟨b, m'⟩ l k
    dsimp only
    have h1 : V a m ⊓ V b m' ≤ V a m := inf_le_left
    have h2 : V a m ⊓ V b m' ≤ V b m' := inf_le_right
    obtain ⟨hu, hrel⟩ := UpperTheory.isUnit_chart_coord_and_homogeneous_chart_transition (π ≫ i) (V a m ⊓ V b m') a b (h1.trans (hle a m)) (h2.trans (hle b m'))
    have e1 : ∀ l, (π ≫ i).appLE _ _ (h1.trans (hle a m)) (chartHom a (F l)) =
        W.presheaf.map (homOfLE h1).op (π.appLE _ _ (le a m) (g a m)) *
          W.presheaf.map (homOfLE h1).op (c a m l) := fun l => by
      rw [← key a m _ h1 l, hc1, map_mul]
    have e2 : ∀ l, (π ≫ i).appLE _ _ (h2.trans (hle b m')) (chartHom b (F l)) =
        W.presheaf.map (homOfLE h2).op (π.appLE _ _ (le b m') (g b m')) *
          W.presheaf.map (homOfLE h2).op (c b m' l) := fun l => by
      rw [← key b m' _ h2 l, hc1, map_mul]
    have r : ∀ l, W.presheaf.map (homOfLE h1).op (π.appLE _ _ (le a m) (g a m)) *
          W.presheaf.map (homOfLE h1).op (c a m l) *
          (π ≫ i).appLE _ _ (h2.trans (hle b m')) (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
        W.presheaf.map (homOfLE h2).op (π.appLE _ _ (le b m') (g b m')) *
          W.presheaf.map (homOfLE h2).op (c b m' l) := fun l => by
      rw [← e1, ← e2]; exact hrel n (F l) (hF l)
    exact cross_of_rel (UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen (hVa a m) h1 _ (hc3 a m))
      (UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen (hVa b m') h2 _ (hc3 b m')) hu (r l) (r k)
  have hcov : iSup (fun x : Fin (N + 1) × Fin (M + 1) => V x.1 x.2) = ⊤ := by
    rw [iSup_prod]
    simp_rw [hVc]
    change ⨆ a, (π ≫ i) ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X]
    rfl
  obtain ⟨f, hfs, hf⟩ := UpperTheory.cech_cocycle_line_bundle (π ≫ i ≫ PSpace.str R N) M
    (fun x : Fin (N + 1) × Fin (M + 1) => V x.1 x.2) hcov (fun x => x.2) (fun x => c x.1 x.2)
    (fun x => hc2 x.1 x.2) hcross
  choose hD hcoord using hf
  have hpf : ∀ a m m', W.basicOpen (c a m' m) = V a m' ⊓ f ⁻¹ᵁ (Proj.basicOpen (grading R M) (X m') ⊓
      Proj.basicOpen (grading R M) (X m)) := by
    intro a m m'
    rw [← hcoord (a, m') m, Scheme.basicOpen_appLE, basicOpen_chartHom_X]
  have eV : ∀ a m, V a m = π ⁻¹ᵁ (U a).1 ⊓ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X m) := by
    intro a m
    refine _root_.le_antisymm (le_inf (le a m) (hD (a, m))) ?_
    rintro w ⟨hw1, hw2⟩
    have hw : w ∈ iSup (V a) := by rw [hVc]; exact hw1
    obtain ⟨m', hm'⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
    have hb : w ∈ W.basicOpen (c a m' m) := by
      rw [hpf]
      exact ⟨hm', hD (a, m') hm', hw2⟩
    rw [← hc5] at hb
    exact hb.2
  have cU : iSup (fun a => (U a).1) = ⊤ := by
    change ⨆ a, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X]
    rfl
  refine ⟨M, f, hfs.symm, UpperTheory.sections_generated_over_affine_product_cover (i ≫ PSpace.str R N) (PSpace.str R M) π f hfs.symm
    (fun a => (U a).1) (fun m => Proj.basicOpen (grading R M) (X m)) (fun a => hU a)
    (fun m => isAffineOpen_stdOpen m) cU iSup_basicOpen_X V hVa eV ?_⟩
  intro a m s
  obtain ⟨P, rfl⟩ := hc4 a m s
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [coe_eval₂Hom, eval₂_C]
    exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact add_mem hp hq
  | mul_X p l hp =>
    rw [map_mul, coe_eval₂Hom, eval₂_X]
    exact mul_mem hp (Subring.subset_closure (Or.inr ⟨chartHom m (X l), hcoord (a, m) l⟩))

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpSmooth
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BCoord
open CategoryTheory Limits MvPolynomial

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_chart {A E B : Type} [CommRing A] [CommRing E] [CommRing B] {D : ℕ}
    (p : A →+* E) (ψ : E →+* B) (s : Fin D → E) (y : Fin D → B) (j : Fin D)
    (hφ : (eval₂Hom p s).Etale)
    (surj : Function.Surjective (eval₂Hom ψ y))
    (ker : RingHom.ker (eval₂Hom ψ y) = Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k))) :
    (eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))).Etale := by
  classical
  let γ := eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))
  let Z : Fin D → MvPolynomial (Fin D) A := Function.update X j 1
  let α' : MvPolynomial (ULift.{0} (Fin D)) A →+* E := eval₂Hom p (fun k => s k.down)
  let β' : MvPolynomial (ULift.{0} (Fin D)) A →+* MvPolynomial (Fin D) A :=
    eval₂Hom C (fun k => X j * Z k.down)
  have hα' : α'.Etale := by
    have e1 : α' = (eval₂Hom p s).comp
        (MvPolynomial.renameEquiv A Equiv.ulift).toRingEquiv.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [α']
      · intro k
        simp [α']
    rw [e1]
    exact RingHom.Etale.respectsIso.2 _ _ hφ
  have hker : ∀ q ∈ Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => C (s k) - C (s j) * X k)), eval₂Hom ψ y q = 0 := by
    intro q hq
    rw [← ker] at hq
    exact hq
  have hyj : y j = 1 := by
    have h0 := hker _ (Ideal.subset_span (Set.mem_insert _ _))
    simp only [map_sub, eval₂Hom_X', map_one] at h0
    exact sub_eq_zero.1 h0
  have hyk : ∀ k, ψ (s k) = ψ (s j) * y k := by
    intro k
    have h0 := hker _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩))
    simp only [map_sub, map_mul, eval₂Hom_C, eval₂Hom_X'] at h0
    exact sub_eq_zero.1 h0
  have hγX : ∀ k, k ≠ j → γ (X k) = y k := by
    intro k hk
    simp [γ, Function.update_of_ne hk]
  have hγXj : γ (X j) = ψ (s j) := by simp [γ]
  have hγZ : ∀ k, γ (X j * Z k) = ψ (s k) := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp [Z, hγXj]
    · rw [map_mul, hγXj]
      simp only [Z, Function.update_of_ne hk]
      rw [hγX k hk, hyk k]
  have hcompat : ∀ t, ψ (α' t) = γ (β' t) := by
    intro t
    have h0 : ψ.comp α' = γ.comp β' := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [α', β', γ]
      · intro k
        simp only [RingHom.comp_apply, α', β', eval₂Hom_X']
        exact (hγZ k.down).symm
    exact RingHom.congr_fun h0 t
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) E := α'.toAlgebra
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) := β'.toAlgebra
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) B := (γ.comp β').toAlgebra
  have hbc := RingHom.Etale.isStableUnderBaseChange.tensorProduct (MvPolynomial (Fin D) A)
    (R := MvPolynomial (ULift.{0} (Fin D)) A) (S := E) hα'
  let fA : MvPolynomial (Fin D) A →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B :=
    { γ with commutes' := fun _ => rfl }
  let gA : E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B :=
    { ψ with commutes' := fun t => hcompat t }
  let F := (Algebra.TensorProduct.lift fA gA (fun _ _ => Commute.all _ _)).toRingHom
  have hF : ∀ a e, F (TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a e) = γ a * ψ e := by
    intro a e
    simp [F, fA, gA]
  have hT : ∀ t, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (α' t) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (β' t) (1 : E) := by
    intro t
    have h1 : α' t = t • (1 : E) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    have h2 : β' t = t • (1 : MvPolynomial (Fin D) A) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  have hTs : ∀ k, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (X j * Z k) (1 : E) := by
    intro k
    simpa [α', β'] using hT (X ⟨k⟩)
  let G0 : MvPolynomial (Fin D) E →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E :=
    eval₂Hom (Algebra.TensorProduct.includeRight :
      E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E).toRingHom (fun k => TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E))
  have hG0C : ∀ e, G0 (C e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e := by
    intro e
    simp [G0]
  have hG0X : ∀ k, G0 (X k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E) := by
    intro k
    simp [G0]
  have hG0 : RingHom.ker (eval₂Hom ψ y) ≤ RingHom.ker G0 := by
    rw [ker, Ideal.span_le]
    rintro q (rfl | ⟨k, rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hG0X]
      simp [Z, Algebra.TensorProduct.one_def]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hG0C, hG0C, hG0X,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hTs k]
      have h3 : TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (s j) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E) * TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s j) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h3, hTs j, Algebra.TensorProduct.tmul_mul_tmul]
      simp [Z, mul_comm]
  let G : B →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E :=
    (Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq)).comp
      (RingHom.quotientKerEquivOfSurjective surj).symm.toRingHom
  have hG : ∀ q, G (eval₂Hom ψ y q) = G0 q := by
    intro q
    have h4 : (RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q)
        = Ideal.Quotient.mk _ q := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq)
      ((RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q)) = G0 q
    rw [h4]
    rfl
  have hGψ : ∀ e, G (ψ e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e := by
    intro e
    rw [← eval₂Hom_C ψ y e, hG, hG0C]
  have hFG : F.comp G = RingHom.id B := by
    have h5 : F.comp G0 = eval₂Hom ψ y := by
      apply MvPolynomial.ringHom_ext
      · intro e
        rw [RingHom.comp_apply, hG0C, hF, map_one, one_mul, eval₂Hom_C]
      · intro k
        rw [RingHom.comp_apply, hG0X, hF, map_one, mul_one, eval₂Hom_X']
        by_cases hk : k = j
        · subst hk
          simp [Z, hyj]
        · simp only [Z, Function.update_of_ne hk]
          exact hγX k hk
    apply RingHom.ext
    intro b
    obtain ⟨q, rfl⟩ := surj b
    rw [RingHom.comp_apply, hG, RingHom.id_apply]
    exact RingHom.congr_fun h5 q
  have hGγ : ∀ a, G (γ a) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a (1 : E) := by
    have h6 : G.comp γ = Algebra.TensorProduct.includeLeftRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        have h7 := hT (C c)
        simp only [α', β', eval₂Hom_C] at h7
        simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
        simp only [γ, eval₂Hom_C, RingHom.comp_apply]
        rw [hGψ, h7]
      · intro k
        simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
        by_cases hk : k = j
        · subst hk
          rw [hγXj, hGψ, hTs]
          simp [Z]
        · rw [hγX k hk, ← eval₂Hom_X' ψ y k, hG, hG0X]
          simp only [Z, Function.update_of_ne hk]
    intro a
    exact RingHom.congr_fun h6 a
  have hGF : G.comp F = RingHom.id _ := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [RingHom.comp_apply, hF, map_mul, RingHom.id_apply, hGγ, hGψ,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
      simp only [RingHom.comp_apply, RingHom.id_apply, map_add (f := _)] at hx hy ⊢
      rw [hx, hy]
  let e := RingEquiv.ofRingHom F G hFG hGF
  have h8 := RingHom.Etale.respectsIso.1 _ e hbc
  convert h8 using 1
  apply RingHom.ext
  intro x
  show γ x = F (algebraMap _ _ x)
  rw [Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
  rfl

end UpperTheory.Gal.KunnethLefschetz.G

open UpperTheory.Gal.DifferentialFormSections in
theorem UpperTheory.Gal.KunnethLefschetz.G.bCoord :
    UpperTheory.Gal.KunnethLefschetz.G.BCoord := by
  intro R _ Z W π D c b j
  exact UpperTheory.Gal.KunnethLefschetz.G.etale_chart _ _ c.s (b.y j) j (dCoord R Z D c) (b.surj j) (b.ker j)
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdC (A : Type) [CommRing A] (D : ℕ) :
    (MvPolynomial.C : A →+* MvPolynomial (Fin D) A).IsStandardSmoothOfRelativeDimension D := by
  rw [← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let v : PEmpty.{1} → MvPolynomial (Fin D) A := PEmpty.elim
  let P0 := Algebra.PreSubmersivePresentation.naive (R := A) (v := v) (σ := Fin D)
    (ι := PEmpty.{1}) PEmpty.elim (fun a => a.elim)
  let P1 : Algebra.SubmersivePresentation A _ (Fin D) PEmpty.{1} :=
    { toPreSubmersivePresentation := P0
      jacobian_isUnit := by
        classical
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  have hv : Ideal.span (Set.range v) = ⊥ := by simp [v]
  let e : (MvPolynomial (Fin D) A ⧸ Ideal.span (Set.range v)) ≃ₐ[A] MvPolynomial (Fin D) A :=
    (Ideal.quotientEquivAlgOfEq A hv).trans (AlgEquiv.quotientBot A _)
  exact ⟨⟨Fin D, PEmpty.{1}, inferInstance, inferInstance, P1.ofAlgEquiv e,
    by simp [Algebra.Presentation.dimension]⟩⟩

private theorem chart {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  have H := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have hr : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.hom_comp, H.cancel_left_isIso,
      CommRingCat.hom_comp, H.cancel_right_isIso]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h
  haveI : SmoothOfRelativeDimension 0 U.ι := by
    rw [← Etale.iff_smoothOfRelativeDimension_zero]
    infer_instance
  rw [← Scheme.Hom.resLE_comp_ι f e]
  simpa using smoothOfRelativeDimension_comp n 0 (f.resLE U V e) U.ι

private theorem ofPts {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ SmoothOfRelativeDimension n (O.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose O hxO hO using H
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O
    (top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩) hO

theorem blSmooth : BlowUpSmooth := by
  intro R _ _ Z W D _ _ π hπ
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  haveI : Smooth (Over.hom Z) := SmoothOfRelativeDimension.smooth (n := D) (f := Over.hom Z)
  haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance
  obtain ⟨-, -, hoff⟩ := blOff R π hπ
  have hp1 : SmoothOfRelativeDimension D (Over.Hom.left (p1 Z)) := by
    change SmoothOfRelativeDimension D (pullback.fst (Over.hom Z) (Over.hom Z))
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have h1 : SmoothOfRelativeDimension D (Over.Hom.left (π ≫ p1 Z)) := by
    apply ofPts
    intro w
    by_cases hw : Over.Hom.left π w ∈ Set.range (Over.Hom.left (dg Z))
    · obtain ⟨z, hz⟩ := hw
      obtain ⟨U, u, hzU, hc⟩ := coordEx R Z D z
      obtain ⟨c, -, -, hcN⟩ := (dChartEx R Z D).1 U u hc z hzU
      obtain ⟨b⟩ := blChart R π hπ D c
      have hwN : w ∈ Over.Hom.left π ⁻¹ᵁ c.N := by
        show Over.Hom.left π w ∈ c.N
        rw [← hz]
        exact hcN
      rw [← b.cov] at hwN
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hwN
      refine ⟨b.V j, hj, chart _ D c.coord.1 (b.aff j) (fun x hx => c.h1 (b.le j hx)) ?_⟩
      change RingHom.IsStandardSmoothOfRelativeDimension D
        (Scheme.Hom.appLE (Over.Hom.left π ≫ Over.Hom.left (p1 Z)) c.U (b.V j) _).hom
      rw [← Scheme.Hom.appLE_comp_appLE _ _ c.U c.N (b.V j) c.h1 (b.le j), CommRingCat.hom_comp]
      have hg := RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp (bCoord R π D c b j)
      have hcomp := hg.comp (stdC _ D)
      rw [MvPolynomial.eval₂Hom_comp_C, zero_add] at hcomp
      exact hcomp
    · haveI : IsClosedImmersion (Over.Hom.left (dg Z)) := by
        change IsClosedImmersion (pullback.diagonal (Over.hom Z))
        infer_instance
      let O0 : (Over.left (XX Z)).Opens :=
        ⟨(Set.range (Over.Hom.left (dg Z)))ᶜ,
          (Over.Hom.left (dg Z)).isClosedEmbedding.isClosed_range.isOpen_compl⟩
      obtain ⟨hiso, -⟩ := hoff O0 rfl
      refine ⟨Over.Hom.left π ⁻¹ᵁ O0, hw, ?_⟩
      change SmoothOfRelativeDimension D
        ((Over.Hom.left π ⁻¹ᵁ O0).ι ≫ Over.Hom.left π ≫ Over.Hom.left (p1 Z))
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      exact IsZariskiLocalAtSource.comp (IsZariskiLocalAtSource.comp hp1 _) _
  refine ⟨h1, ?_⟩
  rw [← Over.w (π ≫ p1 Z)]
  exact smoothOfRelativeDimension_comp D D _ _

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExSmooth
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdSmooth_of_bijective {A B σ : Type} [CommRing A] [CommRing B] [Fintype σ] {d : ℕ}
    (hd : Fintype.card σ = d) (φ : A →+* B) (y : σ → B)
    (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    φ.IsStandardSmoothOfRelativeDimension d := by
  have h0 : (algebraMap A (MvPolynomial (Fin d) A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := d)).mpr
      (GlobalTheory.CompanionTheory.Ar.LieInh.stdSmooth_mvPolynomial A d)
  let e₁ : MvPolynomial (Fin d) A ≃+* MvPolynomial σ A :=
    (MvPolynomial.renameEquiv A (Fintype.equivFinOfCardEq hd).symm).toRingEquiv
  let e₂ : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  have hφ : φ = (e₁.trans e₂).toRingHom.comp (algebraMap A (MvPolynomial (Fin d) A)) := by
    ext a
    simp [e₁, e₂, MvPolynomial.algebraMap_eq]
  rw [hφ]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ h0

private theorem comap_surjective_of_bijective {A B σ : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (y : σ → B) (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    Function.Surjective (PrimeSpectrum.comap φ) := by
  let e : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  let ρ : B →+* A := (MvPolynomial.eval₂Hom (RingHom.id A) fun _ => 0).comp e.symm.toRingHom
  have hρ : ρ.comp φ = RingHom.id A := by
    ext a
    have : e.symm (φ a) = MvPolynomial.C a :=
      e.symm_apply_eq.2 (by simp [e])
    simp [ρ, this]
  intro p
  refine ⟨PrimeSpectrum.comap ρ p, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hρ, PrimeSpectrum.comap_id]

private theorem exists_apply_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : Function.Surjective (PrimeSpectrum.comap (f.appLE U V e).hom)) {y : Y} (hy : y ∈ U) :
    ∃ x, f x = y := by
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hy
  obtain ⟨q, rfl⟩ := hs p
  refine ⟨hV.fromSpec q, ?_⟩
  have h := congr($(IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e) q)
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm

private theorem isProper_snd {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (hf : IsProper f) :
    IsProper (pullback.snd f g) :=
  haveI := hf; inferInstance

private theorem exists_chart {R : Type} [CommRing R] {Z W : Sch R} (d : ℕ) [IsSeparated Z.hom]
    [SmoothOfRelativeDimension (d + 1) Z.hom] (π : W ⟶ XX Z) (hπ : IsBl π) (z : Z.left) :
    ∃ (c : DChart Z (d + 1)) (_ : BChart π c.N c.s), (dg Z).left z ∈ c.N := by
  obtain ⟨U, u, hz, hc⟩ := coordEx R Z (d + 1) z
  obtain ⟨c, -, -, hN⟩ := (dChartEx R Z (d + 1)).1 U u hc z hz
  exact ⟨c, (blChart R π hπ (d + 1) c).some, hN⟩

theorem exSmooth : ExSmooth := by
  intro R _ _ Z W d _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth (d + 1) Z.hom
  refine ⟨⟨fun x => ?_⟩, ?_, ⟨fun z => ?_⟩⟩
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ ((exG π).left x)
    have e : (exI π).left ≫ π.left = (exG π).left ≫ (dg Z).left := pullback.condition
    have hW : (exI π).left x ∈ π.left ⁻¹ᵁ c.N := by
      have h := congr($e x)
      simp only [Scheme.Hom.comp_apply] at h
      change π.left ((exI π).left x) ∈ c.N
      rw [h]
      exact hN
    rw [← b.cov] at hW
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hW
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b j
    exact ⟨_, hA, _, hB, hj, h, stdSmooth_of_bijective (by simp [Fintype.card_subtype_compl]) _ _ hbij⟩
  · exact isProper_snd π.left (dg Z).left (blOff R π hπ).1
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ z
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b 0
    exact exists_apply_eq _ hA hB h (comap_surjective_of_bijective _ _ hbij) hN

end UpperTheory.Gal.KunnethLefschetz.G
end

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.DifferentialFormSections
open FunctorialResolution.Blowup

theorem UpperTheory.Gal.KunnethLefschetz.G.blTop :
    UpperTheory.Gal.KunnethLefschetz.G.BlowUpTop := by
  intro R _ _ Z d _ hZ
  have hprop := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom Z) (Over.hom Z) hZ).2.2
  haveI : IsSeparated (Over.hom Z) := inferInstance
  haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance
  have hXX : IsProjOver (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) :=
    (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom Z) (Over.hom Z) hZ).1 hZ
  obtain ⟨Y, πl, hπ⟩ := exists_isBlowupAlongIdealSheaf (UpperTheory.Gal.KunnethLefschetz.G.XX Z).left
    (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)))
  let W : Sch R := Over.mk (πl ≫ Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
  let π : W ⟶ UpperTheory.Gal.KunnethLefschetz.G.XX Z := Over.homMk πl rfl
  have hBl : UpperTheory.Gal.KunnethLefschetz.G.IsBl π := hπ
  have hW : IsProjOver (Over.hom W) := by
    obtain ⟨M, f, h, hci⟩ :=
      UpperTheory.Gal.KunnethLefschetz.G.blEmb R (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) hXX _ πl hπ
    have hstr : IsProjOver (PSpace.str R M) := ⟨M, 𝟙 _, inferInstance, by simp⟩
    have hP := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
      (PSpace.str R M) hXX).1 hstr
    have h2 := (UpperTheory.Gal.KunnethLefschetz.G.projProd R _ (πl ≫ Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) hP).2.1 _ hci
    rw [pullback.lift_fst_assoc] at h2
    exact h2
  have hoff := UpperTheory.Gal.KunnethLefschetz.G.blOff R π hBl
  have hEx : IsProjOver (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.Ex π)) := by
    have h2 := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom W) (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.Ex π)) hW).2.1
      _ hoff.2.1
    rwa [Over.w] at h2
  have hsm := UpperTheory.Gal.KunnethLefschetz.G.blSmooth R (d + 1) π hBl
  have hex := UpperTheory.Gal.KunnethLefschetz.G.exSmooth R d π hBl
  refine ⟨W, π, hBl, hXX, hW, hEx, ?_, hsm.2, ?_⟩
  · haveI : SmoothOfRelativeDimension (d + 1) (pullback.fst (Over.hom Z) (Over.hom Z)) :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension (d + 1))
        (self := smoothOfRelativeDimension_isStableUnderBaseChange (d + 1))
        (IsPullback.of_hasPullback (Over.hom Z) (Over.hom Z)).flip inferInstance
    show SmoothOfRelativeDimension (d + 1 + (d + 1))
      (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)
    infer_instance
  · haveI := hex.1
    rw [← Over.w (UpperTheory.Gal.KunnethLefschetz.G.exG π)]
    infer_instance
end

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

theorem UpperTheory.Gal.KunnethLefschetz.G.sqCore (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
    (M : Model l K) (d : ℕ) (hM : M.Sm) (hd : SmoothOfRelativeDimension (d + 1) M.p) : ∃ S : Sq M (d + 1), Etale S.D.f := by
  obtain ⟨⟨hproj, ϖ, hϖ, -⟩, -⟩ := hM
  haveI : IsNoetherianRing (OK l K) := oKDvr l K
  let Z : Sch (OK l K) := Over.mk M.p
  haveI : SmoothOfRelativeDimension (d + 1) Z.hom := hd
  obtain ⟨W, π, hbl, hXp, hWp, -, hXs, hWs, -⟩ := blTop (OK l K) Z d hproj
  haveI : IsProper Z.hom := ((projProd (OK l K) Z.hom Z.hom hproj).2.2)
  obtain ⟨D, het, ⟨B⟩⟩ := blowOfBl (OK l K) (d + 1) π hbl
  let P : Model l K := ⟨(XX Z).left, (XX Z).hom⟩
  let Y : Model l K := ⟨W.left, W.hom⟩
  have hΔ : (dg Z).left ≫ P.p = M.p := Over.w (dg Z)
  have hπ : π.left ≫ P.p = Y.p := Over.w π
  haveI : Smooth P.p := SmoothOfRelativeDimension.smooth (d + 1 + (d + 1)) P.p
  haveI : Smooth Y.p := SmoothOfRelativeDimension.smooth (d + 1 + (d + 1)) Y.p
  have hP : P.Sm := ⟨⟨hXp, ϖ, hϖ, smSst _ ϖ P.p⟩, inferInstance⟩
  have hY : Y.Sm := ⟨⟨hWp, ϖ, hϖ, smSst _ ϖ Y.p⟩, inferInstance⟩
  have sq₀ : IsPullback (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) P.q P.p
      (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := IsPullback.of_hasPullback _ _
  have sqΔ : IsPullback (pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
      (Model.genMap (M := M) (N := P) (dg Z).left hΔ) (dg Z).left
      (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm sq₀
    rw [Model.genMap_q, hΔ]
    exact IsPullback.of_hasPullback _ _
  have sqπ : IsPullback (pullback.fst Y.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
      (Model.genMap (M := Y) (N := P) π.left hπ) π.left
      (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm sq₀
    rw [Model.genMap_q, hπ]
    exact IsPullback.of_hasPullback _ _
  exact ⟨{
    P := P, Y := Y, p₁ := (p1 Z).left, p₂ := (p2 Z).left, Δ := (dg Z).left, π := π.left
    h₁ := Over.w (p1 Z), h₂ := Over.w (p2 Z), hΔ := hΔ, hπ := hπ
    Δ₁ := pullback.diagonal_fst _, Δ₂ := pullback.diagonal_snd _
    prod := IsPullback.of_hasPullback _ _
    smP := hP, smY := hY, D := D, loc := B.loc
    blow := blowBC (OK l K) K (OK l K).subtype (XX Z).hom (dg Z).left π.left D (d + 1) P.q _ _ _ _ _ sq₀ sqΔ sqπ ⟨B⟩ }, het⟩

theorem UpperTheory.Gal.KunnethLefschetz.G.sqEx3 : CrystallineSemistableComparison.Onto.SqEx3 := fun l _ K _ M d _ h1 h2 => UpperTheory.Gal.KunnethLefschetz.G.sqCore l K M d h1 h2
