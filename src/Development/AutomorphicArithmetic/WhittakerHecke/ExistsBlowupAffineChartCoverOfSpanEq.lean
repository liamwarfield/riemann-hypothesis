module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.SurjectiveEvalBlowupChartOfSpanEq
open FunctorialResolution.Blowup

namespace UpperTheory.ChartGen

variable {R : Type} [CommRing R]

private theorem val_rho (I : Ideal R) (c : ↥I) (r : R) :
    HomogeneousLocalization.val (chartRingHom I c r) =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)))
        (1 : ↥(Submonoid.powers (reesGenerator I c))) := rfl

private theorem cancel_rho (I : Ideal R) (c : ↥I) (n : ℕ)
    {x y : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)}
    (h : x * chartRingHom I c (c : R) ^ n = y * chartRingHom I c (c : R) ^ n) : x = y := by
  have hn := pow_mem (chartRingHom_mem_nonZeroDivisors I c) n
  have h0 : (x - y) * chartRingHom I c (c : R) ^ n = 0 := by rw [sub_mul, h, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hn).2 _ h0)

private theorem exists_mul_pow_eq (I : Ideal R) (c : ↥I)
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I c)) :
    ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
      z * chartRingHom I c (c : R) ^ n = chartRingHom I c r := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesGrading I)
    (reesGenerator_mem_reesGrading I c) z
  have hx' : x ∈ reesGrading I n := by simpa using hx
  obtain ⟨r, hr, hxr⟩ := (mem_reesGrading_iff_monomial I n x).1 hx'
  refine ⟨n, r, hr, ?_⟩
  rw [← map_pow, HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    val_rho, val_rho, HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hpow : ((reesGenerator I c ^ n : ↥(reesAlgebra I)) : Polynomial R) =
      Polynomial.monomial n ((c : R) ^ n) := by
    rw [SubmonoidClass.coe_pow, reesGenerator_coe, Polynomial.monomial_pow, one_mul]
  push_cast [reesDegreeZeroEquiv_coe_coe, hxr, hpow]
  simp [Polynomial.C_mul_monomial, Polynomial.monomial_mul_C, mul_comm]
  rw [← Polynomial.C_pow, Polynomial.monomial_mul_C]

end UpperTheory.ChartGen

open UpperTheory.ChartGen in
theorem UpperTheory.surjective_eval_blowupChart_of_span_eq :
    ∀ {R : Type} [CommRing R] (I : Ideal R) {M : ℕ} (a : Fin (M + 1) → ↥I), Ideal.span (Set.range fun l => (a l : R)) = I → ∀ m : Fin (M + 1), Function.Surjective (MvPolynomial.eval₂Hom (chartRingHom I (a m)) (fun l => chartFraction I (a m) (a l))) := by
  intro R _ I M a hspan m
  set c := a m with hc
  set φ := MvPolynomial.eval₂Hom (chartRingHom I c) (fun l => chartFraction I c (a l)) with hφ
  have hC : ∀ r : R, chartRingHom I c r ∈ φ.range := fun r =>
    ⟨MvPolynomial.C r, by simp [hφ]⟩
  have hX : ∀ l, chartFraction I c (a l) ∈ φ.range := fun l =>
    ⟨MvPolynomial.X l, by simp [hφ]⟩
  have hfrac : ∀ b : ↥I, chartFraction I c b ∈ φ.range := by
    intro b
    have hb : (b : R) ∈ Ideal.span (Set.range fun l => (a l : R)) := by rw [hspan]; exact b.2
    obtain ⟨s, hs⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hb
    have hw : ∑ l, chartRingHom I c (s l) * chartFraction I c (a l) ∈ φ.range :=
      sum_mem fun l _ => mul_mem (hC _) (hX l)
    have heq : chartFraction I c b = ∑ l, chartRingHom I c (s l) * chartFraction I c (a l) := by
      apply cancel_rho I c 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pow_one, ← chartRingHom_coe_eq_chartFraction_mul, ← hs, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, chartRingHom_coe_eq_chartFraction_mul I c (a l), mul_assoc]
    rw [heq]
    exact hw
  have hpow : ∀ (n : ℕ), ∀ r ∈ I ^ n, ∃ w ∈ φ.range,
      chartRingHom I c r = w * chartRingHom I c (c : R) ^ n := by
    intro n
    induction n with
    | zero => exact fun r _ => ⟨_, hC r, by simp⟩
    | succ n ih =>
      intro r hr
      rw [pow_succ] at hr
      refine Submodule.mul_induction_on hr ?_ ?_
      · intro s hs b hb
        obtain ⟨w, hw, hwe⟩ := ih s hs
        refine ⟨w * chartFraction I c ⟨b, hb⟩, mul_mem hw (hfrac _), ?_⟩
        have hbe := chartRingHom_coe_eq_chartFraction_mul I c ⟨b, hb⟩
        rw [map_mul, hwe]
        simp only at hbe
        rw [hbe]
        ring
      · rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
        exact ⟨wx + wy, add_mem hwx hwy, by rw [map_add (f := _), hx, hy, add_mul]⟩
  intro z
  obtain ⟨n, r, hr, hz⟩ := exists_mul_pow_eq I c z
  obtain ⟨w, hw, hwe⟩ := hpow n r hr
  have hzw : z = w := cancel_rho I c n (hz.trans hwe)
  rw [hzw]
  exact hw
end

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem chart_cover {R : Type} [CommRing R] (I : Ideal R) {M : ℕ} (a : Fin (M + 1) → ↥I)
    (h : Ideal.span (Set.range fun l => (a l : R)) = I) :
    ⨆ m, (affineBlowupChart I (a m) ''ᵁ ⊤) = ⊤ := by
  simp only [Scheme.Hom.image_top_eq_opensRange, opensRange_affineBlowupChart_eq_basicOpen]
  refine Proj.iSup_basicOpen_eq_top (reesGrading I) (fun m => reesGenerator I (a m)) ?_
  refine (reesGrading_irrelevant_le_span I).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  have hb : (b : R) ∈ Ideal.span (Set.range fun l => (a l : R)) := by rw [h]; exact b.2
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb
  have hsum : reesGenerator I b = ∑ l, algebraMap R ↥(reesAlgebra I) (c l) * reesGenerator I (a l) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [reesGenerator_coe, ← hc, MulMemClass.coe_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    show _ = Polynomial.C (c l) * _
    rw [Polynomial.C_mul_monomial]
  rw [SetLike.mem_coe, hsum]
  exact sum_mem fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)

private theorem chart_inter {R : Type} [CommRing R] (I : Ideal R) (a b : ↥I) :
    (affineBlowupChart I a ''ᵁ ⊤) ⊓ (affineBlowupChart I b ''ᵁ ⊤) =
      affineBlowupChart I a ''ᵁ PrimeSpectrum.basicOpen (chartFraction I a b) := by
  have hel : HomogeneousLocalization.Away.isLocalizationElem
        (reesGenerator_mem_reesGrading I a) (reesGenerator_mem_reesGrading I b)
      = chartFraction I a b := by
    apply HomogeneousLocalization.val_injective
    rw [chartFraction_eq_mk]
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.val_mk, pow_one]
  have hpre : affineBlowupChart I a ⁻¹ᵁ (affineBlowupChart I b).opensRange
      = PrimeSpectrum.basicOpen (chartFraction I a b) := by
    rw [opensRange_affineBlowupChart_eq_basicOpen, affineBlowupChart_eq_awayι, ← hel]
    exact Proj.awayι_preimage_basicOpen (reesGrading I) (reesGenerator_mem_reesGrading I a) Nat.one_pos
      (reesGenerator_mem_reesGrading I b) Nat.one_pos
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange]

private theorem fromSpec_appLE_top {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(Z, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(Z, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact CategoryTheory.Functor.map_id _ _

private theorem exists_open_emb {Z W : Scheme.{0}} (I : Z.IdealSheafData) (π : W ⟶ Z)
    (hπ : IsBlowupAlongIdealSheaf π I) (U : Z.affineOpens) :
    ∃ (j : affineBlowup (I.ideal U) ⟶ W) (_ : IsOpenImmersion j),
      j ≫ π = AffineBlowup.toSpec (I.ideal U) ≫ U.2.fromSpec ∧ j ''ᵁ ⊤ = π ⁻¹ᵁ U.1 := by
  have hU : IsAffineOpen U.1 := U.2
  haveI : IsOpenImmersion (IsAffineOpen.fromSpec U.2) := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hI : I.comap U.2.fromSpec = specIdealSheaf (I.ideal U) := by
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    have e : (⊤ : (Spec Γ(Z, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by
      rw [U.2.fromSpec_preimage_self]
    have h5 : (I.comap U.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
        Ideal.map (Scheme.ΓSpecIso Γ(Z, U.1)).inv.hom (I.ideal U) := by
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.2.fromSpec U ⟨⊤, isAffineOpen_top _⟩ e]
      have h6 := fromSpec_appLE_top U.2 e
      have h7 : ∀ f g : Γ(Z, U.1) ⟶ Γ(Spec Γ(Z, U.1), ⊤), f = g →
          Ideal.map f.hom (I.ideal U) = Ideal.map g.hom (I.ideal U) := by
        rintro f _ rfl
        rfl
      exact h7 _ _ h6
    exact h5.trans (specIdealSheaf_ideal_top (I.ideal U)).symm
  have h1 := hπ.pullback_snd_of_isOpenImmersion U.2.fromSpec
  rw [hI] at h1
  obtain ⟨e, he⟩ := (isBlowupAlongIdealSheaf_affineBlowup_toSpec (I.ideal U)).exists_iso h1
  refine ⟨e.hom ≫ pullback.fst π U.2.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  · rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Hom.opensRange_pullbackFst]
    exact congrArg (π ⁻¹ᵁ ·) hU.opensRange_fromSpec

private theorem sections_transfer {Z W : Scheme.{0}} (π : W ⟶ Z) (U : Z.affineOpens) {C : Type} [CommRing C]
    (φ : Γ(Z, U.1) →+* C) (ψ : Spec (CommRingCat.of C) ⟶ W) [IsOpenImmersion ψ]
    (hψ : ψ ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
    (le : ψ ''ᵁ ⊤ ≤ π ⁻¹ᵁ U.1) :
    ∃ e : Γ(W, ψ ''ᵁ ⊤) ≃+* C, (∀ x, e (π.appLE U.1 (ψ ''ᵁ ⊤) le x) = φ x) ∧
      ∀ z, W.basicOpen (e.symm z) = ψ ''ᵁ PrimeSpectrum.basicOpen z := by
  let E : Γ(W, ψ ''ᵁ ⊤) ≅ CommRingCat.of C := ψ.appIso ⊤ ≪≫ Scheme.ΓSpecIso (CommRingCat.of C)
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · have hcat : π.appLE U.1 (ψ ''ᵁ ⊤) le ≫ E.hom = CommRingCat.ofHom φ := by
      have h0 : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ ψ ⁻¹ᵁ (ψ ''ᵁ ⊤) := fun x _ => ⟨x, trivial, rfl⟩
      have h1 : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (ψ ≫ π) ⁻¹ᵁ U.1 := fun x hx => le (h0 hx)
      have h2 : π.appLE U.1 (ψ ''ᵁ ⊤) le ≫ (ψ.appIso ⊤).hom = (ψ ≫ π).appLE U.1 ⊤ h1 := by
        rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
      have h3 : ∀ (f : Spec (CommRingCat.of C) ⟶ Z) (hf : f = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
          (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ f ⁻¹ᵁ U.1),
          f.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom = CommRingCat.ofHom φ := by
        rintro f rfl h
        have h4 : (⊤ : (Spec Γ(Z, U.1)).Opens) ≤ (IsAffineOpen.fromSpec U.2) ⁻¹ᵁ U.1 := by
          rw [U.2.fromSpec_preimage_self]
        rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) (IsAffineOpen.fromSpec U.2) U.1 ⊤ ⊤ h4 le_top, fromSpec_appLE_top U.2 h4]
        have h8 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom φ)).appTop := by
          exact Scheme.Hom.appLE_eq_app _
        rw [h8, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      show π.appLE U.1 (ψ ''ᵁ ⊤) le ≫ (ψ.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom = _
      rw [← Category.assoc, h2]
      exact h3 _ hψ h1
    intro x
    exact congrArg (fun f => f.hom x) hcat
  · intro z
    have h2 : (Spec (CommRingCat.of C)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom z)
        = PrimeSpectrum.basicOpen z := basicOpen_eq_of_affine (R := CommRingCat.of C) z
    rw [← h2, Scheme.image_basicOpen]
    rfl

private theorem assemble {Z W A : Scheme.{0}} (π : W ⟶ Z) (U : Z.affineOpens) {M : ℕ}
    (g : Fin (M + 1) → Γ(Z, U.1)) (C : Fin (M + 1) → Type) [∀ m, CommRing (C m)]
    (φ : ∀ m, Γ(Z, U.1) →+* C m) (fr : ∀ m, Fin (M + 1) → C m)
    (j : A ⟶ W) [IsOpenImmersion j] (hjr : j ''ᵁ ⊤ = π ⁻¹ᵁ U.1)
    (ch : ∀ m, Spec (CommRingCat.of (C m)) ⟶ A) [∀ m, IsOpenImmersion (ch m)]
    (hch : ∀ m, ch m ≫ j ≫ π = Spec.map (CommRingCat.ofHom (φ m)) ≫ U.2.fromSpec)
    (heq : ∀ m l, φ m (g l) = fr m l * φ m (g m))
    (hnzd : ∀ m, φ m (g m) ∈ nonZeroDivisors (C m))
    (hsurj : ∀ m, Function.Surjective (MvPolynomial.eval₂Hom (φ m) (fr m)))
    (hcov : ⨆ m, (ch m ''ᵁ ⊤) = ⊤)
    (hint : ∀ m l, (ch m ''ᵁ ⊤) ⊓ (ch l ''ᵁ ⊤) = ch m ''ᵁ PrimeSpectrum.basicOpen (fr m l)) :
    ∃ (V : Fin (M + 1) → W.Opens) (le : ∀ m, V m ≤ π ⁻¹ᵁ U.1) (c : ∀ m, Fin (M + 1) → Γ(W, V m)),
          (∀ m, IsAffineOpen (V m)) ∧ iSup V = π ⁻¹ᵁ U.1 ∧
          (∀ m l, π.appLE U.1 (V m) (le m) (g l) = π.appLE U.1 (V m) (le m) (g m) * c m l) ∧
          (∀ m, c m m = 1) ∧
          (∀ m, π.appLE U.1 (V m) (le m) (g m) ∈ nonZeroDivisors Γ(W, V m)) ∧
          (∀ m, Function.Surjective (MvPolynomial.eval₂Hom (π.appLE U.1 (V m) (le m)).hom (c m))) ∧
          (∀ m l, V m ⊓ V l = W.basicOpen (c m l)) := by
  have himg : ∀ (m) (O : (Spec (CommRingCat.of (C m))).Opens),
      (ch m ≫ j) ''ᵁ O = j ''ᵁ (ch m ''ᵁ O) := fun m O => Scheme.Hom.comp_image _ _ _
  have hψ : ∀ m, (ch m ≫ j) ≫ π = Spec.map (CommRingCat.ofHom (φ m)) ≫ U.2.fromSpec := by
    intro m
    rw [Category.assoc, hch]
  have hle : ∀ m, (ch m ≫ j) ''ᵁ ⊤ ≤ π ⁻¹ᵁ U.1 := by
    intro m
    rw [himg, ← hjr]
    exact (j.opensFunctor).monotone le_top
  choose e he1 he2 using fun m => sections_transfer π U (φ m) (ch m ≫ j) (hψ m) (hle m)
  have key : ∀ m x, π.appLE U.1 ((ch m ≫ j) ''ᵁ ⊤) (hle m) x = (e m).symm (φ m x) := by
    intro m x
    rw [← he1 m x, RingEquiv.symm_apply_apply]
  have hone : ∀ m, fr m m = 1 := by
    intro m
    have h1 : (fr m m - 1) * φ m (g m) = 0 := by rw [sub_mul, ← heq, one_mul, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp (hnzd m)) _ h1)
  refine ⟨fun m => (ch m ≫ j) ''ᵁ ⊤, hle, fun m l => (e m).symm (fr m l), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact (isAffineOpen_top _).image_of_isOpenImmersion (ch m ≫ j)
  · apply le_antisymm
    · exact iSup_le fun m => hle m
    · rw [← hjr]
      rintro x ⟨y, -, rfl⟩
      have hy : y ∈ ⨆ m, ch m ''ᵁ ⊤ := hcov ▸ trivial
      obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨m, ?_⟩
      rw [himg]
      exact ⟨y, hm, rfl⟩
  · intro m l
    rw [key, key, heq, map_mul, mul_comm]
  · intro m
    simp only [hone, map_one]
  · intro m
    rw [key]
    refine mem_nonZeroDivisors_iff_right.mpr fun y hy => ?_
    have h1 := congrArg (e m) hy
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at h1
    exact (map_eq_zero_iff _ (e m).injective).mp ((mem_nonZeroDivisors_iff_right.mp (hnzd m)) _ h1)
  · intro m
    have hcomp : (MvPolynomial.eval₂Hom (π.appLE U.1 ((ch m ≫ j) ''ᵁ ⊤) (hle m)).hom (fun l => (e m).symm (fr m l)))
        = (e m).symm.toRingHom.comp (MvPolynomial.eval₂Hom (φ m) (fr m)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [key]
      · intro i
        simp
    rw [hcomp]
    exact (e m).symm.surjective.comp (hsurj m)
  · intro m l
    have hinf : ∀ P Q : A.Opens, j ''ᵁ P ⊓ j ''ᵁ Q = j ''ᵁ (P ⊓ Q) := by
      intro P Q
      apply TopologicalSpace.Opens.ext
      exact (Set.image_inter j.isOpenEmbedding.injective).symm
    refine Eq.trans ?_ (he2 m (fr m l)).symm
    calc (ch m ≫ j) ''ᵁ ⊤ ⊓ (ch l ≫ j) ''ᵁ ⊤ = j ''ᵁ (ch m ''ᵁ ⊤) ⊓ j ''ᵁ (ch l ''ᵁ ⊤) := by
          rw [himg, himg]
      _ = j ''ᵁ (ch m ''ᵁ ⊤ ⊓ ch l ''ᵁ ⊤) := hinf _ _
      _ = j ''ᵁ (ch m ''ᵁ PrimeSpectrum.basicOpen (fr m l)) := by rw [hint]
      _ = _ := (himg m _).symm

theorem UpperTheory.exists_blowup_affine_chart_cover_of_span_eq :
    ∀ {Z W : Scheme.{0}} (I : Z.IdealSheafData) (π : W ⟶ Z), IsBlowupAlongIdealSheaf π I → ∀ (U : Z.affineOpens) {M : ℕ} (g : Fin (M + 1) → Γ(Z, U.1)),
        Ideal.span (Set.range g) = I.ideal U →
        ∃ (V : Fin (M + 1) → W.Opens) (le : ∀ m, V m ≤ π ⁻¹ᵁ U.1) (c : ∀ m, Fin (M + 1) → Γ(W, V m)),
          (∀ m, IsAffineOpen (V m)) ∧ iSup V = π ⁻¹ᵁ U.1 ∧
          (∀ m l, π.appLE U.1 (V m) (le m) (g l) = π.appLE U.1 (V m) (le m) (g m) * c m l) ∧
          (∀ m, c m m = 1) ∧
          (∀ m, π.appLE U.1 (V m) (le m) (g m) ∈ nonZeroDivisors Γ(W, V m)) ∧
          (∀ m, Function.Surjective (MvPolynomial.eval₂Hom (π.appLE U.1 (V m) (le m)).hom (c m))) ∧
          (∀ m l, V m ⊓ V l = W.basicOpen (c m l)) := by
  intro Z W I π hπ U M g hg
  have hgm : ∀ l, g l ∈ I.ideal U := fun l => hg ▸ Ideal.subset_span ⟨l, rfl⟩
  let a : Fin (M + 1) → ↥(I.ideal U) := fun l => ⟨g l, hgm l⟩
  obtain ⟨j, hj, hjπ, hjr⟩ := exists_open_emb I π hπ U
  refine assemble π U g (fun m => HomogeneousLocalization.Away (reesGrading (I.ideal U)) (reesGenerator (I.ideal U) (a m)))
    (fun m => chartRingHom (I.ideal U) (a m)) (fun m l => chartFraction (I.ideal U) (a m) (a l)) j hjr
    (fun m => affineBlowupChart (I.ideal U) (a m)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro m
    rw [hjπ, ← Category.assoc, affineBlowupChart_comp_toSpec]
  · exact fun m l => chartRingHom_coe_eq_chartFraction_mul (I.ideal U) (a m) (a l)
  · exact fun m => chartRingHom_mem_nonZeroDivisors (I.ideal U) (a m)
  · exact fun m => UpperTheory.surjective_eval_blowupChart_of_span_eq _ a hg m
  · exact chart_cover _ a hg
  · exact fun m l => chart_inter _ _ _
