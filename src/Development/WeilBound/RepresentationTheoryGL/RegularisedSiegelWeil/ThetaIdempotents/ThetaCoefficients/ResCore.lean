module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.SphBound
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEv
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajor
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.GenK
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WMaj
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixW
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixTh
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LRowTotal
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureExists
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterQuadraticFormIdentity
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExt
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxId
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EisMeasTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LNullSing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemExTrans
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongrOverOfFrame
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularStab
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ProjKComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsLast
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.ContinuousHermitianInnerSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendByZeroHermitianVal
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThCoef
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponents
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.GoodPlacesOutsideFiniteSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompactBis
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRel
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBdd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLow
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfInv
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LCfInv

variable {D : D7} {n : ℕ}

theorem fam_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {u : G D n} (hH : ∀ g, H (g * u) = H g)
    (hφ : ∀ g, φ (g * u) = φ g) (s₁ z : ℂ) (g : G D n) : fam H φ s₁ z (g * u) = fam H φ s₁ z g := by
  simp only [fam, hH, hφ]

theorem eisS_mul {f : G D n → ℂ} {u : G D n} (hf : ∀ g, f (g * u) = f g) (g : G D n) :
    eisS f (g * u) = eisS f g := by
  unfold eisS GlobalTheory.Eis.cosetSum
  refine tsum_congr fun q => ?_
  simp only [GlobalTheory.Eis.term, ← mul_assoc, hf]

theorem E_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hc : IsCont H φ s₀ U d E σ) {u : G D n} (hH : ∀ g, H (g * u) = H g) (hφ : ∀ g, φ (g * u) = φ g) (g : G D n) :
    ∀ z ∈ U, E z (g * u) = E z g := by
  have ah : AnalyticOnNhd ℂ (E · (g * u)) U := (hc.hol (g * u)).analyticOnNhd hc.isOpen
  have ag : AnalyticOnNhd ℂ (E · g) U := (hc.hol g).analyticOnNhd hc.isOpen
  obtain ⟨τ, hτ⟩ := hc.right.1
  have hx : ((max τ σ + 1 : ℝ) : ℂ) ∈ rightOf (max τ σ) := by simp
  have hxU : ((max τ σ + 1 : ℝ) : ℂ) ∈ U := hτ (rightOf_subset (le_max_left _ _) hx)
  have ev : (E · (g * u)) =ᶠ[𝓝 ((max τ σ + 1 : ℝ) : ℂ)] (E · g) := by
    filter_upwards [(isOpen_rightOf (max τ σ)).mem_nhds hx] with w hw
    have hw' : σ < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    simp only [hc.eq w hw', eisS_mul (fam_mul hH hφ s₀ w)]
  exact fun z hz => ah.eqOn_of_preconnected_of_eventuallyEq ag hc.right.isPreconnected hxU ev hz

end PositivityTheory.Rg.Rsw.L.LCfInv

namespace PositivityTheory.Rg.Rsw.L

open LCfInv in
theorem cfInv : CfInv := by
  intro D n H s₀ φ U d E σ hc ε hε u hH hφ k g
  unfold cf
  congr 1
  refine circleIntegral.integral_congr hε.1.le fun z hz => ?_
  have hzU : z ∈ U := hε.2.1 (Metric.sphere_subset_closedBall hz)
  simp only [E_mul hc hH hφ g z hzU]

end PositivityTheory.Rg.Rsw.L

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormula
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianCoefficient
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianCoefficient
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem coefN_finset_sum_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (N : ℕ) (Φ : Fin N → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hM ψ hψ dx hdx db hdb T N Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, ht, -, hB, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hB n M
  obtain ⟨hψc, hψn, -⟩ := id hψ
  have hstar : ∀ b, starN σ J ψ dx (fun X => ∑ i, Φ i X) b = ∑ i, starN σ J ψ dx (Φ i) b := by
    intro b
    unfold starN
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun i _ => ?_
    obtain ⟨hc, hi⟩ := GlobalTheory.CompanionTheory.SiegelND.CoefSum.continuous_integrable_tuple σ hCM M n dx hdx.1 (Φ i) (hΦ i)
    have hq : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
        algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
          (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)) :=
      continuous_const.mul (ht.comp (continuous_const.matrix_mul (hG n M J)).matrix_trace)
    refine hi.norm.mono' (hc.mul (hψc.comp hq)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, hψn, mul_one]
  unfold coefN
  simp_rw [hstar, Finset.sum_mul]
  refine integral_finsetSum _ fun i _ => ?_
  have hI := GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb (Φ i) (hΦ i)
  have hc : Continuous fun b : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp (continuous_const.mul
      (ht.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  refine hI.norm.mono' (hI.1.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun b => ?_
  rw [norm_mul, hψn, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianCoefficientStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_hermitian_coefficient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (N : ℕ) (Φ : Fin N → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_finset_sum_all | exact GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_finset_sum_all | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_finset_sum_all <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormula
noncomputable section

section Body
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Pure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem coefS_pure (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (h2n : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf)
    (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (hdet : T.det ≠ 0) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S →
      ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ →
      ∀ A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E),
        (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) →
        coefSN σ b J ψ dx db (pureN φ A) T S =
          (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) *
            ∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ) := by
  classical
  obtain ⟨hEu, hlat⟩ := GlobalTheory.T.adelic_measure_euler_product_decomposition F E σ hCM M J hJ n h2n ψ hψ dx hdx d b laminf lam hinf hlam
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.euler_product_measure_eventually_standard F E M n d b dx 1 _ _ hEu
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.hermitian_measure_euler_product F E σ hCM M J hJ n h2n ψ hψ db hdb d b laminf lam hinf hlam
  have hq := GlobalTheory.T.gram_matrix_integral_almost_all_places F E σ hCM M J hJ n h2n d b T hT
  have hqf := Filter.eventually_cofinite.1 hq
  refine ⟨S₀ ∪ S₁ ∪ hqf.toFinset, fun S hS φ hφ A hA hAl => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : ∀ v, v ∉ S → ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))
  obtain ⟨ρ, U, hρ, hρs, hU, hUs, hI, hc, hbd, hlim⟩ := hS₁ S hS1
  have hΦSB : IsSchwartzBruhat (pureN φ A) := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n d b S φ A hφ hA hAl
  have hΦdx : Integrable (pureN φ A) dx := GlobalTheory.T.schwartz_bruhat_integrable_adelic F E σ hCM M J hJ n h2n ψ hψ dx hdx _ hΦSB
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦSB
  have hu : ∀ (R : Type) [CommRing R] [Algebra F R],
      IsUnit (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    intro R _ _
    have h : (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det = inclR R T.det :=
      ((inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (inclR R)
  set cI : HermR (Ainf F) σ n := hermOf (Ainf F) σ T hT with hcI
  have hInf := GlobalTheory.T.archimedean_gram_fibre_measure_exists F E σ hCM M J hJ n h2n d b laminf hinf minf hminf cI (hu _) φ hφ ρ hρ hρs
  have hV := fun v => GlobalTheory.T.local_gram_fibre_measure_unramified F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (hu _) (A v) (hA v).1 (hA v).2 (fun k => U k v)
    (fun k => ⟨(hU k v).1, (hU k v).2.1, (hU k v).2.2.1⟩) (hUs v)
  have hUpos : ∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal :=
    fun k v => (hU k v).2.2.2
  have hρpos : ∀ k, 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) := fun k => (hρ k).2.2.2
  have hck : ∀ k, (∫ y, testH σ b (ρ k) S (U k) y ∂db) ≠ 0 := by
    intro k
    rw [hc k]
    refine mul_ne_zero (by exact_mod_cast (hρpos k).ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    exact_mod_cast (hUpos k v).ne'
  have a1 : ∀ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R'),
      hermMap f σ (hermOf R σ T hT) = hermOf R' σ T hT := fun f => hermMap_hermOf f σ T hT
  have h3 : ∀ (x : Fin n → Fin M → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      hermV σ v (hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x)) =
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) (projV v (projFin x)) := by
    intro x v
    simp only [hermV, hermFin, hermMap_sub, a1, hermMap_gramH]
    rfl
  have h0 : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
      hermInf σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) = cI - gramH hCM hJ (Ainf F) (projInf x) := by
    intro x
    simp only [hermInf, hermMap_sub, a1, hermMap_gramH]
    rfl
  have key : ∀ k, ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb / ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db =
      ((∫ X, φ X * (ρ k (cI - gramH hCM hJ (Ainf F) X) : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) /
          ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) *
        ∏ v ∈ S, (((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v})).toReal /
            (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℝ) : ℂ) := by
    intro k
    have hf := GlobalTheory.T.siegel_weil_integral_normalised F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦdx
      (testH σ b (ρ k) S (U k)) (hI k).1 (hI k).2 T hT
    let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
      if v ∈ S then A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v} else A v
    have hA'S : ∀ v ∈ S, A' v = A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v} :=
      fun v hv => if_pos hv
    have hA'n : ∀ v, v ∉ S → A' v = latV b v := fun v hv => (if_neg hv).trans (hAl v hv)
    have hmem : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
        (projFin x ∈ boxFN A ∧ hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∈ boxH σ b n S (U k)) ↔
          projFin x ∈ boxFN A' := by
      intro x
      constructor
      · rintro ⟨h, h'⟩ v
        by_cases hv : v ∈ S
        · rw [hA'S v hv]
          refine ⟨h v, ?_⟩
          show _ ∈ U k v
          rw [← h3 x v]
          exact h'.1 v hv
        · rw [show A' v = A v from if_neg hv]
          exact h v
      · intro h
        refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
        · by_cases hv : v ∈ S
          · have := h v
            rw [hA'S v hv] at this
            exact this.1
          · have := h v
            rwa [show A' v = A v from if_neg hv] at this
        · have := h v
          rw [hA'S v hv] at this
          rw [h3 x v]
          exact this.2
        · have := h v
          rw [hA'n v hv] at this
          rw [h3 x v]
          exact hS2 v hv _ this
    have hpt : ∀ x, pureN φ A x * testH σ b (ρ k) S (U k) (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) =
        pureN (fun X => φ X * (ρ k (cI - gramH hCM hJ (Ainf F) X) : ℂ)) A' x := by
      intro x
      unfold pureN testH
      rw [h0 x]
      by_cases h : projFin x ∈ boxFN A'
      · obtain ⟨ha, hb⟩ := (hmem x).2 h
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb, Set.indicator_of_mem h]
        ring
      · rw [Set.indicator_of_notMem h, mul_zero]
        by_cases ha : projFin x ∈ boxFN A
        · have hb : hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∉ boxH σ b n S (U k) :=
            fun hb => h ((hmem x).1 ⟨ha, hb⟩)
          rw [Set.indicator_of_notMem hb]
          simp
        · rw [Set.indicator_of_notMem ha]
          simp
    have hmeasA' : ∀ v, MeasurableSet (A' v) := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).1
      · rw [show A' v = A v from if_neg hv]
        exact (GlobalTheory.T.local_gram_fibre_measure_standard_volume F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v) _ (hu _) (A v) (hA v).1 (hA v).2).1
    have hfinA' : ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v) ≠ ⊤ := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).2
      · rw [hA'n v hv, hlat v]; exact ENNReal.one_ne_top
    have he := (hS₀ S hS0 _ (hInf.1 k).1 (hInf.1 k).2 A' hmeasA' hfinA' hA'n).2
    have htail : (∏' v : {v // v ∉ S}, (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) b (lam v.1) n M (latV b v.1)).toReal) = 1 := by
      simp [hlat]
    rw [htail] at he
    have hprod : (∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v)).toReal : ℂ)) =
        ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v})).toReal : ℂ) :=
      Finset.prod_congr rfl fun v hv => by rw [hA'S v hv]
    have e1 : ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb / ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db =
        (∫ bb, fouH σ ψ db (testH σ b (ρ k) S (U k)) bb *
          (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db) /
          ∫ y, testH σ b (ρ k) S (U k) y ∂db := by
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall fun bb => by simp only []; ring)
    rw [e1, hf, integral_congr_ae (Filter.Eventually.of_forall hpt), he, hprod, hc k]
    push_cast
    rw [Finset.prod_div_distrib]
    simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_one]
    rw [div_mul_div_comm]
  have lim1 : Filter.Tendsto (fun k => ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb /
        ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db) Filter.atTop
      (nhds (coefSN σ b J ψ dx db (pureN φ A) T S)) := by
    have hχ : Continuous (chiT σ ψ T) := GlobalTheory.T.continuous_fourier_character_of_matrix F E σ hCM M J hJ n h2n ψ hψ T
    refine tendsto_integral_of_dominated_convergence (fun bb => ‖starN σ J ψ dx (pureN φ A) bb‖) ?_ hstar.norm ?_ ?_
    · intro k
      exact ((hI k).1.div_const _).aestronglyMeasurable.mul (hstar.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    · intro k
      refine Filter.Eventually.of_forall fun bb => ?_
      rw [norm_mul, norm_mul, show ‖chiT σ ψ T bb‖ = 1 from hψ.2.1 _, mul_one, norm_div]
      exact mul_le_of_le_one_left (norm_nonneg _)
        ((div_le_one (norm_pos_iff.2 (hck k))).2 (hbd k bb))
    · refine Filter.Eventually.of_forall fun bb => ?_
      exact (hlim bb).mul_const _
  have lim2 := hInf.2.mul (tendsto_finsetProd S fun v _ =>
    (Complex.continuous_ofReal.tendsto _).comp (hV v).2)
  exact tendsto_nhds_unique lim1 (lim2.congr fun k => by simpa using (key k).symm)

theorem pure_identity (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (h2n : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf)
    (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (hdet : T.det ≠ 0)
    (hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hφ : IsSchwartzArch φ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v)) (hAl : ∀ v, v ∉ S₀ → A v = latV b v) :
    Integrable (pureN φ A) I ∧ coefN σ J ψ dx db (pureN φ A) T = ∫ X, pureN φ A X ∂I := by
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_measure_eventually_standard F E M n d b _ 1 _ _ hEu
  obtain ⟨S₂, hS₂⟩ := coefS_pure σ hCM J hJ h2n ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT hdet
  have hu : ∀ (R : Type) [CommRing R] [Algebra F R],
      IsUnit (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    intro R _ _
    have h : (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det = inclR R T.det :=
      ((inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (inclR R)
  obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_gram_fibre_measure_formula F E σ hCM M J hJ n h2n d b laminf hinf minf hminf _ (hu _) φ hφ
  have hφi' := hφi.self_of_nhds
  have hΦSB : IsSchwartzBruhat (pureN φ A) := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n d b S₀ φ A hφ hA hAl
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦSB
  have hlimC := GlobalTheory.T.siegel_eisenstein_unfolding_identity F E σ hCM M J hJ n h2n ψ hψ dx db _ hstar d b T
  have hsum := hEu.2.1
  have htail := GlobalTheory.T.tendsto_tail_infinite_product_one _ hsum
  have hfin := fun v => GlobalTheory.T.local_gram_fibre_measure_standard_volume F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (hu _) (A v) (hA v).1 (hA v).2
  refine ⟨?_, ?_⟩
  · have hs : S₁ ⊆ S₀ ∪ S₁ := Finset.subset_union_right
    exact (hS₁ (S₀ ∪ S₁) hs φ hφm hφi' A (fun v => (hfin v).1) (fun v => (hfin v).2)
      (fun v hv => hAl v fun h => hv (Finset.mem_union_left _ h))).1
  have hev : ∀ᶠ S in Filter.atTop, S₀ ∪ S₁ ∪ S₂ ⊆ S := Filter.eventually_ge_atTop _
  have hlim2 : Filter.Tendsto (fun S => coefSN σ b J ψ dx db (pureN φ A) T S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ))
      Filter.atTop (nhds (coefN σ J ψ dx db (pureN φ A) T * ((1 : ℝ) : ℂ))) :=
    hlimC.mul ((Complex.continuous_ofReal.tendsto _).comp htail)
  have hconst : ∀ᶠ S in Filter.atTop, coefSN σ b J ψ dx db (pureN φ A) T S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) =
      ∫ X, pureN φ A X ∂I := by
    filter_upwards [hev] with S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
    have hs2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
    have hAS : ∀ v, v ∉ S → A v = latV b v := fun v hv => hAl v fun h => hv (hs0 h)
    rw [hS₂ S hs2 φ hφ A hA hAS, (hS₁ S hs1 φ hφm hφi' A (fun v => (hfin v).1) (fun v => (hfin v).2) hAS).2]
    simp
  have := tendsto_nhds_unique (hlim2.congr' hconst) tendsto_const_nhds
  simpa using this

end Pure

end GlobalTheory.CompanionTheory.SiegelND.Coef

end Body

section Final

open GlobalTheory.CompanionTheory.SiegelND.Coef

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
    μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ T : Matrix (Fin n) (Fin n) E, (∀ a b, σ (T b a) = T a b) → T.det ≠ 0 →
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n h2n ψ hψ dx hdx db hdb μ 𝓕 hμ h𝓕 Φ hΦ T hT hdet
  classical
  let b := Module.finBasis F E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨minf, hminf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1) b laminf hinf.1 n
  choose m hm using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1 n
  have hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b (GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) 1
      (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) :=
    GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero F E σ hCM n M J hJ (by omega) T hT hdet _ b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨N, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_finite_sum_of_products F E σ hCM M J hJ n h2n _ b Φ hΦ
  have hSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Coef.pureN (φ i) (A i)) := fun i =>
    GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b S (φ i) (A i) (hφ i) (hA i) (hAl i)
  have hΦe : Φ = fun X => ∑ i, Coef.pureN (φ i) (A i) X := funext hsum
  have hP := fun i => Coef.pure_identity σ hCM J hJ h2n ψ hψ dx hdx db hdb _ _ b laminf lam hinf hlam minf hminf m hm
    T hT hdet hEu S (φ i) (hφ i) (A i) (hA i) (hAl i)
  have e1 : ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) =
      ∑ i, ∫ X, Coef.pureN (φ i) (A i) X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
    simp only [hsum]
    exact integral_finsetSum _ fun i _ => (hP i).1
  rw [e1, hΦe, GlobalTheory.T.siegel_weil_hermitian_coefficient F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb T N _ hSB]
  exact Finset.sum_congr rfl fun i _ => (hP i).2

end Final
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormulaStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_hermitian_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
    μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ T : Matrix (Fin n) (Fin n) E, (∀ a b, σ (T b a) = T a b) → T.det ≠ 0 →
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta | exact GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.JPosOfIdemEx
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.JacquetPiatetskiBoundHolds
open GlobalTheory.CompanionTheory.Jp
theorem _root_.GlobalTheory.T.jacquet_piatetski_bound_holds : GlobalTheory.CompanionTheory.Jp.GoodPlacesOutsideFiniteSet := by
  first | exact @PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound | exact PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound | (intros; apply PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound <;> assumption)
end

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

theorem jPos_of_idemEx : IdemEx → JPos := by
  intro _ D n r t hrt hr ψ hψ χ hχ hres nb hnb S
  have hB2 : SplitPlaceRankCutEigenvalue := GlobalTheory.T.split_place_rank_cut_of_alternative (GlobalTheory.T.alternative_local_computation_of_components GlobalTheory.T.iwasawa_decomposition_statement GlobalTheory.T.height_bound_statement GlobalTheory.T.uniform_boundedness_statement GlobalTheory.T.compactness_statement GlobalTheory.T.positivity_statement)
  obtain ⟨v, hvS, hpsi, τ, hchi⟩ := GlobalTheory.T.jacquet_piatetski_bound_holds D r ψ hψ χ hχ hres S
  obtain ⟨C, c, hK, hd, hc, hint⟩ := hB2 D n r t hrt hr ψ hψ nb hnb v hpsi τ
  refine ⟨v, hvS, C, c, hK, hd, hc, ?_⟩
  intro νv hH hP z f _ hlaw hinv g
  exact GlobalTheory.T.section_eigenfunction_maximal_compact D n χ nb hnb v τ hchi C νv hH z (c z) (hint νv hH hP z) f hlaw hinv g

end GlobalTheory.CompanionTheory.Jp
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibEx
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExB
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

abbrev thM (V : HSp D) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (T : Matrix (Fin r) (Fin r) D.host.E) :
    Measure (Fin r → Fin V.rank → AE D) :=
  GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram μH 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = T}

theorem thInt (V : HSp D) (hr : 2 * r < V.rank) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμH : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (T : Matrix (Fin r) (Fin r) D.host.E)
    (hT : ∀ a b, D.sp.cm.sig (T b a) = T a b) (hdet : T.det ≠ 0) (Φ : (Fin r → Fin V.rank → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    Integrable Φ (thM V μH 𝓕 T) := by
  classical
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  let b := Module.finBasis D.host.F D.host.E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf D.host.F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV D.host.F
  have : BorelSpace (Ainf D.host.F) := ⟨rfl⟩
  have : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), BorelSpace (Fv D.host.F v) :=
    fun _ => ⟨rfl⟩
  obtain ⟨minf, hminf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Ainf D.host.F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf D.host.F hCM.1) b laminf hinf.1 r
  choose m hm using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Fv D.host.F v)
    (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv D.host.F v) b (lam v) (hlam v).1 r
  have hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b (thM V μH 𝓕 T) 1
      (minf (hermOf (Ainf D.host.F) D.sp.cm.sig T hT)) (fun v => m v (hermOf (Fv D.host.F v) D.sp.cm.sig T hT)) :=
    GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero D.host.F D.host.E D.sp.cm.sig hCM r V.rank V.gram hJ (by omega) T hT hdet _ b laminf lam hinf hlam
      μH 𝓕 hμH h𝓕 minf m hminf hm
  obtain ⟨N, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_finite_sum_of_products D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b Φ hΦ
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_measure_eventually_standard D.host.F D.host.E V.rank r _ b _ 1 _ _ hEu
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R],
      IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det := by
    intro R _ _
    have h : (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det = HeckeCharacterZeroLocus.SiegelWeilU.inclR R T.det :=
      ((HeckeCharacterZeroLocus.SiegelWeilU.inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR R)
  have hP : ∀ i, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i)) (thM V μH 𝓕 T) := by
    intro i
    obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_gram_fibre_measure_formula D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b laminf hinf
      minf hminf _ (hu _) (φ i) (hφ i)
    have hfin := fun v => GlobalTheory.T.local_gram_fibre_measure_standard_volume D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b v (lam v)
      (hlam v) (m v) (hm v) (hermOf (Fv D.host.F v) D.sp.cm.sig T hT) (hu _) (A i v) (hA i v).1 (hA i v).2
    exact (hS₁ (S ∪ S₁) Finset.subset_union_right (φ i) hφm hφi.self_of_nhds (A i) (fun v => (hfin v).1)
      (fun v => (hfin v).2) (fun v hv => hAl i v fun h => hv (Finset.mem_union_left _ h))).1
  have hΦe : Φ = fun X => ∑ i, GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i) X := funext hsum
  rw [hΦe]
  exact integrable_finsetSum _ fun i _ => hP i

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.FinCptOfIntegrable
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace PositivityTheory.Rg.Rsw.L.LatticeFibreBump

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem archBump [IsTotallyReal F] {M n : ℕ} (C : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (hC : IsCompact C) :
    ∃ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ ∧ ∀ Y ∈ C, φ Y = 1 := by
  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin n)
  let eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  obtain ⟨ρ, hρ⟩ := (hC.image eV.continuous).isBounded.subset_closedBall 0
  let β : ContDiffBump (0 : Fin N → ℝ) :=
    ⟨max ρ 1, max ρ 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : SchwartzMap (Fin N → ℝ) ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  refine ⟨fun X => f (eA X), ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩, fun Y hY => ?_⟩
  show ((β (eA Y) : ℝ) : ℂ) = 1
  have hm : eA Y ∈ Metric.closedBall (0 : Fin N → ℝ) β.rIn :=
    Metric.closedBall_subset_closedBall (le_max_left ρ 1) (hρ ⟨Y, hY, rfl⟩)
  rw [β.one_of_mem_closedBall hm, Complex.ofReal_one]

omit [NumberField F] [NumberField E] in
theorem repr_natCast_mul' {d : ℕ} (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R]
    [Algebra F R] (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((N : R ⊗[F] E) * y) k =
      (N : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem scaled_cpt_open {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hL : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧
      IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    IsCompact {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} ∧
      IsOpen {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  set u : Fv F v ⊗[F] E := algebraMap F _ ((N : F)⁻¹) with hu
  have hNu : (N : Fv F v ⊗[F] E) * u = 1 := by
    rw [hu, ← map_natCast (algebraMap F (Fv F v ⊗[F] E)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have hc : ∀ c : Fv F v ⊗[F] E, Continuous fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => c * Y a i :=
    fun c => continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have heq : {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} =
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => u * Y a i) '' latV b v := by
    ext Y
    constructor
    · intro hY
      refine ⟨_, hY, ?_⟩
      funext a i
      show u * ((N : Fv F v ⊗[F] E) * Y a i) = Y a i
      rw [← mul_assoc, mul_comm u, hNu, one_mul]
    · rintro ⟨Z, hZ, rfl⟩
      show (fun a i => (N : Fv F v ⊗[F] E) * (u * Z a i)) ∈ latV b v
      simpa only [← mul_assoc, hNu, one_mul] using hZ
  exact ⟨heq ▸ hL.1.image (hc u), hL.2.preimage (hc _)⟩


omit [NumberField E] in
theorem scaled_eq_lat {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hv : (algebraMap F (Af F) ((N : F)⁻¹)) v ∈ v.adicCompletionIntegers F) :
    {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} = latV b v := by
  have hw : algebraMap F (Fv F v) ((N : F)⁻¹) ∈ v.adicCompletionIntegers F := by
    have h : (algebraMap F (Af F) ((N : F)⁻¹)) v = algebraMap F (Fv F v) ((N : F)⁻¹) :=
      (evalV F v).commutes _
    rwa [h] at hv
  have hwN : algebraMap F (Fv F v) ((N : F)⁻¹) * (N : Fv F v) = 1 := by
    rw [← map_natCast (algebraMap F (Fv F v)) N, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have key : ∀ c : Fv F v, (N : Fv F v) * c ∈ v.adicCompletionIntegers F ↔ c ∈ v.adicCompletionIntegers F := by
    intro c
    constructor
    · intro h
      have := mul_mem hw h
      rwa [← mul_assoc, hwN, one_mul] at this
    · exact fun h => mul_mem (natCast_mem _ N) h
  ext Y
  simp only [Set.mem_ofPred_eq, latV, repr_natCast_mul', key]

theorem finCpt_of_integrable (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (n : ℕ) (h2n : 2 * n < M) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hν : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := F) (E := E) Φ → Integrable Φ ν) :
    IsFiniteMeasureOnCompacts ν := by
  classical
  have : IsTotallyReal F := hCM.1
  refine ⟨fun K hK => ?_⟩
  let b := Module.finBasis F E
  obtain ⟨N, R, hN, -, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hCM _ b n M).2 K hK
  obtain ⟨hcInf, -, -, hlat, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM _ b n M
  obtain ⟨φ, hφ, hφ1⟩ := archBump (projInf '' K) (hK.image hcInf)
  let A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun v => {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}
  let y : Af F := algebraMap F (Af F) ((N : F)⁻¹)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | y v ∉ v.adicCompletionIntegers F}.Finite := y.2
  have hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => scaled_cpt_open b v N hN (hlat v)
  have hAl : ∀ v, v ∉ hfin.toFinset → A v = latV b v := fun v hv =>
    scaled_eq_lat b v N hN (not_not.mp fun h => hv (hfin.mem_toFinset.mpr h))
  have hΦ := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b hfin.toFinset φ A hφ hA hAl
  have hint := hν _ hΦ
  have h1 : K ⊆ {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := by
    intro X hX
    have e1 : GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X = 1 := by
      unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
      rw [hφ1 _ ⟨X, hX, rfl⟩, Set.indicator_of_mem
        (show projFin X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxFN A from fun v => (hsub X hX).1 v), one_mul]
    simp [e1]
  calc ν K ≤ ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := measure_mono h1
    _ = 1 * ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := (one_mul _).symm
    _ ≤ ∫⁻ X, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ ∂ν := mul_meas_ge_le_lintegral₀ hint.1.enorm 1
    _ < ⊤ := hint.2

end PositivityTheory.Rg.Rsw.L.LatticeFibreBump

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

theorem thFin (V : HSp D) (hr : 2 * r < V.rank) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμH : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (T : Matrix (Fin r) (Fin r) D.host.E)
    (hT : ∀ a b, D.sp.cm.sig (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsFiniteMeasureOnCompacts (thM V μH 𝓕 T) :=
  PositivityTheory.Rg.Rsw.L.LatticeFibreBump.finCpt_of_integrable D.sp.cm.sig (GlobalTheory.DefiniteQuotient.cmExt D) V.rank V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V) r hr _ fun Φ hΦ =>
      thInt V hr μH 𝓕 hμH h𝓕 T hT hdet Φ hΦ

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExC
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}


open GlobalTheory.CompanionTheory.SiegelND in
theorem tupOf_act (V : HSp D) (h : GA D V) (X : Fin r → Fin V.rank → AE D) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h X) = mm (mt V h) (tupOf X) := by
  ext i a
  rfl


open GlobalTheory.CompanionTheory.SiegelND in
theorem ip_tupOf (V : HSp D) (X : Fin r → Fin V.rank → AE D) :
    ip V (tupOf X) (tupOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X := by
  ext a b
  exact (GlobalTheory.CompanionTheory.SiegelND.hR_tup V (tupOf X) (tupOf X) a b).symm


open GlobalTheory.CompanionTheory.SiegelND in
def tupE (D : D7) (m r : ℕ) : (Fin r → Fin m → AE D) ≃ᵐ Mx D m r where
  toFun := tupOf
  invFun := tupInv
  left_inv := tupInv_tupOf
  right_inv := tupOf_tupInv
  measurable_toFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupOf.measurable
  measurable_invFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupInv.measurable


open GlobalTheory.CompanionTheory.SiegelND in
theorem finE {m : ℕ} (ν : Measure (Fin r → Fin m → AE D)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (ν.map (tupE D m r)) := by
  refine ⟨fun K hK => ?_⟩
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D m r) ⁻¹' K = tupInv '' K := by
    ext X
    exact ⟨fun hX => ⟨tupOf X, hX, rfl⟩, fun ⟨y, hy, hyX⟩ => by subst hyX; exact hy⟩
  rw [hs]
  exact (hK.image continuous_tupInv).measure_lt_top


open GlobalTheory.CompanionTheory.SiegelND in
theorem suppE (V : HSp D) (T : Matrix (Fin r) (Fin r) D.host.E) (ν : Measure (Fin r → Fin V.rank → AE D))
    (h : ν {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ = 0) :
    ν.map (tupE D V.rank r) {x | ip V x x ≠ rat T} = 0 := by
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D V.rank r) ⁻¹' {x | ip V x x ≠ rat T} ⊆
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ := by
    intro X hX h0
    apply hX
    change ip V (tupOf X) (tupOf X) = rat T
    rw [ip_tupOf]
    exact h0
  exact measure_mono_null hs h


open GlobalTheory.CompanionTheory.SiegelND in
theorem invE (V : HSp D) (ν : Measure (Fin r → Fin V.rank → AE D)) (h : GA D V)
    (hm : Measurable (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h : (Fin r → Fin V.rank → AE D) → _))
    (hν : ν.map (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h) = ν) :
    (ν.map (tupE D V.rank r)).map (fun x => mm (mt V h) x) = ν.map (tupE D V.rank r) := by
  set e := tupE D V.rank r
  have hg : Measurable fun x : Mx D V.rank r => mm (mt V h) x := by
    have : (fun x : Mx D V.rank r => mm (mt V h) x) =
        e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h ∘ e.symm :=
      funext fun x => (tupOf_act V h (tupInv x)).symm
    rw [this]
    exact e.measurable.comp (hm.comp e.symm.measurable)
  have hc : (fun x : Mx D V.rank r => mm (mt V h) x) ∘ e = e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h :=
    funext fun X => (tupOf_act V h X).symm
  rw [Measure.map_map hg e.measurable, hc, ← Measure.map_map e.measurable hm, hν]

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

set_option maxHeartbeats 1000000 in
open GlobalTheory.CompanionTheory.SiegelND in
theorem _root_.PositivityTheory.Rg.Rsw.L.fibEx : FibEx := by
  intro D r V hr ψ hψ θ hθ μ hμ lam hlam b₀ hb₀
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨μH, 𝓕, hμH, h𝓕, -⟩ := GlobalTheory.Published.SiegelOneVector.exists_normalised D.sp.cm.sig V.gram hCM hJ
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  have hT : ∀ a b, D.sp.cm.sig (b₀.1 b a) = b₀.1 a b := fun a b => by
    have := congrFun (congrFun b₀.2 a) b
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hCM (AF D.host.F)
  have := hB r V.rank
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact _ _ D.sp.cm.sig hCM V.rank V.gram hJ (AF D.host.F)
  obtain ⟨ac, -, -, -⟩ := hact r
  have hTI := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ μH 𝓕 hμH h𝓕 r b₀.1
  have hfin := thFin V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀
  refine ⟨(thM V μH 𝓕 b₀.1).map (tupE D V.rank r), finE _, suppE V b₀.1 _ hTI.2,
    fun h => invE V _ h (ac.comp (continuous_const.prodMk continuous_id)).measurable (hTI.1 h), fun φ hφ => ?_⟩
  have hSB := GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ
  have hI := thInt V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀ _ hSB
  refine ⟨(tupE D V.rank r).measurableEmbedding.integrable_map_iff.2 hI, ?_⟩
  rw [hW φ b₀, (tupE D V.rank r).measurableEmbedding.integral_map]
  exact GlobalTheory.T.siegel_weil_hermitian_formula D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr ψ hψ dx hdx db hdb μH 𝓕 hμH h𝓕 _ hSB
    b₀.1 hT hb₀

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

theorem PositivityTheory.Rg.Rsw.resCore : PositivityTheory.Rg.Rsw.ResCore :=
  open PositivityTheory.Rg.Rsw in
  have i := PositivityTheory.Rg.Rsw.L.idemEx
  have ge := PositivityTheory.Rg.Rsw.L.goodEv i
  have be := PositivityTheory.Rg.Rsw.L.bumpEx i
  have wm := PositivityTheory.Rg.Rsw.L.wMaj
  have tp := PositivityTheory.Rg.Rsw.L.thProd wm
  have rt := PositivityTheory.Rg.Rsw.L.rowTotal i be
  have fw := PositivityTheory.Rg.Rsw.L.fixW i PositivityTheory.Rg.Rsw.L.genK wm
  have ns := PositivityTheory.Rg.Rsw.L.nullSing i
  have t2 := GlobalTheory.CompanionTheory.ColumnSplitting.main i PositivityTheory.Rg.Rsw.L.latBound GlobalTheory.CompanionTheory.QKAvg.qk PositivityTheory.Rg.Rsw.L.ikSch
  have em := PositivityTheory.Rg.Rsw.Em.eisMeas i be (PositivityTheory.Rg.Rsw.L.major i ge be) fw (PositivityTheory.Rg.Rsw.L.fixTh i PositivityTheory.Rg.Rsw.L.geng PositivityTheory.Rg.Rsw.L.genK) tp (PositivityTheory.Rg.Rsw.Cell.muCell htExist i)
    PositivityTheory.Rg.Rsw.L.fibEx (GlobalTheory.CompanionTheory.RCellP.rcell wm PositivityTheory.Rg.Rsw.L.partFT) PositivityTheory.Rg.Rsw.L.posExt (PositivityTheory.Rg.Rsw.L.approxId i)
  have mi := PositivityTheory.Rg.Rsw.L.muId i ge be tp em ns (GlobalTheory.CompanionTheory.OrbUniq.uniq_of_trans i ns (GlobalTheory.CompanionTheory.RgTrans.idemEx_trans i)) (GlobalTheory.CompanionTheory.RswNoFrame.noFrame i) t2 (PositivityTheory.Rg.Rsw.L.toS i)
  have ci := GlobalTheory.CompanionTheory.RkCoef.target polar resMu mapsExist cfFJ pcBound pcFc rSec htExist tp rt wm PositivityTheory.Rg.Rsw.L.ikSch t2 mi
  have tb := PositivityTheory.Rg.Rsw.L.thBdd wm PositivityTheory.Rg.Rsw.L.latBound PositivityTheory.Rg.Rsw.L.wa1
  have cl := PositivityTheory.Rg.Rsw.L.cutLow PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1
  have ie := (fun _ _ _ => PositivityTheory.Rg.Rsw.L.ikEq2 : PositivityTheory.Rg.Rsw.L.GenG → PositivityTheory.Rg.Rsw.L.WMaj → PositivityTheory.Rg.Rsw.L.IkSch → PositivityTheory.Rg.Rsw.L.IkEq) PositivityTheory.Rg.Rsw.L.geng wm PositivityTheory.Rg.Rsw.L.ikSch
  have tc := PositivityTheory.Rg.Rsw.L.thCoef PositivityTheory.Rg.Rsw.L.latBound
  PositivityTheory.Rg.Rsw.L.resCore polar cfFJ i ge fw wm (GlobalTheory.CompanionTheory.Jp.jPos_of_idemEx i) (PositivityTheory.Rg.Rsw.L.cfRel htExist) PositivityTheory.Rg.Rsw.L.cfInv cl
    (PositivityTheory.Rg.Rsw.L.cutId polar cfFJ ci tc PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1 PositivityTheory.Rg.Rsw.L.cfInv tb cl PositivityTheory.Rg.Rsw.L.ikSch ie wm) tb tc PositivityTheory.Rg.Rsw.L.ikSch ie
