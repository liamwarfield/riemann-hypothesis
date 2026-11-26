module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductFormulaDefiniteOfRallisConverge
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernels
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralEqSiegelEisensteinOfWeilRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralEqSiegelEisensteinOfWeilRange
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem thetaMean_eq_eis_of_weil : GlobalTheory.Published.WeilSiegelFormulaUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 2 * A.rank < B.rank → (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) → ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ φ : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B φ → (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧ GlobalTheory.ThetaMean.thetaMean omh mH φ = GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) := by
  intro hWeil D ψ A B ha hb hwitt χB omh homh ν 𝓕 hcov mH hmH φ hφ
  have hwitt' : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hwitt
  obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt'
  obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
  refine ⟨hint, ?_⟩
  obtain ⟨-, h2⟩ := hser hb ν 𝓕 hcov
  funext g
  rw [← swSection_eq_swSec]
  exact ((h2 g).2).symm

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralEqSiegelEisensteinOfWeilRangeStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_eq_siegelEisenstein_of_weilRange : GlobalTheory.Published.WeilSiegelFormulaUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 2 * A.rank < B.rank → (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) → ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ φ : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B φ → (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧ GlobalTheory.ThetaMean.thetaMean omh mH φ = GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) := by
  first | exact @GlobalTheory.Core.Rk.IP.thetaMean_eq_eis_of_weil | exact GlobalTheory.Core.Rk.IP.thetaMean_eq_eis_of_weil | (intros; apply GlobalTheory.Core.Rk.IP.thetaMean_eq_eis_of_weil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfHyp
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RallisInnerProductConvergentOfWeilSiegelFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConvergentInnerProductConjugateOrientationWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelNormSqModerateGrowthLarge
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelNormSqModerateGrowthLarge
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem normSq_theta_modGrowth_big : GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation →
    ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t →
    ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
    (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  intro hSWF hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat mH hmH Φ hΦ
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  obtain ⟨ha, ht, hb, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  obtain ⟨hφ, hid⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have h2ab : 2 * A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  obtain ⟨hint, hEV⟩ := GlobalTheory.T.thetaIntegral_eq_siegelEisenstein_of_weilRange hSWF D ψ A B (by omega) h2ab hw χB omh homh ν 𝓕 hP.covol mH hmH
    (delta A B Φ Φ) hφ

  have key : ∀ g h, thetaKO om g h Φ * conj (thetaKO om g h Φ) =
      ((χB (detA A g) : Circle) : ℂ) * thetaKO omh (io A (g, g)) h (delta A B Φ Φ) := by
    intro g h
    rw [(hid g g h).2]
    have e : ((χB (detA A g) : Circle) : ℂ) * (((χB (detA A g))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g h Φ * conj (thetaKO om g h Φ))) * e
  have knorm : ∀ g h, ‖thetaKO om g h Φ‖ ^ 2 = ‖thetaKO omh (io A (g, g)) h (delta A B Φ Φ)‖ := by
    intro g h
    have := congrArg norm (key g h)
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj, ← sq] at this
    rw [this]
  have hleft : ∀ g, LeftInv (GQ B) fun h => thetaKO om g h Φ := fun g γ hγ h => by
    show thetaKO om g (γ * h) Φ = thetaKO om g h Φ
    have e : ((g, γ * h) : GA D A × GA D B) = (1, γ) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hP.weil.om_aut 1 (one_mem _) _ hγ _ (hP.weil.om_pres _ _ hΦ.1)
  have hcont : ∀ g, Continuous fun h => thetaKO om g h Φ := fun g =>
    (hP.weil.om_cont Φ hΦ.1 0).comp (Continuous.prodMk_right g)
  have hL2 : ∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ := by
    intro g
    refine ⟨hleft g, ?_⟩
    have hm : AEStronglyMeasurable (descend (GQ B) fun h => thetaKO om g h Φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ B) mH) := by
      rw [aestronglyMeasurable_quotMeasure_iff_lift, (hleft g).lift_descend]
      exact (hcont g).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint (io A (g, g))).norm.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend]
    exact (knorm g _).symm
  refine ⟨hL2, ?_⟩

  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hCt, hReg⟩ := hSEC D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem
  obtain ⟨k, hk⟩ := hReg (sZero A B)
  have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
    have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, Complex.div_re]
    rw [e]
    have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast h2ab
    linarith
  have hF := hCt.1
  have hv0 := hF.eisValueAt hF.analyticOnNhd_flat hre
  have hv : GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (sZero A B)
      (ThetaMean.thetaMean omh mH (delta A B Φ Φ)) := by
    rw [hEV]; simpa only [flatH_self] using hv0
  obtain ⟨r, hr, -, -, C₁, N, hC₁⟩ := GlobalTheory.Eis.EisRegularAt.of_eisValueAt hk hv
  have hE : ∀ x, ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) x‖ ≤ C₁ * GlobalTheory.Grow.height (dblSp A) x ^ N := by
    intro x
    have e := hv.eisCont_eq
    have := hC₁ (sZero A B) (Metric.mem_ball_self hr) x
    rw [e] at this
    exact this
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (norm_nonneg _).trans (hE 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (GlobalTheory.Grow.height_pos _ _) _)
  obtain ⟨C₂, c, hC₂⟩ := GlobalTheory.Grow.IoHeight.main D A
  have hvol := GlobalTheory.RallisIP.Model.vol_pos (B := B) mH
  have hpet : ∀ g, ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖ =
      (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖ := by
    intro g
    have e1 : petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ) =
        ((χB (detA A g) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g _
    rw [e1, norm_mul, Circle.norm_coe, one_mul, ← measure_smul_average, norm_smul, ThetaMean.thetaMean,
      Real.norm_of_nonneg measureReal_nonneg]
  refine ⟨(autMeasure B mH).real Set.univ * C₁ * C₂ ^ N, 2 * c * N, fun g => ?_⟩
  rw [hpet g]
  have h2 : GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N ≤ (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := by
    refine pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ N
    have := hC₂ g g
    rwa [← sq, ← pow_mul] at this
  calc (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖
      ≤ (autMeasure B mH).real Set.univ * (C₁ * GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N) :=
        mul_le_mul_of_nonneg_left (hE _) hvol.le
    _ ≤ (autMeasure B mH).real Set.univ * (C₁ * (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁0) hvol.le
    _ = (autMeasure B mH).real Set.univ * C₁ * C₂ ^ N * GlobalTheory.Grow.height A g ^ (2 * c * N) := by
        rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelNormSqModerateGrowthLargeStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_normSq_moderateGrowth_large : GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  first | exact @GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big | exact GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big | (intros; apply GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityFlatSectionCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityFlatSectionCuspForms
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem basicIdentity_flat : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → ∀ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ → ∀ A : CptF V, ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → GlobalTheory.Eis.BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ :=
  fun hE hC D V hV a ha hI μ hμ _ _ hφ _ hθ _ m hm f₁ h₁ f₂ h₂ s hs =>
    GlobalTheory.T.doubling_basicIdentity_unfolding D V a ha μ hμ s hs _ (GlobalTheory.Eis.flat_mem hI hφ s) (GlobalTheory.T.siegelEisenstein_spherical_moderateGrowth_real_point hE D V hV a ha hI s.re hs) m hm f₁ f₂
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2)
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.2)
      (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityFlatSectionCuspFormsStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingBasicIdentity_flatSection_cuspForms : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → ∀ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ → ∀ A : CptF V, ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → GlobalTheory.Eis.BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ := by
  first | exact @GlobalTheory.Core.Rk.IP.basicIdentity_flat | exact GlobalTheory.Core.Rk.IP.basicIdentity_flat | (intros; apply GlobalTheory.Core.Rk.IP.basicIdentity_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRange
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem innerProduct_convergent : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : GlobalTheory.Core.Rk.IP.WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧ Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m ∧ petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
  intro hC hWS hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  obtain ⟨ha, ht, hb, hθ, hSig, hCart, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  obtain ⟨hφ, hid⟩ := hTC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1
  have hK := GlobalTheory.T.doublingVector_fockPair_isCompactFinite D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ hΦ₁ hΦ₂
  have h2a : 2 * A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

  obtain ⟨-, hEis⟩ := GlobalTheory.T.thetaIntegral_eq_siegelEisenstein_of_weilRange hWS D ψ A B ha h2a hw χB omh homh ν 𝓕 hP.covol mH hmH (delta A B Φ₁ Φ₂) hφ
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ₁ Φ₂) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]

  have hf₁ := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u₁ hu₁
  have hf₂ := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u₂ hu₂
  have rd : ∀ u ∈ A0 θ A cA, GlobalTheory.Grow.RapidDec A u := fun u hu =>
    GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (mem_cuspForms.1 hu).1.1 (mem_cuspForms.1 hu).1.2

  have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
    have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, Complex.div_re]
    rw [e]
    have : (A.rank : ℝ) < t := by exact_mod_cast hat
    have hb' : (B.rank : ℝ) = A.rank + t := by exact_mod_cast hb
    rw [hb']; linarith
  have hBI := GlobalTheory.T.doublingBasicIdentity_flatSection_cuspForms hSEC hC D A (by omega) a hP.maj hI χB⁻¹ hHk (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) hmem θ hθ cA m hm _ hf₁ _ hf₂ (sZero A B) hre
  simp only [flatH_self] at hBI
  obtain ⟨-, hZc, hZe⟩ := hBI

  have hpt : ∀ g, swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) *
      conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) =
      wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g := by
    intro g
    have e1 : swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) = wcoef om ν 𝓕 Φ₁ Φ₂ g :=
      (hCC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1).2 g
    have e2 : conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) = rcoef m u₁ u₂ g := by
      simp only [GlobalTheory.Eis.petCoef, rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend]
      rw [← integral_conj]
      congr 1
      ext x
      simp
    rw [e1, e2]
  have hInt : Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m := by
    have e : (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) = fun g =>
        swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) *
          starRingEnd ℂ (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) :=
      funext fun g => (hpt g).symm
    rw [e]
    exact hZc
  have hZ : GlobalTheory.Eis.dblInt A χB⁻¹ m (GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)))
      (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) = ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
    rw [hZe]
    unfold zetaH pairInt
    exact integral_congr_ae (.of_forall fun g => hpt g)

  have hKer : ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
      Continuous (Function.uncurry fun g h => thetaKO om g h Φ) ∧
      (∀ γ ∈ GQ A, ∀ g h, thetaKO om (γ * g) h Φ = thetaKO om g h Φ) ∧
      (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ) ∧
      ∀ h, GlobalTheory.Grow.ModGrowth A fun g => thetaKO om g h Φ := by
    intro Φ hΦ
    obtain ⟨hL2, hMG⟩ := GlobalTheory.T.thetaKernel_normSq_moderateGrowth_large hWS hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat mH hmH Φ hΦ
    refine ⟨hP.weil.om_cont Φ hΦ.1 0, fun γ hγ g h => ?_, hL2, hMG, fun h => ?_⟩
    · have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hP.weil.om_aut γ hγ 1 (one_mem _) _ (hP.weil.om_pres _ _ hΦ.1)
    · obtain ⟨C, N, hCN⟩ := GlobalTheory.T.theta_kernel_moderate_growth_both_variables D ψ A B χA χB om hP.weil Φ hΦ.1
      refine ⟨C * GlobalTheory.Grow.height B h ^ N, N, fun g => (hCN g h).trans (le_of_eq ?_)⟩
      rw [mul_pow]; ring
  obtain ⟨i₁, i₂, l₁, l₂, hss⟩ := GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels D A B m mH hm hmH (fun g h => thetaKO om g h Φ₁)
    (fun g h => thetaKO om g h Φ₂) (fun K hK => by
      rcases hK with rfl | rfl
      exacts [hKer Φ₁ hΦ₁, hKer Φ₂ hΦ₂]) u₁ u₂ (rd u₁ hu₁) (rd u₂ hu₂)
  refine ⟨⟨i₁, l₁⟩, ⟨i₂, l₂⟩, hInt, ?_⟩
  rw [← hZ, ← hEis]

  have key : ∀ g₁ g₂ h, thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) * thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂) := by
    intro g₁ g₂ h
    rw [(hid g₁ g₂ h).2]
    have e : ((χB (detA A g₂) : Circle) : ℂ) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂))) * e
  have hpet : ∀ g₁ g₂, petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) *
        ((volQ B mH : ℂ) * GlobalTheory.ThetaMean.thetaMean omh mH (delta A B Φ₁ Φ₂) (io A (g₁, g₂))) := by
    intro g₁ g₂
    have e1 : petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
        ((χB (detA A g₂) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂)) q
            ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g₁ g₂ _
    rw [e1, ← measure_smul_average, GlobalTheory.ThetaMean.thetaMean, Complex.real_smul]
    rfl
  have hss' : petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = _ := hss
  rw [hss', GlobalTheory.Eis.dblInt, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun q => ?_)
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, hpet, MonoidHom.inv_apply, Circle.coe_inv, inv_inv,
    RCLike.conj_conj]
  ring

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRangeStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : GlobalTheory.Core.Rk.IP.WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧ Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m ∧ petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
  first | exact @GlobalTheory.Core.Rk.IP.innerProduct_convergent | exact GlobalTheory.Core.Rk.IP.innerProduct_convergent | (intros; apply GlobalTheory.Core.Rk.IP.innerProduct_convergent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConvergentInnerProductConjugateOrientationWeil
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.IP

variable {D : D7}

theorem integrable_star_comp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ := by
  simpa using (Complex.conjCLE.toContinuousLinearMap).integrable_comp hf

theorem memL2_conj_comp (V : HSp D) (μ : Measure (GA D V)) {f : GA D V → ℂ}
    (hf : MemL2Quotient (GQ V) μ f) : MemL2Quotient (GQ V) μ (fun x => conj (f x)) := by
  refine ⟨fun γ hγ g => by simp only [hf.1 γ hγ g], ?_⟩
  have := (Complex.conjCLE.toContinuousLinearMap).comp_memLp' hf.2
  convert this using 1
  funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem petersson_star_comp (V : HSp D) (μ : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) :
    petersson V μ (fun x => conj (f₁ x)) (fun x => conj (f₂ x)) = conj (petersson V μ f₁ f₂) := by
  simp only [petersson, pet]
  rw [← integral_conj]
  congr 1; funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem innerProduct_convergent_conj : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ) (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ), HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c → m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₁ f₁ ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₂ f₂ ∧ Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧ petersson B ν (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₁ f₁) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m := by
  intro hRD hWS hSE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hw ht hK hm hν hf₁ hf₂
  obtain ⟨om, Φ₁, Φ₂, hW, hF₁, hF₂, -, -, hK₁, hK₂, μ, 𝓕, hcov, hc⟩ := hK
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.T.exists_adelicMajorantFrame_for_cartanInvolutions D θ A sA hS.2.2.2.1 hS.2.2.2.2.2.2.1
  have hP : Pair ψ θ A B χA χB sA sB t cA a om μ 𝓕 := ⟨hS, ha, ha', hW, hcov⟩
  obtain ⟨hU₁, hU₂, hI, hE⟩ := GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range hRD hWS hSE D ψ θ A B χA χB sA sB t cA a om μ 𝓕 hP hw ht m ν hm hν
    Φ₁ Φ₂ hF₁ hF₂ f₁ hf₁ f₂ hf₂
  have hcg : ∀ g, c g = conj (wcoef om μ 𝓕 Φ₁ Φ₂ g) := by
    intro g
    have h1 : wcoef om μ 𝓕 Φ₁ Φ₂ g = conj (c g) := by
      have h2 := hc g
      simp only at h2
      rw [h2]; rfl
    rw [h1, Complex.conj_conj]
  have hlift : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K u = fun h => conj (up om m Φ u h) := by
    intro K Φ u hK; funext h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift, up, petersson, pet, hK]
    rw [← integral_conj]
    congr 1; funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend]
  have hconv : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) → UpConv om m ν Φ u → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K u := by
    intro K Φ u hK hU
    refine ⟨fun h => ?_, ?_⟩
    · have := integrable_star_comp (hU.1 h)
      convert this using 2 with q
      simp [GlobalTheory.AutomorphicL2Unitary.descend, hK]
    · rw [hlift K Φ u hK]
      exact memL2_conj_comp B ν hU.2
  refine ⟨hconv K₁ Φ₁ f₁ hK₁ hU₁, hconv K₂ Φ₂ f₂ hK₂ hU₂, ?_, ?_⟩
  · have := integrable_star_comp hI
    convert this using 2 with g
    simp [hcg, rcoef]
  · rw [hlift K₁ Φ₁ f₁ hK₁, hlift K₂ Φ₂ f₂ hK₂, petersson_star_comp, hE, map_mul, ← integral_conj]
    simp [hcg, rcoef]

end GlobalTheory.Core.Rk.IP

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConvergentInnerProductConjugateOrientationWeilStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergentInnerProduct_conjugateOrientation_weil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ) (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ), HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c → m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₁ f₁ ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₂ f₂ ∧ Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧ petersson B ν (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₁ f₁) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m := by
  first | exact @GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj | exact GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj | (intros; apply GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelPairFlipConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelPairFlipConjugate
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.KernelFlip

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem annih_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T)
    {aS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {bT : Matrix (Fin T.rank) (Fin T.rank) ℂ} (τ : D.what₂.Tau)
    (hS : IsCartanInv (gramAt D S τ) aS) (hT : IsCartanInv (gramAt D T τ) bT)
    (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ T S) θ τ (cplxO bT aS) w (dag S T f) =
      dag S T (annih (heisO ψ S T) θ τ (cplxO aS bT) (GlobalTheory.FockAdjoint.cdag S T τ w) f) := by
  unfold annih
  rw [GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.cdag_cplx τ hS hT,
    GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hf]
  funext x
  simp only [dag, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, map_add (f := _), map_mul, map_neg, Complex.conj_I]
  ring

theorem annih_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf))

theorem foldr_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS : RealMat S) (sT : RealMat T)
    (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => exact hg
  | cons p l ih => exact annih_theta hψ hθ _ _ _ ih

theorem foldr_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (l : List (D.what₂.Tau × Matrix (Fin S.rank) (Fin T.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    l.foldr (fun p f => annih (heisO ψ T S) θ p.1 (cplxO (sT p.1) (sS p.1)) p.2 f) (dag S T g) =
      dag S T ((l.map fun p => (p.1, GlobalTheory.FockAdjoint.cdag S T p.1 p.2)).foldr
        (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih, annih_dag hψ hθ L p.1 (hS p.1) (hT p.1) _ (foldr_theta hψ hθ sS sT _ hg)]

theorem fock_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) {Φ : WO S T → ℂ}
    (h : IsFockVec ψ θ S T sS sT Φ) : IsFockVec ψ θ T S sT sS (dag S T Φ) := by
  obtain ⟨hth, N, hN⟩ := h
  refine ⟨L.theta Φ hth, N, fun l hl => ?_⟩
  rw [foldr_dag hψ hθ L sS sT hS hT l hth, hN _ (by simpa using hl)]
  funext x
  simp [dag]

theorem coef_dag (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) {X : Type} (x : X → WO T S → ℂ) (x' : X → WO S T → ℂ)
    (hx : ∀ p, x' p = dag T S (x p)) (Φ : WO T S → ℂ) (c : X → ℂ) (h : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef T S x Φ c) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef S T x' (dag T S Φ) fun p => starRingEnd ℂ (c p) := by
  obtain ⟨μ, 𝓕, ⟨hμ, h𝓕, h1⟩, hc⟩ := h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have : BorelSpace (WO T S) := ⟨rfl⟩
  have : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, ⟨hHaar, hF, ?_⟩, fun p => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · show starRingEnd ℂ (c p) = _
    rw [hc p, MeasurableEquiv.restrict_map, hpre, integral_map_equiv, ← integral_conj, hx p]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have ew : eM.symm (eM w) = w := eM.symm_apply_apply w
    show starRingEnd ℂ (x p w * starRingEnd ℂ (Φ w)) =
      dag T S (x p) (eM w) * starRingEnd ℂ (dag T S Φ (eM w))
    simp only [dag]
    have e2 : adjO T S (eM w) = w := hTS.invol w
    rw [e2, map_mul]

end GlobalTheory.KernelFlip


open GlobalTheory.KernelFlip in
theorem GlobalTheory.KernelFlip.kernelPair_flip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB true (fun _ => True) (fun _ => True) K₁ K₂ c → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c := by
  intro D ψ θ A B χA χB sA sB K₁ K₂ c hθ hsA hsB hK
  obtain ⟨om, Φ₁, Φ₂, H, hF₁, hF₂, -, -, hK₁, hK₂, hc⟩ := hK
  have hψ : IsStdChar D ψ (-1) := H.std
  have hBA : AdjLaw ψ B A := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hψ B A
  have hAB : AdjLaw ψ A B := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hψ A B
  obtain ⟨om', H', hom'⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ B A χB χA om H
  have hθK : ∀ (g : GA D A) (h : GA D B) (Φ : WO B A → ℂ),
      starRingEnd ℂ (thetaKO om' g h (dag B A Φ)) = thetaKO om h g Φ := by
    intro g h Φ
    simp only [thetaKO]
    rw [hom' h g Φ]
    simp only [dag]
    rw [GlobalTheory.WeilConj.adjO_zero hBA, Complex.conj_conj]
  refine ⟨om', dag B A Φ₁, dag B A Φ₂, H', fock_dag hψ hθ hBA sB sA hsB hsA hF₁,
    fock_dag hψ hθ hBA sB sA hsB hsA hF₂, trivial, trivial, fun g h => ?_, fun g h => ?_, ?_⟩
  · rw [hθK, hK₁]
  · rw [hθK, hK₂]
  · exact coef_dag hAB hBA (fun g : GA D A => om (1, g) Φ₁) (fun g : GA D A => om' (g, 1) (dag B A Φ₁))
      (fun g => hom' 1 g Φ₁) Φ₂ c hc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelPairFlipConjugateStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernelPair_flip_conjugate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB true (fun _ => True) (fun _ => True) K₁ K₂ c → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c := by
  first | exact @GlobalTheory.KernelFlip.kernelPair_flip | exact GlobalTheory.KernelFlip.kernelPair_flip | (intros; apply GlobalTheory.KernelFlip.kernelPair_flip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RallisInnerProductConvergentOfWeilSiegelFormula
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Proof.Corev

theorem convergent_both_orientations :
    GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D := by
  intro hR hW hE D ψ θ A B χA χB sA sB t cA o K₁ K₂ c m ν f₁ f₂ hS hρ ht hK hm hν hf₁ hf₂
  cases o with
  | false => exact GlobalTheory.T.convergentInnerProduct_conjugateOrientation_weil hR hW hE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hρ ht hK hm hν hf₁ hf₂
  | true =>
    obtain ⟨_, _, _, hθ, _, _, hA, hB, _⟩ := id hS
    exact GlobalTheory.T.convergentInnerProduct_conjugateOrientation_weil hR hW hE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hρ ht
      (GlobalTheory.T.thetaKernelPair_flip_conjugate D ψ θ A B χA χB sA sB K₁ K₂ c hθ hA hB hK) hm hν hf₁ hf₂

end GlobalTheory.Proof.Corev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RallisInnerProductConvergentOfWeilSiegelFormulaStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallisInnerProduct_convergent_of_weilSiegelFormula : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D := by
  first | exact @GlobalTheory.Proof.Corev.convergent_both_orientations | exact GlobalTheory.Proof.Corev.convergent_both_orientations | (intros; apply GlobalTheory.Proof.Corev.convergent_both_orientations <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem innerProductFormula_of_hypotheses : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  intro hDecay hWeil hCont D G _ _ Pl0 T A Ks _ _ _ R F hL
  exact GlobalTheory.T.thetaInnerProductFormulaDefinite_of_rallisConvergent hDecay R F (GlobalTheory.T.rallisInnerProduct_convergent_of_weilSiegelFormula hDecay hWeil hCont D) hL

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  first | exact @GlobalTheory.innerProductFormula_of_hypotheses | exact GlobalTheory.innerProductFormula_of_hypotheses | (intros; apply GlobalTheory.innerProductFormula_of_hypotheses <;> assumption)
