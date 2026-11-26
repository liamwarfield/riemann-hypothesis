module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsL
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilThetaConvergenceOfSiegelSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaSumSiegelSetLeTorusPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaSumSiegelSetLeTorusPower
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusBound

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ Q : Set (GA D V), IsCompact Q → ∀ Φ : schwartzA θ V.rank n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ y ∈ Q, GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc Q hQ Φ
  have hSB := GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨-, K, hK, hmaj⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ V.rank n Φ.1 hSB
  obtain ⟨K', hK', hmul⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le D θ hθ V n Q hQ K hK
  obtain ⟨N, C₁, hC₁, hframe⟩ := GlobalTheory.T.siegelTorus_tsum_majorant_translatedRationalPoints_le D θ hθ V n r X Y hXY c hc K' hK'
  obtain ⟨C₀, hC₀⟩ := hmaj N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  set A : ℝ := max C₀ 0 * C₂ with hA
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) hC₂
  refine ⟨A * C₁, mul_nonneg hA0 hC₁, ?_⟩
  intro t ht a ha y hy
  have hpt : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      GlobalTheory.SiegelFormula.invPt V (a * y) ξ
        = (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (GlobalTheory.SiegelFormula.invPt V a ξ) : Mx D V.rank n) := by
    intro ξ
    have h2 : Formalism.L2.Theta.mt V (a * y)⁻¹ = Formalism.L2.Theta.mt V y⁻¹ * Formalism.L2.Theta.mt V a⁻¹ := by
      rw [mul_inv_rev]; rfl
    simp only [GlobalTheory.SiegelFormula.invPt, h2, Matrix.mul_assoc]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ
        ≤ ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := by
    intro ξ
    rw [← ENNReal.ofReal_mul hA0, ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [hpt ξ]
    set x := GlobalTheory.SiegelFormula.invPt V a ξ
    have h1 := hC₀ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    have h2 := hmul' y hy x
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    calc ‖Φ.1 (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)‖
        ≤ C₀ * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := h1
      _ ≤ max C₀ 0 * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ max C₀ 0 * (C₂ * GlobalTheory.Unf.maj θ K' N x) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = A * GlobalTheory.Unf.maj θ K' N x := by rw [hA, mul_assoc]
  calc GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ := rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal A * ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        by gcongr; exact hframe t ht a ha
    _ = ENNReal.ofReal (A * C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_mul hA0]; congr 1; ring

end GlobalTheory.TorusBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaSumSiegelSetLeTorusPowerStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absThetaSum_siegelSet_le_torusPower : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ Q : Set (GA D V), IsCompact Q → ∀ Φ : schwartzA θ V.rank n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ y ∈ Q, GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  first | exact @GlobalTheory.TorusBound.absTheta_le_torus | exact GlobalTheory.TorusBound.absTheta_le_torus | (intros; apply GlobalTheory.TorusBound.absTheta_le_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaIntLeSetLIntegralOfCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaIntLeSetLIntegralOfCover
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover : ∀ (D : D7) (V : HSp D) (n : ℕ) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank n → ℂ, Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → GlobalTheory.SiegelFormula.absThetaInt V ν φ ≤ ∫⁻ g in S, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
  intro D V n ν hν φ hφ S hS hcov
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hleft := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have e1 : GlobalTheory.SiegelFormula.absThetaInt V ν φ =
      ∫⁻ g in GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
    rw [GlobalTheory.SiegelFormula.absThetaInt, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure,
      lintegral_map (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hφ) GlobalTheory.AutomorphicL2Unitary.measurable_mk]
    exact lintegral_congr fun g => hleft.descend_mk g
  rw [e1]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν
    (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (GQ V) ν) hS hScov
    (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) (fun γ hγ g => hleft γ hγ g)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaIntLeSetLIntegralOfCoverStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absThetaInt_le_setLIntegral_of_cover' : ∀ (D : D7) (V : HSp D) (n : ℕ) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank n → ℂ, Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → GlobalTheory.SiegelFormula.absThetaInt V ν φ ≤ ∫⁻ g in S, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
  first | exact @GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover | exact GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover | (intros; apply GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSiegelTorusConeModulusLtTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSiegelTorusConeModulusLtTop
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelSet

theorem lintegral_cone_modulus_lt_top_of_witt : ∀ (F : Type) [Field F] [NumberField F] (m r n : ℕ) (c : ℝ), 0 < c → (r = 0 ∨ n + r < m) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (2 * n))) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F m t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ m r n c hc h
  rcases h with h | h
  · subst h
    simp only [GlobalTheory.SiegelSet.modulus, Finset.univ_eq_empty, Finset.prod_empty, mul_one, inv_one, ENNReal.ofReal_one,
      lintegral_const, one_mul]
    rw [Measure.restrict_apply MeasurableSet.univ]
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) _ < ⊤
    rw [Measure.pi_of_empty]
    exact measure_lt_top _ _
  · exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top F m r (2 * n) hc (by omega)

end GlobalTheory.SiegelSet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSiegelTorusConeModulusLtTopStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_siegelTorusCone_modulus_lt_top : ∀ (F : Type) [Field F] [NumberField F] (m r n : ℕ) (c : ℝ), 0 < c → (r = 0 ∨ n + r < m) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (2 * n))) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F m t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top_of_witt | exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top_of_witt | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top_of_witt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameColumnsLeWittIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameColumnsLeWittIndex
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittIdxBound

theorem witt_frame_le_wittIdx : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  intro D V r X Y h
  obtain ⟨ev, hev⟩ := GlobalTheory.BesselCompare.eMat_surj V X
  obtain ⟨ev', hev'⟩ := GlobalTheory.BesselCompare.eMat_surj V Y
  have hiso : ∀ a b, V.hT (ev a) (ev b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev]
    exact congrFun (congrFun h.xx a) b
  have hpair : ∀ i j, V.hT (ev i) (ev' j) = if i = j then 1 else 0 := fun i j => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev, hev', h.xy]
    simp [Matrix.one_apply]
  have hli : LinearIndependent D.host.E ev := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (fun v => V.hT v (ev' j)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, LinearMap.zero_apply] at h1
    simpa using h1
  have hmem : ∀ x ∈ Submodule.span D.host.E (Set.range ev), ∃ c : Fin r → D.host.E, ∑ i, c i • ev i = x :=
    fun x hx => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx
  apply le_csSup
  · refine ⟨Module.finrank D.host.E V.V, ?_⟩
    rintro k ⟨W, rfl, -⟩
    exact Submodule.finrank_le W
  · refine ⟨Submodule.span D.host.E (Set.range ev), ?_, ?_⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
    · intro x hx y hy
      obtain ⟨c, rfl⟩ := hmem x hx
      obtain ⟨d, rfl⟩ := hmem y hy
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hiso]

end GlobalTheory.WittIdxBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameColumnsLeWittIndexStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittFrame_columns_le_wittIndex : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  first | exact @GlobalTheory.WittIdxBound.witt_frame_le_wittIdx | exact GlobalTheory.WittIdxBound.witt_frame_le_wittIdx | (intros; apply GlobalTheory.WittIdxBound.witt_frame_le_wittIdx <;> assumption)
end
end

noncomputable section

open scoped Matrix NNReal ENNReal TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilThetaConv

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hwitt θ hθ ν hν Φ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram V)
  have hr : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := GlobalTheory.T.hermitianWittFrame_columns_le_wittIndex D V r Xf Yf hW
  have hr' : r = 0 ∨ n + r < V.rank := by rcases hwitt with h | h <;> omega
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (GlobalTheory.Doubling.isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  have hΦc : Continuous Φ.1 := (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ V.rank n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ V.rank n Φ.1 Φ.2)).1
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.absThetaSum_siegelSet_le_torusPower D θ hθ V n r Xf Yf hW c hc (C₀ * (K : Set (GA D V))) (hC₀.mul hK) Φ
  have hI := GlobalTheory.T.lintegral_siegelTorusCone_modulus_lt_top D.host.F V.rank r n c hc hr'
  calc GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1
      ≤ ∫⁻ g in GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K, GlobalTheory.SiegelFormula.absTheta V Φ.1 g ∂ν :=
        GlobalTheory.T.absThetaInt_le_setLIntegral_of_cover' D V n ν hν Φ.1 hΦc _ hcl.measurableSet hcov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
          ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (fun g => GlobalTheory.SiegelFormula.absTheta V Φ.1 g) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have e : p * a * k = a * (a⁻¹ * p * a * k) := by group
        rw [e]
        exact hC t ht a ha _ (Set.mul_mem_mul (hconj p hp t ht a ha) hk)
    _ = C₁ * (ENNReal.ofReal C * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
          ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hC0, mul_assoc]
    _ < ⊤ := by
        have := hI.ne
        finiteness

end GlobalTheory.WeilThetaConv

end
end

namespace UpperTheory.Lit

theorem siegelSetUnitary_of_core : GlobalTheory.Published.SiegelSetUnitary := PositivityTheory.ThKR.siegel_of_core PositivityTheory.Prw.siegelCore_holds

theorem weilThetaConvergence : GlobalTheory.Published.WeilThetaConvergence :=
  GlobalTheory.WeilThetaConv.weilThetaConvergence_of_siegelSet siegelSetUnitary_of_core

end UpperTheory.Lit
