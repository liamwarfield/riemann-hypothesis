module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMajorant

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsIsCovolOneRatMx
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi Formalism.IndefR.Mult MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatMxCovol

theorem exists_isCovolOne_ratMx : ∀ (D : D7) (m n : ℕ), ∃ (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 := by
  intro D m n
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  exact GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (Mx D m n) (ratMx D m n) ⟨i5, K, hK, hc⟩

end GlobalTheory.CompanionTheory.RatMxCovol
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFinite
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem weil_fock_mem (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) (hr : ResEta D χ V.rank) (θ : InfFam D) (hθ : IsInfFam θ)
    (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (hω : IsWeilSch ψ χ θ V μ ω)
    (l : D.what₂.Tau → ℝ) (hl : HasRealPar ψ θ l) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (Φ : schwartzA θ V.rank n) (hΦ : Φ.1 ∈ fockA θ V n l s)
    (k : G D n) (hk : k ∈ K D n) : (ω k Φ).1 ∈ fockA θ V n l s := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  obtain ⟨hth, N, hN⟩ := hfock
  have hk' : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    ⟨hdat.om_pres _ f hth, N,
      GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ (κ.symm k) (hcomm _ hk') N f hth hN⟩
  have hmem := GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have htrk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htrk
  exact Eq.mpr (congrArg (fun φ : Mx D V.rank n → ℂ => φ ∈ fockA θ V n l s) htrk) hmem

theorem weilKFin : WeilKFin := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  have hfin := GlobalTheory.StdUnn.KFin.fock_kfinite D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  set S := Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ} with hS
  refine ⟨S.map (schwartzA θ V.rank n).subtype, Module.Finite.map S _, ?_, ?_⟩
  · rw [hS, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Ψ, ⟨k, hk, rfl⟩, rfl⟩
    exact weil_fock_mem D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ k hk
  · intro k hk
    exact ⟨ω k Φ, Submodule.subset_span ⟨k, hk, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFiniteStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_K_finite : WeilKFin := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilKFin | exact GlobalTheory.CompanionTheory.ThTot.weilKFin | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilKFin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.LeftInvSect
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem iwaCpt : IwaCpt := by
  intro D n C hC
  have hCK : IsCompact (C * (K D n : Set (G D n))⁻¹) := hC.mul isCompact_K.inv
  have hQ : IsCompact ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) :=
    (isClosed_P (D := D) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hCK
  have hL := hQ.image (continuous_leviBlock (D := D) (n := n))
  set L := leviBlock (D := D) (n := n) '' ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) with hLdef
  have hR : Continuous fun a : GL (Fin n) (AE D) => (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_absE.comp continuous_detGL)
  obtain ⟨R, hRb⟩ := (hL.image hR).bddAbove
  refine ⟨Units.val '' L, (fun a : GL (Fin n) (AE D) => (a⁻¹).1) '' L, R, hL.image Units.continuous_val,
    hL.image Units.continuous_coe_inv, fun h hh => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := Iwasawa.exists_mul D n h
  have hmem : leviBlock (D := D) (n := n) ⟨q, hq⟩ ∈ L :=
    ⟨⟨q, hq⟩, ⟨q * k, hh, k⁻¹, Set.inv_mem_inv.2 hk, by simp⟩, rfl⟩
  obtain ⟨m, t, b, e, hm, ht⟩ := exists_levi_unip hq (leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  exact ⟨m, t, k, _, b, hk, by rw [e], hm, ht, ⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩, hRb ⟨_, hmem, rfl⟩⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactnessStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt | exact GlobalTheory.CompanionTheory.ThTot.iwaCpt | (intros; apply GlobalTheory.CompanionTheory.ThTot.iwaCpt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTotalOfEuclidean
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTotalOfEuclidean
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem eq_zero_of_orth_SB {Y : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [ν.IsAddHaarMeasure] (f : Y → ℂ) (hf : Continuous f)
    (h : ∀ k ∈ GlobalTheory.WeilM.SB Y, ∫ y, f y * conj (k y) ∂ν = 0) : f = 0 := by
  funext y0
  by_contra hne
  have hpos : 0 < ‖f y0‖ := norm_pos_iff.2 hne
  have hN : {y | ‖f y - f y0‖ < ‖f y0‖ / 2} ∈ 𝓝 y0 :=
    (isOpen_lt (hf.sub continuous_const).norm continuous_const).mem_nhds (by simpa using hpos)
  obtain ⟨C, hCa, hCu, hC⟩ := local_compact_nhds hN
  obtain ⟨U, hU, hyU, hUC⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := Y)).mem_nhds_iff.mp hCa
  have hUc : IsCompact U := hC.of_isClosed_subset hU.1 hUC
  have hk : U.indicator (1 : Y → ℂ) ∈ GlobalTheory.WeilM.SB Y :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hU).isLocallyConstant,
      HasCompactSupport.intro' hUc hU.isClosed (fun x hx => Set.indicator_of_notMem hx _)⟩
  have h0 : ∫ y in U, f y ∂ν = 0 := by
    rw [← h _ hk, ← integral_indicator hU.2.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ U <;> simp [hy]
  have hfin : ν U < ∞ := hUc.measure_lt_top
  have hνpos : 0 < ν.real U := by
    refine ENNReal.toReal_pos (hU.2.measure_pos ν ⟨y0, hyU⟩).ne' hfin.ne
  have hint : IntegrableOn f U ν := hf.continuousOn.integrableOn_compact hUc
  have hc : ∫ y in U, (f y - f y0) ∂ν = - (ν.real U • f y0) := by
    rw [integral_sub hint (integrableOn_const hfin.ne), h0, setIntegral_const, zero_sub]
  have hb : ‖∫ y in U, (f y - f y0) ∂ν‖ ≤ ‖f y0‖ / 2 * ν.real U :=
    norm_setIntegral_le_of_norm_le_const hfin fun y hy => (hCu (hUC hy)).le
  rw [hc, norm_neg, norm_smul, Real.norm_of_nonneg hνpos.le] at hb
  nlinarith

theorem total_of_split {G Z Y : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [LocallyCompactSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : G ≃ₜ+ Z × Y) (m : Measure G) [m.IsAddHaarMeasure] (lam : Measure Z) [lam.IsAddHaarMeasure]
    (ν : Measure Y) [ν.IsAddHaarMeasure] (T : Set (Z → ℂ)) (hT : ∀ t ∈ T, Continuous t ∧ Integrable t lam)
    (hE : ∀ w : Z → ℂ, Continuous w → (∃ B : ℝ, ∀ z, ‖w z‖ ≤ B) → (∀ t ∈ T, ∫ z, w z * conj (t z) ∂lam = 0) → w = 0)
    (u : G → ℂ) (hu : Continuous u) (hB : ∃ B : ℝ, ∀ x, ‖u x‖ ≤ B)
    (h : ∀ t ∈ T, ∀ k ∈ GlobalTheory.WeilM.SB Y, ∫ x, u x * conj (t (e x).1 * k (e x).2) ∂m = 0) : u = 0 := by
  obtain ⟨B, hB⟩ := hB
  haveI : (lam.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure lam ν
  haveI : (m.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  have hmap := Measure.isAddLeftInvariant_eq_smul (m.map e) (lam.prod ν)
  have hcpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (m.map e) (lam.prod ν)
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  set v : Z × Y → ℂ := fun p => u (e.symm p) with hv
  have hvc : Continuous v := hu.comp e.symm.continuous
  have hvB : ∀ p, ‖v p‖ ≤ B := fun p => hB _
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hvB (Classical.choice (by infer_instance : Nonempty (Z × Y))))
  have hkey : ∀ k ∈ GlobalTheory.WeilM.SB Y, ∀ z, ∫ y, v (z, y) * conj (k y) ∂ν = 0 := by
    intro k hk
    have hkc : Continuous k := hk.1.continuous
    have hki : Integrable k ν := hkc.integrable_of_hasCompactSupport hk.2
    have hcc : Continuous fun y => conj (k y) := Complex.continuous_conj.comp hkc
    have hw : (fun z => ∫ y, v (z, y) * conj (k y) ∂ν) = 0 := by
      refine hE _ ?_ ⟨∫ y, B * ‖k y‖ ∂ν, fun z => ?_⟩ fun t ht => ?_
      · refine continuous_of_dominated (bound := fun y => B * ‖k y‖) (fun z => ?_) (fun z => ?_) (hki.norm.const_mul B) ?_
        · exact ((hvc.comp (Continuous.prodMk_right z)).mul hcc).aestronglyMeasurable
        · refine Eventually.of_forall fun y => ?_
          rw [norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_right (hvB _) (norm_nonneg _)
        · refine Eventually.of_forall fun y => ?_
          exact (hvc.comp (Continuous.prodMk_left y)).mul continuous_const
      · refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hki.norm.const_mul B) (Eventually.of_forall fun y => ?_))
        show ‖v (z, y) * conj (k y)‖ ≤ B * ‖k y‖
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_right (hvB _) (norm_nonneg _)
      · obtain ⟨htc, hti⟩ := hT t ht
        set F : Z × Y → ℂ := fun p => v p * conj (t p.1 * k p.2) with hF
        have hFc : Continuous F := hvc.mul (Complex.continuous_conj.comp ((htc.comp continuous_fst).mul (hkc.comp continuous_snd)))
        have hFi : Integrable F (lam.prod ν) := by
          refine ((hti.mul_prod hki).norm.const_mul B).mono' hFc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
          simp only [hF, norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_right (hvB _) (by positivity)
        have h1 : ∫ x, u x * conj (t (e x).1 * k (e x).2) ∂m = ((Measure.addHaarScalarFactor (m.map e) (lam.prod ν) : ℝ≥0) : ℝ) • ∫ p, F p ∂(lam.prod ν) := by
          have : ∫ p, F p ∂(m.map e) = ∫ x, F (e x) ∂m := hemb.integral_map F
          have h2 : ∀ x, F (e x) = u x * conj (t (e x).1 * k (e x).2) := fun x => by simp [hF, hv]
          simp only [h2] at this
          rw [← this]
          conv_lhs => rw [hmap]
          rw [integral_smul_nnreal_measure, NNReal.smul_def]
        have h3 : ∫ p, F p ∂(lam.prod ν) = 0 := by
          have := h1.symm.trans (h t ht k hk)
          exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hcpos.ne')
        rw [integral_prod F hFi] at h3
        rw [← h3]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hF, map_mul]
        rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring
    intro z
    exact congrFun hw z
  funext x
  have h0 := eq_zero_of_orth_SB ν (fun y => v ((e x).1, y)) (hvc.comp (Continuous.prodMk_right _))
    (fun k hk => hkey k hk (e x).1)
  have := congrFun h0 (e x).2
  simpa [hv] using this

section Poly

variable {D : D7} {m n : ℕ}

def coordV (k : D.what₂.Tau × Fin m × Fin n × Bool) (z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1

def polyV (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℂ :=
  evalPoly q fun τ => Matrix.of (z τ)

theorem polyV_eq (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    polyV q z = MvPolynomial.eval (fun k => coordV k z) q := rfl

def coordL (k : D.what₂.Tau × Fin m × Fin n) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1))

theorem coordL_apply (k : D.what₂.Tau × Fin m × Fin n) (z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    coordL k z = z k.1 k.2.1 k.2.2 := rfl

theorem coordV_temperate (k : D.what₂.Tau × Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coordV (D := D) k) := by
  obtain ⟨τ, i, j, b⟩ := k
  cases b
  · exact (coordL (D := D) (τ, i, j)).hasTemperateGrowth
  · exact (((Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp (coordL (D := D) (τ, i, j))).hasTemperateGrowth

theorem polyV_temperate (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (polyV q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : polyV (D := D) (m := m) (n := n) (MvPolynomial.C a) = fun _ => a := by
      funext z; simp [polyV_eq]
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : polyV (p + q) = fun z => polyV p z + polyV q z := by
      funext z; simp [polyV_eq]
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : polyV (p * MvPolynomial.X k) = fun z => polyV p z * coordV k z := by
      funext z; simp [polyV_eq]
    rw [this]; exact hp.mul (coordV_temperate k)

theorem exists_conj_polyV (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∃ q' : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ, ∀ z, conj (polyV q z) = polyV q' z := by
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C (conj a), fun z => by simp [polyV_eq]⟩
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', fun z => ?_⟩
    have h1 := hp z
    have h2 := hq z
    simp only [polyV_eq, map_add (f := _)] at h1 h2 ⊢
    rw [h1, h2]
  | mul_X p k hp =>
    obtain ⟨p', hp⟩ := hp
    refine ⟨p' * MvPolynomial.X (k.1, k.2.1, k.2.2.1, !k.2.2.2), fun z => ?_⟩
    have h1 := hp z
    simp only [polyV_eq, map_mul, MvPolynomial.eval_X] at h1 ⊢
    rw [h1]
    congr 1
    obtain ⟨τ, i, j, b⟩ := k
    cases b <;> simp [coordV]

def polyAlg (D : D7) (m n : ℕ) : Subalgebra ℂ ((D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ) :=
  (MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ) (coordV (D := D) (m := m) (n := n))).range

theorem aeval_coordV (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ) (coordV (D := D) (m := m) (n := n)) q = polyV q := by
  induction q using MvPolynomial.induction_on with
  | C a => funext z; simp [polyV_eq]
  | add p q hp hq => funext z; simp [polyV_eq, hp, hq]
  | mul_X p k hp => funext z; simp [polyV_eq, hp]

end Poly

section Gauss

variable {D : D7} {p : ℕ}

theorem gram_at_place_rank_one (τ : D.what₂.Tau) : gramAt D (V1 D) τ = 1 := by
  have h : (V1 D).gram = 1 := by
    refine Matrix.ext fun i j => ?_
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0 i j).trans ?_
    show (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
    rfl
  show (HSpace.gram (V1 D)).map (tauE D τ) = 1
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

open scoped ComplexOrder in
theorem cartan_one (k : ℕ) : IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 :=
  ⟨mul_one _, by simp, by simpa using Matrix.PosDef.one⟩

def sqSum (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) : ℝ :=
  ∑ τ, |l τ| * ∑ j, ∑ i, ‖z τ i j‖ ^ 2

def gaussR (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) : ℝ :=
  Real.exp (-(2 * Real.pi) * sqSum l z)

theorem gauss_eq (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) :
    gauss (V1 D) l (fun _ => 1) (fun τ => Matrix.of (z τ)) = (gaussR l z : ℂ) := by
  rw [gauss, gaussR, Complex.ofReal_exp, sqSum]
  congr 1
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [gram_at_place_rank_one, mul_one, Matrix.mul_one, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul' (z τ i j)]
  rfl

theorem continuous_gaussR (l : D.what₂.Tau → ℝ) : Continuous (gaussR (D := D) (p := p) l) := by
  unfold gaussR sqSum
  fun_prop

theorem gaussR_le (l : D.what₂.Tau → ℝ) (L : ℝ) (hL0 : 0 < L) (hL : ∀ τ, L ≤ |l τ|)
    (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) :
    gaussR l z ≤ 1 * Real.exp (-(2 * Real.pi * L) * ‖z‖ ^ 2) := by
  rw [one_mul, gaussR]
  refine Real.exp_le_exp.2 ?_
  have hS : ∀ τ, 0 ≤ ∑ j, ∑ i, ‖z τ i j‖ ^ 2 := fun τ => by positivity
  have h1 : L * ∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2 ≤ sqSum l z := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right (hL τ) (hS τ)
  have h2 : ‖z‖ ^ 2 ≤ ∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2 := by
    have h3 : ‖z‖ ≤ Real.sqrt (∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun τ => (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => Real.le_sqrt_of_sq_le ?_
      calc ‖z τ i j‖ ^ 2 ≤ ∑ i, ‖z τ i j‖ ^ 2 :=
            Finset.single_le_sum (f := fun i => ‖z τ i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
        _ ≤ ∑ j, ∑ i, ‖z τ i j‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ∑ i, ‖z τ i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
        _ ≤ _ := Finset.single_le_sum (f := fun τ => ∑ j, ∑ i, ‖z τ i j‖ ^ 2) (fun τ _ => hS τ) (Finset.mem_univ τ)
    calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun τ _ => hS τ)
  have hp := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left h2 hL0.le]

end Gauss

theorem fockTotal_of_eucTotal : EucTotal → FockTotal := by
  intro hEuc D p θ hθ l hl μ 𝓕 hμ u hu hB horth
  haveI := hμ.1
  haveI : IsModuleTopology (Af D.host.F) (GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (GlobalTheory.RegSch.IkSchwartz.AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  haveI : TotallyDisconnectedSpace (Af D.host.F) := GlobalTheory.TamePartR.totallyDisconnected_finiteAdele D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.secondCountableTopology
  haveI : T2Space (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isEmbedding.t2Space
  haveI : TotallyDisconnectedSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.symm.totallyDisconnectedSpace
  letI : MeasurableSpace (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := borel _
  haveI : BorelSpace (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (V1 D).rank p) := ⟨rfl⟩
  haveI := (lattice_Mx D (V1 D).rank p).1
  obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ (V1 D).rank p
  let lam : Measure (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) := Measure.addHaar
  let ν : Measure (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := Measure.addHaar
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D p (V1 D) l hl (fun _ => 1) (fun τ => by
    rw [gram_at_place_rank_one]
    exact cartan_one _)
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 < L ∧ ∀ τ, L ≤ |l τ| := by
    rcases isEmpty_or_nonempty D.what₂.Tau with h | h
    · exact ⟨1, one_pos, fun τ => (h.false τ).elim⟩
    · obtain ⟨τ₀, -, h₀⟩ := Finset.exists_min_image Finset.univ (fun τ => |l τ|) Finset.univ_nonempty
      exact ⟨|l τ₀|, abs_pos.2 (hl τ₀), fun τ => h₀ τ (Finset.mem_univ τ)⟩
  refine total_of_split e μ lam ν
    {t | ∃ q : MvPolynomial (D.what₂.Tau × Fin (V1 D).rank × Fin p × Bool) ℂ, ∀ z, t z = polyV q z * (gaussR l z : ℂ)}
    ?_ ?_ u hu hB ?_
  · rintro t ⟨q, hq⟩
    have ht : t = SchwartzMap.smulLeftCLM ℂ (polyV q) f := by
      funext z
      rw [SchwartzMap.smulLeftCLM_apply_apply (polyV_temperate q), hq, hf, gauss_eq]
      rfl
    rw [ht]
    exact ⟨SchwartzMap.continuous _, SchwartzMap.integrable _⟩
  · intro w hw hwB hwt
    refine hEuc _ lam (D.what₂.Tau × Fin (V1 D).rank × Fin p) coordL (fun z hz => ?_) (polyAlg D _ p) (fun k => ?_) (fun k => ?_)
      (gaussR l) (continuous_gaussR l) (fun z => Real.exp_pos _) 1 (2 * Real.pi * L) (by positivity) (fun z => ?_) w hw hwB ?_
    · funext τ i j
      exact hz (τ, i, j)
    · refine ⟨MvPolynomial.X (k.1, k.2.1, k.2.2, false), ?_⟩
      refine (MvPolynomial.aeval_X _ _).trans ?_
      funext z
      simp [coordV, coordL_apply]
    · refine ⟨MvPolynomial.X (k.1, k.2.1, k.2.2, true), ?_⟩
      refine (MvPolynomial.aeval_X _ _).trans ?_
      funext z
      simp [coordV, coordL_apply]
    · have := gaussR_le l L hL0 hL z
      simpa [neg_mul] using this
    · rintro P ⟨q, rfl⟩
      obtain ⟨q', hq'⟩ := exists_conj_polyV q
      have := hwt (fun z => polyV q' z * (gaussR l z : ℂ)) ⟨q', fun z => rfl⟩
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      have h1 : (MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) → ℂ) (coordV (D := D) (m := (V1 D).rank) (n := p))) q = polyV q := aeval_coordV q
      show w z * ((MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) → ℂ) (coordV (D := D) (m := (V1 D).rank) (n := p))) q) z * _ = _
      rw [h1]
      show w z * polyV q z * (gaussR l z : ℂ) = w z * conj (polyV q' z * (gaussR l z : ℂ))
      rw [map_mul, ← hq' z, Complex.conj_conj, Complex.conj_ofReal, mul_assoc]
  · rintro t ⟨q, hq⟩ k hk
    have := horth (fun x => evalPoly q (fun τ => compAt θ τ x) * gauss (V1 D) l (fun _ => 1) (fun τ => compAt θ τ x) *
      k (fun i j => finPart D (x i j))) (Submodule.subset_span ⟨q, k, hk, rfl⟩)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show u x * conj (t (e x).1 * k (e x).2) = u x * conj (evalPoly q (fun τ => compAt θ τ x) * gauss (V1 D) l (fun _ => 1) (fun τ => compAt θ τ x) *
      k (fun i j => finPart D (x i j)))
    rw [hq, he, ← gauss_eq]
    rfl

end GlobalTheory.CompanionTheory.ThTot
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTotalOfEuclideanStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_total_of_euclidean : EucTotal → FockTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal | exact GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.fockTotal_of_eucTotal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotal
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.ThTot.EucT

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z]

lemma exp_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Real.exp (b * r - a * r ^ 2) ≤
      ((n.factorial : ℝ) * Real.exp (1 + (1 + b) ^ 2 / (4 * a))) * (1 + r) ^ (-(n : ℝ)) := by
  have h1 : (1 + r) ^ n / (n.factorial : ℝ) ≤ Real.exp (1 + r) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have h1' : (1 + r) ^ n ≤ (n.factorial : ℝ) * Real.exp (1 + r) := by
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have h2 : (1 + r) + (b * r - a * r ^ 2) ≤ 1 + (1 + b) ^ 2 / (4 * a) := by
    have e : (1 + b) ^ 2 / (4 * a) - ((1 + b) * r - a * r ^ 2) = (1 + b - 2 * a * r) ^ 2 / (4 * a) := by
      field_simp
      ring
    have h3 : 0 ≤ (1 + b - 2 * a * r) ^ 2 / (4 * a) := by positivity
    nlinarith
  have hp : 0 < (1 + r) ^ n := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
  calc Real.exp (b * r - a * r ^ 2) * (1 + r) ^ n
      ≤ Real.exp (b * r - a * r ^ 2) * ((n.factorial : ℝ) * Real.exp (1 + r)) := by gcongr
    _ = (n.factorial : ℝ) * Real.exp ((1 + r) + (b * r - a * r ^ 2)) := by
        rw [Real.exp_add (1 + r) (b * r - a * r ^ 2)]; ring
    _ ≤ _ := by gcongr

lemma integrable_gauss (lam : Measure Z) [lam.IsAddHaarMeasure] (a b : ℝ) (ha : 0 < a) :
    Integrable (fun z : Z => Real.exp (b * ‖z‖ - a * ‖z‖ ^ 2)) lam := by
  have hn : ((Module.finrank ℝ Z : ℕ) : ℝ) < ((Module.finrank ℝ Z + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hi := (integrable_one_add_norm (E := Z) (μ := lam) hn).const_mul
    (((Module.finrank ℝ Z + 1).factorial : ℝ) * Real.exp (1 + (1 + b) ^ 2 / (4 * a)))
  refine hi.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_bound a b ha _ _ (norm_nonneg z)

lemma pow_abs_le (x : ℝ) (n : ℕ) : |x| ^ n ≤ (n.factorial : ℝ) * Real.exp |x| := by
  have h1 := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
  rw [div_le_iff₀ (by positivity)] at h1
  linarith

lemma abs_le_op (ℓ : Z →L[ℝ] ℝ) (z : Z) : |ℓ z| ≤ ‖ℓ‖ * ‖z‖ := by
  simpa using ℓ.le_opNorm z

lemma int_mom {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (lam : Measure Z) [lam.IsAddHaarMeasure]
    (f : Z → E) (hf : Continuous f) (K a : ℝ) (ha : 0 < a) (hK : 0 ≤ K)
    (hb : ∀ z, ‖f z‖ ≤ K * Real.exp (-a * ‖z‖ ^ 2)) (ℓ : Z →L[ℝ] ℝ) (n : ℕ) :
    Integrable (fun z => (ℓ z) ^ n • f z) lam := by
  have hi := (integrable_gauss lam a ‖ℓ‖ ha).const_mul (K * (n.factorial : ℝ))
  refine hi.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => ?_)
  rw [norm_smul, norm_pow, Real.norm_eq_abs]
  have h1 : |ℓ z| ^ n ≤ (n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖) :=
    (pow_abs_le _ n).trans (by gcongr; exact abs_le_op ℓ z)
  calc |ℓ z| ^ n * ‖f z‖ ≤ ((n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖)) * (K * Real.exp (-a * ‖z‖ ^ 2)) := by
        gcongr
        exact hb z
    _ = K * (n.factorial : ℝ) * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]; ring

lemma dual_mem {ι : Type} [Fintype ι] (c : ι → Z →L[ℝ] ℂ) (hsep : ∀ z, (∀ k, c k z = 0) → z = 0)
    (A : Subalgebra ℂ (Z → ℂ)) (hc : ∀ k, (fun z => c k z) ∈ A) (hconj : ∀ k, (fun z => conj (c k z)) ∈ A)
    (ℓ : Z →L[ℝ] ℝ) : (fun z => ((ℓ z : ℝ) : ℂ)) ∈ A := by
  classical
  have hre : ∀ k, (fun z => (((c k z).re : ℝ) : ℂ)) ∈ A := by
    intro k
    have : (fun z => (((c k z).re : ℝ) : ℂ)) =
        (1 / 2 : ℂ) • ((fun z => c k z) + fun z => conj (c k z)) := by
      funext z
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.add_conj]
      push_cast; ring
    rw [this]
    exact A.smul_mem (A.add_mem (hc k) (hconj k)) _
  have him : ∀ k, (fun z => (((c k z).im : ℝ) : ℂ)) ∈ A := by
    intro k
    have : (fun z => (((c k z).im : ℝ) : ℂ)) =
        (-Complex.I / 2 : ℂ) • ((fun z => c k z) - fun z => conj (c k z)) := by
      funext z
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.sub_conj]
      push_cast
      have := Complex.I_mul_I
      linear_combination (((c k z).im : ℂ)) * this
    rw [this]
    exact A.smul_mem (A.sub_mem (hc k) (hconj k)) _
  let T : Z →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun k => (c k : Z →ₗ[ℝ] ℂ)
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    exact hsep z fun k => congrFun hz k
  obtain ⟨S, hS⟩ := T.exists_leftInverse_of_injective hT
  let φ : (ι → ℂ) →ₗ[ℝ] ℝ := (ℓ : Z →ₗ[ℝ] ℝ) ∘ₗ S
  have hφ : ∀ z, ℓ z = ∑ k, ((c k z).re * φ (Pi.single k 1) + (c k z).im * φ (Pi.single k Complex.I)) := by
    intro z
    have h0 : ℓ z = φ (T z) := by
      have : S (T z) = z := LinearMap.congr_fun hS z
      simp [φ, this]
    have h1 : T z = ∑ k, ((c k z).re • (Pi.single k 1 : ι → ℂ) + (c k z).im • (Pi.single k Complex.I : ι → ℂ)) := by
      funext j
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      simp [T, Finset.sum_add_distrib, Complex.re_add_im]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, h1, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have : (fun z => ((ℓ z : ℝ) : ℂ)) = ∑ k, (((φ (Pi.single k 1) : ℝ) : ℂ) • (fun z => (((c k z).re : ℝ) : ℂ)) +
      ((φ (Pi.single k Complex.I) : ℝ) : ℂ) • (fun z => (((c k z).im : ℝ) : ℂ))) := by
    funext z
    rw [hφ z]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this]
  exact A.sum_mem fun k _ => A.add_mem (A.smul_mem (hre k) _) (A.smul_mem (him k) _)

lemma exp_series (x : ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x ^ n / (n.factorial : ℂ)) atTop (𝓝 (Complex.exp x)) := by
  have h : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  exact h.tendsto_sum_nat

lemma char_zero (lam : Measure Z) [lam.IsAddHaarMeasure] (h : Z → ℝ) (hc : Continuous h) (K a : ℝ)
    (ha : 0 < a) (hK : 0 ≤ K) (hb : ∀ z, ‖h z‖ ≤ K * Real.exp (-a * ‖z‖ ^ 2))
    (hm : ∀ (ℓ : Z →L[ℝ] ℝ) (n : ℕ), ∫ z, (ℓ z) ^ n * h z ∂lam = 0) (ℓ : Z →L[ℝ] ℝ) :
    ∫ z, (h z : ℂ) * Complex.exp (ℓ z * Complex.I) ∂lam = 0 := by
  let F : ℕ → Z → ℂ := fun N z =>
    (h z : ℂ) * ∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)
  have hbi : Integrable (fun z => K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2)) lam :=
    (integrable_gauss lam a ‖ℓ‖ ha).const_mul K
  have hbound : ∀ N z, ‖F N z‖ ≤ K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by
    intro N z
    have hs : ‖∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖
        ≤ Real.exp (‖ℓ‖ * ‖z‖) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Finset.range N, ‖((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖
          = |ℓ z| ^ n / (n.factorial : ℝ) := by
        intro n _
        simp [norm_pow, Complex.norm_real]
      rw [Finset.sum_congr rfl this]
      refine (Real.sum_le_exp_of_nonneg (abs_nonneg _) N).trans ?_
      gcongr
      exact abs_le_op ℓ z
    have hh : ‖(h z : ℂ)‖ = ‖h z‖ := by simp
    calc ‖F N z‖ = ‖h z‖ * ‖∑ n ∈ Finset.range N, ((ℓ z : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖ := by
          simp only [F, norm_mul, hh]
      _ ≤ (K * Real.exp (-a * ‖z‖ ^ 2)) * Real.exp (‖ℓ‖ * ‖z‖) := by
          gcongr
          exact hb z
      _ = K * Real.exp (‖ℓ‖ * ‖z‖ - a * ‖z‖ ^ 2) := by
          rw [sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]; ring
  have hzero : ∀ N, ∫ z, F N z ∂lam = 0 := by
    intro N
    have hF : F N = fun z => ∑ n ∈ Finset.range N,
        (Complex.I ^ n / (n.factorial : ℂ)) * (((ℓ z) ^ n * h z : ℝ) : ℂ) := by
      funext z
      simp only [F, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      rw [mul_pow]
      ring
    rw [hF, integral_finsetSum]
    · refine Finset.sum_eq_zero fun n _ => ?_
      rw [integral_const_mul, integral_complex_ofReal, hm ℓ n]
      simp
    · intro n _
      have := int_mom lam h hc K a ha hK hb ℓ n
      simp only [smul_eq_mul] at this
      exact this.ofReal.const_mul _
  have hlim := tendsto_integral_of_dominated_convergence (μ := lam) (F := F)
    (f := fun z => (h z : ℂ) * Complex.exp (ℓ z * Complex.I)) _
    (fun N => Continuous.aestronglyMeasurable (by simp only [F]; fun_prop)) hbi
    (fun N => Eventually.of_forall (hbound N))
    (Eventually.of_forall fun z => (exp_series _).const_mul _)
  simp only [hzero] at hlim
  exact (tendsto_nhds_unique hlim tendsto_const_nhds)

lemma real_zero (lam : Measure Z) [lam.IsAddHaarMeasure] (h : Z → ℝ) (hc : Continuous h) (K a : ℝ)
    (ha : 0 < a) (hK : 0 ≤ K) (hb : ∀ z, ‖h z‖ ≤ K * Real.exp (-a * ‖z‖ ^ 2))
    (hm : ∀ (ℓ : Z →L[ℝ] ℝ) (n : ℕ), ∫ z, (ℓ z) ^ n * h z ∂lam = 0) (z : Z) : h z = 0 := by
  haveI : ProperSpace Z := FiniteDimensional.proper ℝ Z
  have hi : Integrable h lam := by
    have := int_mom lam h hc K a ha hK hb 0 0
    simpa using this
  let fp : Z → ℝ≥0 := fun z => Real.toNNReal (h z)
  let fm : Z → ℝ≥0 := fun z => Real.toNNReal (-h z)
  have cfp : Continuous fp := continuous_real_toNNReal.comp hc
  have cfm : Continuous fm := continuous_real_toNNReal.comp hc.neg
  haveI : IsFiniteMeasure (lam.withDensity fun z => (fp z : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  haveI : IsFiniteMeasure (lam.withDensity fun z => (fm z : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hi.neg.2
  have key : ∀ (f : Z → ℝ≥0), Continuous f → (∀ z, (f z : ℝ) ≤ ‖h z‖) → ∀ ℓ : Z →L[ℝ] ℝ,
      Integrable (fun z => f z • Complex.exp (ℓ z * Complex.I)) lam := by
    intro f cf hf ℓ
    refine hi.norm.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun z => ?_)
    · have : (fun z => f z • Complex.exp (ℓ z * Complex.I)) =
          fun z => ((f z : ℝ) : ℂ) * Complex.exp (ℓ z * Complex.I) := by
        funext z
        rw [NNReal.smul_def, Complex.real_smul]
      rw [this]
      have cf' : Continuous fun z => (f z : ℝ) := NNReal.continuous_coe.comp cf
      fun_prop
    · rw [NNReal.smul_def, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simpa using hf z
  have hchar : charFunDual (lam.withDensity fun z => (fp z : ℝ≥0∞)) =
      charFunDual (lam.withDensity fun z => (fm z : ℝ≥0∞)) := by
    funext ℓ
    rw [charFunDual_apply, charFunDual_apply,
      integral_withDensity_eq_integral_smul cfp.measurable,
      integral_withDensity_eq_integral_smul cfm.measurable, ← sub_eq_zero,
      ← integral_sub (key fp cfp (fun z => ?_) ℓ) (key fm cfm (fun z => ?_) ℓ)]
    · rw [← char_zero lam h hc K a ha hK hb hm ℓ]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [fp, fm, NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal']
      rw [← sub_mul, ← Complex.ofReal_sub, max_zero_sub_eq_self]
    · simp only [fp, Real.coe_toNNReal', Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · simp only [fm, Real.coe_toNNReal', Real.norm_eq_abs]
      exact max_le (neg_le_abs _) (abs_nonneg _)
  have heq := Measure.ext_of_charFunDual hchar
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (ENNReal.continuous_coe.comp cfp).measurable.aemeasurable
    (ENNReal.continuous_coe.comp cfm).measurable.aemeasurable).1 heq
  have hall := (Continuous.ae_eq_iff_eq lam (ENNReal.continuous_coe.comp cfp)
    (ENNReal.continuous_coe.comp cfm)).1 hae
  have h1 : fp z = fm z := ENNReal.coe_injective (congrFun hall z)
  have h2 : ((fp z : ℝ≥0) : ℝ) = fm z := congrArg _ h1
  simp only [fp, fm, Real.coe_toNNReal'] at h2
  have := max_zero_sub_eq_self (h z)
  linarith

theorem eucTotal : EucTotal := by
  intro Z _ _ _ _ _ lam _ ι _ c hsep A hc hconj g gc gpos C a ha hg w wc hw hint
  obtain ⟨B, hB⟩ := hw
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := by
    have h0 := (gpos 0).trans_le (hg 0)
    exact ((mul_pos_iff_of_pos_right (Real.exp_pos _)).1 h0).le
  have hK : 0 ≤ B * C := mul_nonneg hB0 hC0
  have hmom : ∀ (ℓ : Z →L[ℝ] ℝ) (n : ℕ), ∫ z, (ℓ z) ^ n • (w z * (g z : ℂ)) ∂lam = 0 := by
    intro ℓ n
    have hP := hint _ (pow_mem (dual_mem c hsep A hc hconj ℓ) n)
    rw [← hP]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.pow_apply, Complex.real_smul]
    push_cast
    ring
  have hF : Continuous fun z => w z * (g z : ℂ) := by fun_prop
  have hFb : ∀ z, ‖w z * (g z : ℂ)‖ ≤ B * C * Real.exp (-a * ‖z‖ ^ 2) := by
    intro z
    have hgz : ‖(g z : ℂ)‖ = g z := by simp [abs_of_pos (gpos z)]
    rw [norm_mul, hgz, mul_assoc]
    exact mul_le_mul (hB z) (hg z) (gpos z).le hB0
  have hre : ∀ z, (w z * (g z : ℂ)).re = 0 := by
    refine real_zero lam (fun z => (w z * (g z : ℂ)).re) (by fun_prop) (B * C) a ha hK
      (fun z => (show ‖(w z * (g z : ℂ)).re‖ ≤ ‖w z * (g z : ℂ)‖ by
        rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _).trans (hFb z)) ?_
    intro ℓ n
    have := Complex.reCLM.integral_comp_comm (int_mom lam _ hF (B * C) a ha hK hFb ℓ n)
    rw [hmom ℓ n] at this
    simpa only [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul, Complex.zero_re] using this
  have him : ∀ z, (w z * (g z : ℂ)).im = 0 := by
    refine real_zero lam (fun z => (w z * (g z : ℂ)).im) (by fun_prop) (B * C) a ha hK
      (fun z => (show ‖(w z * (g z : ℂ)).im‖ ≤ ‖w z * (g z : ℂ)‖ by
        rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _).trans (hFb z)) ?_
    intro ℓ n
    have := Complex.imCLM.integral_comp_comm (int_mom lam _ hF (B * C) a ha hK hFb ℓ n)
    rw [hmom ℓ n] at this
    simpa only [Complex.imCLM_apply, Complex.smul_im, smul_eq_mul, Complex.zero_im] using this
  funext z
  have hz : w z * (g z : ℂ) = 0 := Complex.ext (hre z) (him z)
  have hgz : (g z : ℂ) ≠ 0 := by exact_mod_cast (gpos z).ne'
  exact (mul_eq_zero.1 hz).resolve_right hgz

end GlobalTheory.CompanionTheory.ThTot.EucT

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotalStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euclidean_total : EucTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | exact GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7}

def subH {k m : ℕ} (b : HermE D m) (e : Fin k → Fin m) : HermE D k :=
  ⟨b.1.submatrix e e, by
    have h := b.2
    funext i j
    exact congrFun (congrFun h (e i)) (e j)⟩

theorem subH_isDiagInv {k m : ℕ} {b : HermE D m} (hb : IsDiagInv b) {e : Fin k → Fin m} (he : Function.Injective e) :
    IsDiagInv (subH b e) := by
  obtain ⟨h1, h2⟩ := hb
  have hd : ∀ i, b.1 i i ≠ 0 := by
    intro i h0
    apply h2
    rw [← h1.diagonal_diag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hs : (subH b e).1.IsDiag := h1.submatrix he
  refine ⟨hs, ?_⟩
  rw [← hs.diagonal_diag, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hd (e i)

theorem diagonal_invertible_block_form {ρ : ℕ} {b : HermE D (ρ + 1)} (hb : IsDiagInv b) :
    IsBlockSL2Embedding b (subH b (Fin.castAdd 1)) (subH b (Fin.natAdd ρ)) := by
  have hne : ∀ (i : Fin ρ) (j : Fin 1), Fin.castAdd 1 i ≠ Fin.natAdd ρ j := by
    intro i j h
    have := congrArg Fin.val h
    simp at this
    omega
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun i j => hb.1 (hne i j), fun i j => hb.1 (hne i j).symm⟩

theorem core (h0 : ZeroTotal) (h1 : OneTotal) (hS : StepTotal) (hH : HeckeEta) (D : D7) :
    ∀ (ρ p : ℕ) (μ : Measure (Mx D ρ p)) (𝓕 : Set (Mx D ρ p)), IsCovolOne (ratMx D ρ p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, IsDiagInv b₀ → ∀ χ, IsHeckeChar D χ → ResEta D χ ρ → (ρ = 0 → χ = 1) →
    ∀ θ, IsInfFam θ → Total ψ χ θ b₀ μ := by
  intro ρ
  induction ρ with
  | zero =>
    intro p μ 𝓕 hμ ψ hψ b₀ _ χ _ _ h1' θ hθ
    obtain rfl := h1' rfl
    exact h0 D p μ 𝓕 hμ ψ hψ b₀ θ hθ
  | succ ρ ih =>
    intro p μ 𝓕 hμ ψ hψ b₀ hb χ hχ hr _ θ hθ
    obtain ⟨χ₁, hχ₁, hr₁, he⟩ : ∃ χ₁, IsHeckeChar D χ₁ ∧ ResEta D χ₁ 1 ∧ (ρ = 0 → χ₁ = χ) := by
      by_cases h : ρ = 0
      · subst h
        exact ⟨χ, hχ, hr, fun _ => rfl⟩
      · obtain ⟨χ₁, a, b⟩ := hH D 1
        exact ⟨χ₁, a, b, fun h' => absurd h' h⟩
    have hχ' : IsHeckeChar D (χ * χ₁⁻¹) := by
      refine ⟨?_, fun x => ?_⟩
      · have c1 := hχ.1
        have c2 := hχ₁.1
        exact c1.mul c2.inv
      · have a1 := hχ.2 x
        have a2 := hχ₁.2 x
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, a1, a2, inv_one, mul_one]
    have hr' : ResEta D (χ * χ₁⁻¹) ρ := by
      refine ⟨hr.1, fun η hη a => ?_⟩
      have e1 := hr.2 η hη a
      have e2 := hr₁.2 η hη a
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1, e2, pow_one, pow_succ]
      exact mul_inv_cancel_right _ _
    obtain ⟨μr, 𝓕r, hμr⟩ := GlobalTheory.CompanionTheory.RatMxCovol.exists_isCovolOne_ratMx D ρ p
    obtain ⟨μs, 𝓕s, hμs⟩ := GlobalTheory.CompanionTheory.RatMxCovol.exists_isCovolOne_ratMx D 1 p
    have hinj1 : Function.Injective (Fin.castAdd 1 : Fin ρ → Fin (ρ + 1)) := Fin.castAdd_injective _ _
    have hinj2 : Function.Injective (Fin.natAdd ρ : Fin 1 → Fin (ρ + 1)) := Fin.natAdd_injective _ _
    have hd2 := subH_isDiagInv hb hinj2
    have T := hS D ρ 1 p μr 𝓕r μs 𝓕s μ 𝓕 hμr hμs hμ ψ hψ (χ * χ₁⁻¹) χ₁ θ hθ _ _ b₀ (diagonal_invertible_block_form hb)
      (ih p μr 𝓕r hμr ψ hψ _ (subH_isDiagInv hb hinj1) _ hχ' hr'
        (fun h => by rw [he h]; exact mul_inv_cancel χ) θ hθ)
      (h1 D p μs 𝓕s hμs ψ hψ _ hd2.2 χ₁ hχ₁ hr₁ θ hθ)
    rwa [inv_mul_cancel_right] at T

theorem thTotal_of (h0 : ZeroTotal) (h1 : OneTotal) (hS : StepTotal) : HeckeEta → ThTotal := by
  intro hH D ρ p m ψ hψ b₀ hb χ hχ hr h0' θ hθ
  exact core h0 h1 hS hH D ρ p m.μ m.𝓕 m.hμ ψ hψ b₀ hb χ hχ hr h0' θ hθ

theorem thTotal : HeckeEta → ThTotal :=
  thTotal_of GlobalTheory.T.zero_coefficient_total
    (GlobalTheory.T.rank_one_theta_total GlobalTheory.T.weil_representation_continuity (GlobalTheory.T.rank_one_majorant GlobalTheory.T.weil_representation_continuity GlobalTheory.T.weil_representation_K_finite GlobalTheory.T.orbit_majorant GlobalTheory.T.iwasawa_compactness)
      (GlobalTheory.T.fock_total_of_euclidean GlobalTheory.T.euclidean_total))
    (GlobalTheory.T.step_total_of_products (GlobalTheory.T.product_theta_of_schwartz_tensor GlobalTheory.T.schwartz_tensor_density) GlobalTheory.T.product_measure_statement)

end GlobalTheory.CompanionTheory.ThTot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEtaStatement
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_total_of_hecke_eta : HeckeEta → ThTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.thTotal | exact GlobalTheory.CompanionTheory.ThTot.thTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.thTotal <;> assumption)
end
