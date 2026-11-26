module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.OrbRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.ExistsOrthogonalFamily

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInvT
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem fibTrans {D : D7} (X : HidaSetting D) (μinf : Measure (TupI X)) (νinf : Measure (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)))
    (fibInf : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) → Measure (TupI X))
    (hfib : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fibInf)
    (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (hS : μinf.map (fun y => g • y) = μinf) :
    IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ
      (fun b => (fibInf b).map (fun y => g • y)) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hm : Measurable (fun y : TupI X => g • y) := measurable_smul_tupI X g
  have hinv : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), (fun y : TupI X => g • y) ⁻¹' ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X) =
      (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X := by
    intro b; ext y
    simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, gramR_smulI, indI_smul_iff]
  have hmeasA : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), MeasurableSet ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X) := fun b =>
    (isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurableSet.inter
      (isOpen_IndI X).measurableSet
  have hU' : (fun y : TupI X => g • y) ⁻¹' IndI X = IndI X := by
    ext y; exact indI_smul_iff X g y
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs hU => ?_⟩
  · rw [Measure.map_apply hm (hmeasA b).compl, preimage_compl, hinv b]
    exact hfib.1 b
  · calc ∫⁻ v in IndI X, φ v ∂μinf = ∫⁻ v in IndI X, φ v ∂(μinf.map (fun y => g • y)) := by rw [hS]
      _ = ∫⁻ v in IndI X, φ (g • v) ∂μinf := by
          rw [setLIntegral_map (isOpen_IndI X).measurableSet hφ hm, hU']
      _ = ∫⁻ b, ∫⁻ v, φ (g • v) ∂(fibInf b) ∂νinf := hfib.2.1 _ (hφ.comp hm)
      _ = ∫⁻ b, ∫⁻ v, φ v ∂((fibInf b).map (fun y => g • y)) ∂νinf := by
          congr 1; funext b; rw [lintegral_map hφ hm]
  · have hc' : Continuous (fun v => φ (g • v)) := hc.comp (continuous_smul_tupI X g)
    have hs' : HasCompactSupport (fun v => φ (g • v)) := hs.comp_homeomorph (smulH X g)
    have hU2 : tsupport (fun v => φ (g • v)) ⊆ IndI X := by
      rw [show (fun v => φ (g • v)) = φ ∘ smulH X g from rfl, tsupport_comp_eq_preimage]
      intro y hy
      exact (indI_smul_iff X g y).1 (hU hy)
    obtain ⟨hI, hC⟩ := hfib.2.2 _ hc' hs' hU2
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
      exact hI b hb
    · have e : (fun b => ∫ v, φ v ∂((fibInf b).map (fun y => g • y))) =
          fun b => ∫ v, φ (g • v) ∂(fibInf b) := by
        funext b; rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
      rw [e]
      exact hC

theorem fibEqI {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (μinf : Measure (TupI X))
    (νinf : Measure (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS))) (fib1 fib2 : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) → Measure (TupI X))
    (hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) μinf)
    (hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) νinf)
    (h1 : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fib1)
    (h2 : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fib2) : fib1 = fib2 := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI := hμ.1
  haveI := hν.1
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))
  haveI : LocallyCompactSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :=
    (isClosed_HermRP (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact FU.fib_eq h1 h2 (continuous_gramHI X) (fun _ => rfl) Subtype.val_injective (isOpen_IndI X)

theorem invFib_of (hS : SdInvG) : InvFib := by
  intro D X u' ψ hT μinf νinf fibInf hP g
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (hS X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h (TI X u' hT)

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperOne
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperL
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem pushLFin_of_proper (h : ProperOrb) : PushLFin := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK hKI
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  obtain ⟨N, hN, C, hC, hNC⟩ := h X u' ψ hT μinf νinf fibInf hH K hK hKI
  rw [Measure.map_apply (measurable_orbM X u') hK.isClosed.measurableSet]
  refine lt_of_le_of_lt (measure_mono fun g hg => hNC 1 (mem_of_mem_nhds hN) g ?_) hC.measure_lt_top
  rw [rmulT_one]; exact hg

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ProperOne : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K →
      ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • Y0 X u' ∈ K → g ∈ C

def InvNbhd : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ N ∈ 𝓝 (1 : MfI X), ∃ Nc : Set (MfI X), IsCompact Nc ∧ ∀ b ∈ N, ∃ c ∈ Nc, c * b = 1

theorem continuous_right_mul_tuple {D : D7} (X : HidaSetting D) :
    Continuous (fun p : MfI X × TupI X => rmulT X p.1 p.2) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply_apply c a).comp continuous_fst).mul ((continuous_apply_apply c i).comp continuous_snd)

theorem properOrb_of_one (h1 : ProperOne) (hI : InvNbhd) : ProperOrb := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK _
  obtain ⟨N, hN, Nc, hNc, hNi⟩ := hI X
  have hK' : IsCompact ((fun p : MfI X × TupI X => rmulT X p.1 p.2) '' (Nc ×ˢ K)) :=
    (hNc.prod hK).image (continuous_right_mul_tuple X)
  obtain ⟨C, hC, hgC⟩ := h1 X u' ψ hT μinf νinf fibInf hH _ hK'
  refine ⟨N, hN, C, hC, fun b hb g hg => hgC g ?_⟩
  obtain ⟨c, hc, hcb⟩ := hNi b hb
  have hbc : b * c = 1 := mul_eq_one_comm.1 hcb
  refine ⟨(c, g • rmulT X b (Y0 X u')), ⟨hc, hg⟩, ?_⟩
  show rmulT X c (g • rmulT X b (Y0 X u')) = g • Y0 X u'
  rw [smul_rmulT, rmulT_rmulT, hbc, rmulT_one]

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfAction
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ActMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (Z : TupI X),
    Measurable (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Z)

def FibOrbAt : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∀ T ∈ Ω₁, ∃ k : ENNReal,
      fibInf T = k • X.measG.μGinf.map (fun g => g • rmulT X (a T) (Y0 X u'))

def OrbCont : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∃ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) ∧
      PolId X u' μinf νinf a Ω₁ c

def JacOneC : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem isOpen_ne_zero_top : IsOpen (({0}ᶜ ∩ {⊤}ᶜ : Set ENNReal)) :=
  isOpen_compl_singleton.inter isOpen_compl_singleton

theorem polar_local_of_orbit (hK : KPos) (h2 : OrbCont) (h4 : JacOneC) : PolarLoc := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC⟩ := sqChart_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, c, hcc, hc⟩ := h2 X u' ψ hT μinf νinf fibInf hP Ω a hC
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  have hc0 : c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹ :=
    h4 X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₁ hΩ₁ hΩ₁n c hcc hc
  have hne0 : c (TI X u' hT) ≠ 0 := by rw [hc0]; exact ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hneT : c (TI X u' hT) ≠ ⊤ := by rw [hc0]; exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne'
  have hN : c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hcc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hne0, Set.mem_compl_singleton_iff.2 hneT⟩)
  refine ⟨Ω₁ ∩ c ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), a, fun T => ((c T)⁻¹).toReal, inter_mem hΩ₁n hN, hC.2.1, hC.2.2.1,
    ?_, ?_, ?_⟩
  · show ((c (TI X u' hT))⁻¹).toReal = KVal X u'
    rw [hc0, inv_inv, ENNReal.toReal_ofReal hK0.le]
  · have ht : (c (TI X u' hT))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne0
    have hinv : ContinuousAt (fun T => (c T)⁻¹) (TI X u' hT) := tendsto_inv_iff.2 hcc
    exact ContinuousAt.comp (g := ENNReal.toReal) (f := fun T => (c T)⁻¹) (ENNReal.continuousAt_toReal ht) hinv
  · intro φ hφ S hS hSm
    rw [hc φ hφ S (hS.trans Set.inter_subset_left) hSm]
    refine setLIntegral_congr_fun hSm ?_
    intro T hTS
    have hT2 := (hS hTS).2
    have h0 : c T ≠ 0 := Set.mem_compl_singleton_iff.1 hT2.1
    show c T * _ = (ENNReal.ofReal ((c T)⁻¹).toReal)⁻¹ * _
    rw [ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 h0), inv_inv]

theorem orbCont_of (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) : OrbCont := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, hk⟩ := h1 X u' ψ hT μinf νinf fibInf hP Ω a hC
  obtain ⟨φ, hφc, hφm, hφs, hφU, hφ0, hIpos, hIfin, hIc⟩ := h2 X u' ψ hT μinf νinf fibInf hP a hC.2.1 hC.2.2.1
  have hfib := hP.2.2.2.2.2.2
  have hΦm : Measurable fun y => ENNReal.ofReal (φ y) := ENNReal.measurable_ofReal.comp hφm
  set I : HmI X → ENNReal := fun T =>
    ∫⁻ g, ENNReal.ofReal (φ (g • rmulT X (a T) (Y0 X u'))) ∂X.measG.μGinf with hIdef
  set Nf : HmI X → ENNReal := fun T => ∫⁻ y, ENNReal.ofReal (φ y) ∂(fibInf T) with hNdef
  have hI1 : I (TI X u' hT) = ∫⁻ g, ENNReal.ofReal (φ (g • Y0 X u')) ∂X.measG.μGinf := by
    simp only [hIdef]; rw [hC.2.1, rmulT_one]
  have hI0 : I (TI X u' hT) ≠ 0 := by rw [hI1]; exact hIpos.ne'
  have hIT : I (TI X u' hT) ≠ ⊤ := by rw [hI1]; exact hIfin.ne
  have hIN : I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ) ∈ 𝓝 (TI X u' hT) :=
    hIc (isOpen_ne_zero_top.mem_nhds ⟨Set.mem_compl_singleton_iff.2 hI0, Set.mem_compl_singleton_iff.2 hIT⟩)

  have c3 := hfib.2.2 φ hφc hφs hφU
  have hNeq : Nf = fun T => ENNReal.ofReal (∫ v, φ v ∂(fibInf T)) := by
    funext T
    exact (ofReal_integral_eq_lintegral_ofReal (c3.1 T (Set.mem_univ _))
      (Eventually.of_forall fun y => hφ0 y)).symm
  have hNc : ContinuousAt Nf (TI X u' hT) := by
    rw [hNeq]
    exact (ENNReal.continuous_ofReal.comp (continuousOn_univ.1 c3.2)).continuousAt
  refine ⟨Ω₁ ∩ I ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ), Set.inter_subset_left.trans hΩ₁, inter_mem hΩ₁n hIN,
    fun T => Nf T / I T, ENNReal.Tendsto.div hNc (Or.inr hI0) hIc (Or.inl hIT), ?_⟩
  intro φ' hφ' S hS hSm
  have hGS := hG X S hSm
  have c2 := hfib.2.1 ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ')
    (hφ'.indicator hGS)
  rw [lintegral_indicator hGS, Measure.restrict_restrict hGS] at c2
  rw [c2]
  have inner : ∀ b, ∫⁻ v, (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S)).indicator φ' v
      ∂(fibInf b) = S.indicator (fun T => ∫⁻ v, φ' v ∂(fibInf T)) b := by
    intro b
    have hae : ∀ᵐ y ∂(fibInf b), y ∈ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {Subtype.val b} ∩ IndI X :=
      ae_iff.2 (hfib.1 b)
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
      exact Set.indicator_of_mem (Set.mem_preimage.2 (show gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y ∈
        Subtype.val '' S from ⟨b, hb, hy1.symm⟩)) _
    · rw [Set.indicator_of_notMem hb]
      calc _ = ∫⁻ _, (0 : ENNReal) ∂(fibInf b) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with y hy
              have hy1 := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
              refine Set.indicator_of_notMem ?_ _
              rintro ⟨c, hc, hcy⟩
              have hcb : c = b := Subtype.val_injective (hcy.trans hy1)
              exact hb (hcb ▸ hc)
        _ = 0 := lintegral_zero
  simp_rw [inner]
  rw [lintegral_indicator hSm]
  refine setLIntegral_congr_fun hSm ?_
  intro T hTS
  obtain ⟨k, hkT⟩ := hk T (hS hTS).1
  have hIT2 := (hS hTS).2
  have h0 : I T ≠ 0 := Set.mem_compl_singleton_iff.1 hIT2.1
  have hTop : I T ≠ ⊤ := Set.mem_compl_singleton_iff.1 hIT2.2
  have hm := hA X (rmulT X (a T) (Y0 X u'))
  have e1 : ∀ ψ' : TupI X → ENNReal, Measurable ψ' →
      ∫⁻ v, ψ' v ∂(fibInf T) = k * ∫⁻ g, ψ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf := by
    intro ψ' hψ'
    rw [hkT, lintegral_smul_measure, lintegral_map hψ' hm, smul_eq_mul]
  have hNk : Nf T = k * I T := e1 _ hΦm
  show ∫⁻ v, φ' v ∂(fibInf T) = Nf T / I T * ∫⁻ g, φ' (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf
  rw [hNk, ENNReal.mul_div_cancel_right h0 hTop, e1 φ' hφ']

theorem polar_local_of_action (hK : KPos) (hG : GramMeas) (hA : ActMeas) (h1 : FibOrbAt) (h2 : PushCont) (h4 : JacOneC) :
    PolarLoc :=
  polar_local_of_orbit hK (orbCont_of hG hA h1 h2) h4

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds
noncomputable section

namespace PI.AprimeInfWitt

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabSW.OrbR
open scoped TensorProduct

theorem witt_R {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h2 : Module.finrank F E = 2) (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range)
    (hinv : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) {a : ℕ}
    (X0 : Fin a → Fin M → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (hdet : (gramE σ J X0).det ≠ 0) (R : Type) [CommRing R] [Algebra F R]
    (hU : PIW.AdelicOrbitU.UnitChoice R) (y : Fin a → Fin M → R ⊗[F] E)
    (hy : gramR R σ J y = (gramE σ J X0).map (inclR R)) :
    ∃ g : HA R σ J, g • ratTup (F := F) R X0 = y := by
  set T := gramE σ J X0 with hTdef
  let sE : E →+* E := σ
  have hTH : IsHerm sE T := by
    ext i j; exact hT i j
  have hh : PI.UnitaryGroupMassFormula.HermConj.IsHermForm sE (hform sE T) :=
    { add := fun x y z => by
        rw [PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot,
          PIW.AdelicOrbitU.hform_eq_dot, mulVec_add, dotProduct_add]
      smul := fun x c y => PIW.AdelicOrbitU.hform_smul_right sE T c x y
      herm := fun x y => (PIW.AdelicOrbitU.hform_conj sE T hinv hTH x y).symm }
  obtain ⟨v, hvli, hvo⟩ := PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family sE a (Fin a → E)
    (by simp) (hform sE T) hh
  set P : Matrix (Fin a) (Fin a) E := tM v with hP
  have hPu : IsUnit P.det := by
    have h1 : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.mp hvli
    have h2 : P = (Matrix.of v)ᵀ := rfl
    rw [h2, det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h1
  set D := cT sE P * T * P with hD
  have hDv : ∀ j k, hform sE T (v j) (v k) = D j k := fun j k => gram_tM sE T v j k
  have hDoff : ∀ j k, j ≠ k → D j k = 0 := fun j k hjk => by rw [← hDv]; exact hvo j k hjk
  have hDdiag : D = Matrix.diagonal fun j => D j j := by
    ext j k
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [hDoff j k hjk, Matrix.diagonal_apply_ne _ hjk]
  have hDdet : D.det ≠ 0 := by
    have hc : (cT sE P).det = sE P.det := by
      rw [cT, det_transpose, RingHom.map_det]; rfl
    rw [hD, det_mul, det_mul, hc]
    refine mul_ne_zero (mul_ne_zero ?_ hdet) hPu.ne_zero
    exact (map_ne_zero sE).mpr hPu.ne_zero
  have hDne : ∀ j, D j j ≠ 0 := by
    intro j
    rw [hDdiag, det_diagonal] at hDdet
    exact Finset.prod_ne_zero_iff.mp hDdet j (Finset.mem_univ j)
  have hDfix : ∀ j, σ (D j j) = D j j := fun j => by
    rw [← hDv]; exact PIW.AdelicOrbitU.hform_conj sE T hinv hTH _ _

  let sS := sigR R σ
  let JS := JR (F := F) R J
  have hsS : ∀ z, sS (sS z) = z := (PIW.AdelicOrbitU.stFix F E σ h2 hfix R).1
  have hJS : IsHerm sS JS := PIW.AdelicOrbitU.isHerm_JR R σ J hJ.1
  have hJSd : IsUnit JS.det := PIW.AdelicOrbitU.isUnit_det_JR (F := F) R J hJ.2
  have hcTmap : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) E),
      cT sS (N.map (inclR (F := F) R)) = (cT sE N).map (inclR (F := F) R) := by
    intro p q N; ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
    exact PIW.AdelicOrbitU.sigR_inclR (F := F) R σ _
  set Xm : Matrix (Fin M) (Fin a) (R ⊗[F] E) := (tM X0).map (inclR (F := F) R) with hXm
  set Pm : Matrix (Fin a) (Fin a) (R ⊗[F] E) := P.map (inclR (F := F) R) with hPm
  have hTg : cT sE (tM X0) * J * tM X0 = T := by
    ext i j; rw [← gram_tM]; rfl
  have hyg : cT sS (tM y) * JS * tM y = T.map (inclR (F := F) R) := by
    ext i j; rw [← gram_tM]; exact congrFun (congrFun hy i) j
  let x' : Fin a → Fin M → R ⊗[F] E := fun j r => (Xm * Pm) r j
  let y' : Fin a → Fin M → R ⊗[F] E := fun j r => (tM y * Pm) r j
  have hGx : ∀ j k, hform sS JS (x' j) (x' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM x' = Xm * Pm := rfl
    rw [e, gram_mul, hXm, hPm, hcTmap, hcTmap]
    show ((cT sE P).map (inclR (F := F) R) * ((cT sE (tM X0)).map (inclR (F := F) R) * J.map (inclR (F := F) R) *
      (tM X0).map (inclR (F := F) R)) * P.map (inclR (F := F) R)) j k = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hTg]
    rfl
  have hGy : ∀ j k, hform sS JS (y' j) (y' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM y' = tM y * Pm := rfl
    rw [e, gram_mul, hyg, hPm, hcTmap, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  obtain ⟨g, hgU, hgx⟩ := orb_orth sS JS hsS hJS hJSd a x' y'
    (fun j k hjk => by rw [hGx, hDoff j k hjk, map_zero])
    (fun j k => by rw [hGx, hGy])
    (fun j => by rw [hGx]; exact (isUnit_iff_ne_zero.mpr (hDne j)).map _)
    (fun j t => by
      obtain ⟨β, hβ⟩ := (hfix _).mp (hDfix j)
      have hβ0 : β ≠ 0 := by
        rintro rfl; exact hDne j (by rw [← hβ, map_zero])
      obtain ⟨lam, hlam, hu⟩ := PIW.AdelicOrbitU.stLam F E σ h2 hfix R hU t β hβ0
      refine ⟨lam, hlam, ?_⟩
      rw [hGx, ← hβ, PIW.AdelicOrbitU.inclR_algebraMap]
      exact hu)
  have hmat : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm * Pm = tM y * Pm := by
    ext r j
    rw [Matrix.mul_assoc]
    have := congrFun (hgx j) r
    simpa [x', y', Matrix.mul_apply, mulVec, dotProduct] using this
  have hPmu : IsUnit Pm.det := by
    show IsUnit ((inclR (F := F) R).mapMatrix P).det
    rw [← RingHom.map_det]; exact hPu.map _
  have hmat2 : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm = tM y := by
    have := congrArg (fun N => N * Pm⁻¹) hmat
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hPmu] using this
  refine ⟨(⟨g, hgU⟩ : HR R σ J), ?_⟩
  funext i
  funext r
  show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (F := F) R X0 i) r = y i r
  have := congrFun (congrFun hmat2 r) i
  simpa [Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct] using this

end PI.AprimeInfWitt

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittInf_holds : WittInf := by
  intro D X u' ψ hT μinf νinf fibInf hP y hy
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ a : X.B.I.E, X.B.I.cm.sig a = a ↔ a ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun a => X.B.I.cm.fixed a
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hU : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  have hyG : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hU y hyG
  exact ⟨g, hg⟩

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacGlue
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ImgLim
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter

theorem img_ratio {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {f' : E → (E →L[ℝ] E)} {U : Set E} {x₀ : E}
    (hf' : ∀ x ∈ U, HasFDerivWithinAt f (f' x) U x) (hinj : Set.InjOn f U)
    (hc : ContinuousAt (fun x => |(f' x).det|) x₀)
    (A : ℕ → Set E) (hAm : ∀ n, MeasurableSet (A n)) (hAU : ∀ n, A n ⊆ U) (hA0 : ∀ n, 0 < μ (A n))
    (hAt : ∀ n, μ (A n) < ⊤) (hsh : ∀ V ∈ 𝓝 x₀, ∀ᶠ n in atTop, A n ⊆ V) :
    Tendsto (fun n => (μ (f '' A n)).toReal / (μ (A n)).toReal) atTop (𝓝 |(f' x₀).det|) := by
  have key : ∀ n, μ (f '' A n) = ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ := fun n =>
    (lintegral_abs_det_fderiv_eq_addHaar_image μ (hAm n)
      (fun x hx => (hf' x (hAU n hx)).mono (hAU n)) (hinj.mono (hAU n))).symm
  rw [Metric.tendsto_nhds]
  intro ε hε
  set d := |(f' x₀).det| with hd
  have hV : (fun x => |(f' x).det|) ⁻¹' Set.Ioo (d - ε / 2) (d + ε / 2) ∈ 𝓝 x₀ :=
    hc (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hsh _ hV] with n hn
  have hm0 := hA0 n
  have hmt := hAt n
  have hmr : 0 < (μ (A n)).toReal := ENNReal.toReal_pos hm0.ne' hmt.ne
  have up : ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ ≤ ENNReal.ofReal (d + ε / 2) * μ (A n) := by
    calc _ ≤ ∫⁻ _ in A n, ENNReal.ofReal (d + ε / 2) ∂μ :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun x hx =>
            ENNReal.ofReal_le_ofReal (hn hx).2.le))
      _ = _ := setLIntegral_const _ _
  have lo : ENNReal.ofReal (d - ε / 2) * μ (A n) ≤ ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ := by
    calc _ = ∫⁻ _ in A n, ENNReal.ofReal (d - ε / 2) ∂μ := (setLIntegral_const _ _).symm
      _ ≤ _ := lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun x hx =>
            ENNReal.ofReal_le_ofReal (hn hx).1.le))
  have hupt : ENNReal.ofReal (d + ε / 2) * μ (A n) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt.ne
  have hIt : ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ ≠ ⊤ := ne_top_of_le_ne_top hupt up
  have u1 : (∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ).toReal ≤ (d + ε / 2) * (μ (A n)).toReal := by
    have := ENNReal.toReal_mono hupt up
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have l1 : (d - ε / 2) * (μ (A n)).toReal ≤ (∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ).toReal := by
    have := ENNReal.toReal_mono hIt lo
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hmr.le) this
  rw [key n, Real.dist_eq, abs_sub_lt_iff]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hmr]; nlinarith
  · rw [sub_lt_comm, lt_div_iff₀ hmr]; nlinarith

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def gVal {D : D7} (X : HidaSetting D) : ℝ :=
  Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F)

def tVal {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : ℝ :=
  Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F))

def GrpLim {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  (∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → MeasurableSet (TubeG X u' (κ '' ball 0 ρ)) ∧
      0 < X.measG.μGinf (TubeG X u' (κ '' ball 0 ρ)) ∧ X.measG.μGinf (TubeG X u' (κ '' ball 0 ρ)) < ⊤) ∧
  ∀ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) → Tendsto ρ atTop (𝓝 0) →
    Tendsto (fun n => (X.measG.μGinf (TubeG X u' (κ '' ball 0 (ρ n)))).toReal /
      (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal) atTop (𝓝 (gVal X))

def PsiM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X) {ι η : Type}
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
  eT (κ z.1 • rmulT X (a (eH.symm z.2)) (Y0 X u'))

def TupJac {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (μinf : Measure (TupI X)) (νinf : Measure (HmI X)) (a : HmI X → MfI X) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η) (eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cμ cν : ℝ)
    (Ψ' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)),
    0 < cμ ∧ 0 < cν ∧ μinf.map eT = ENNReal.ofReal cμ • volume ∧ νinf.map eH = ENNReal.ofReal cν • volume ∧
    U ∈ 𝓝 ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) ∧
    (∀ z ∈ U, HasFDerivWithinAt (PsiM X u' a κ eT eH) (Ψ' z) U z) ∧ Set.InjOn (PsiM X u' a κ eT eH) U ∧
    ContinuousAt (fun z => |(Ψ' z).det|) ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) ∧
    (∀ᶠ T in 𝓝 (TI X u' hT), IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X) ∧
    cμ * |(Ψ' ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT))).det| / cν = tVal X u'

def GoodP : ChartPred := fun X u' hT μinf νinf a =>
  ∃ (ι : Type) (_ : Fintype ι) (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
    GrpLim X u' κ ∧ TupJac X u' hT μinf νinf a κ

theorem splitAsym_good : SplitAsymFor GoodP := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  obtain ⟨ι, hι, κ, ⟨⟨ρ0, hρ0, hG0⟩, hGl⟩, η, hη, eT, eH, cμ, cν, Ψ', U, hcμ, hcν, hμ, hν, hU, hΨ', hinj,
    hdet, hev, harith⟩ := hPr
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : BorelSpace (HmI X) := ⟨rfl⟩
  haveI hHaar : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  set T0 := TI X u' hT with hT0
  set z0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η := (0, eH T0) with hz0
  set Ψ := PsiM X u' a κ eT eH with hΨ
  set d := |(Ψ' z0).det| with hd

  have hdet1 : (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∈ 𝓝 z0 := hdet (Iio_mem_nhds (by linarith))
  have hHn : eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X}) ∈ 𝓝 (eH T0) := by
    apply eH.symm.continuous.continuousAt.preimage_mem_nhds
    rw [eH.symm_apply_apply]
    exact inter_mem hΩ₂n hev
  have hS : U ∩ (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∩
      Prod.snd ⁻¹' (eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X})) ∈ 𝓝 z0 :=
    inter_mem (inter_mem hU hdet1) (continuous_snd.continuousAt.preimage_mem_nhds hHn)
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.1 hS
  set m0 := min r ρ0 with hm0
  have hm0p : 0 < m0 := lt_min hr hρ0
  set ρ : ℕ → ℝ := fun n => m0 / ((n : ℝ) + 2) with hρ
  have hρp : ∀ n, 0 < ρ n := fun n => div_pos hm0p (by positivity)
  have hρle : ∀ n, ρ n < m0 := fun n => by
    show m0 / ((n : ℝ) + 2) < m0
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hρr : ∀ n, ρ n < r := fun n => (hρle n).trans_le (min_le_left _ _)
  have hρ0' : ∀ n, ρ n < ρ0 := fun n => (hρle n).trans_le (min_le_right _ _)
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat m0).comp (tendsto_add_atTop_nat 2)
    refine h1.congr fun n => ?_
    simp only [Function.comp, hρ, Nat.cast_add, Nat.cast_ofNat]

  set A : ℕ → Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) := fun n => ball 0 (ρ n) ×ˢ ball (eH T0) (ρ n) with hA
  have hAb : ∀ n, A n = ball z0 (ρ n) := fun n => ball_prod_same _ _ _
  have hAS : ∀ n, A n ⊆ U ∩ (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∩
      Prod.snd ⁻¹' (eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X})) := fun n => by
    rw [hAb n]; exact (ball_subset_ball (hρr n).le).trans hrS
  have hAU : ∀ n, A n ⊆ U := fun n z hz => (hAS n hz).1.1
  have hAm : ∀ n, MeasurableSet (A n) := fun n => by rw [hAb n]; exact measurableSet_ball
  set V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := fun n => κ '' ball 0 (ρ n) with hV
  set W : ℕ → Set (HmI X) := fun n => eH ⁻¹' ball (eH T0) (ρ n) with hW
  have hWp : ∀ n, ∀ T ∈ W n, T ∈ Ω₂ ∧ IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X := by
    intro n T hTW
    have h1 := (hAS n (show ((0 : EuclideanSpace ℝ ι), eH T) ∈ A n from ⟨by exact Set.mem_preimage.mpr (mem_ball_self (hρp n)), hTW⟩)).2
    simpa [eH.symm_apply_apply] using h1
  set_option synthInstance.maxHeartbeats 100000 in
  have hΨc : ∀ n, ContinuousOn Ψ (A n) := fun n z hz =>
    ((hΨ' z (hAU n hz)).mono (hAU n)).continuousWithinAt
  have hΨm : ∀ n, MeasurableSet (Ψ '' A n) := fun n =>
    (hAm n).image_of_continuousOn_injOn (hΨc n) (hinj.mono (hAU n))
  have hBox : ∀ n, BoxT X u' a (V n) (W n) = eT ⁻¹' (Ψ '' A n) := by
    intro n
    ext y
    constructor
    · rintro ⟨T, hTW, g, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(x, eH T), ⟨hx, hTW⟩, ?_⟩
      simp [hΨ, PsiM, eH.symm_apply_apply]
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, hy⟩
      refine ⟨eH.symm t, ?_, κ x, ⟨x, hx, rfl⟩, ?_⟩
      · show eH (eH.symm t) ∈ ball (eH T0) (ρ n)
        rw [eH.apply_symm_apply]; exact ht
      · apply eT.injective
        rw [← hy]
        rfl
  have hvolΨ : ∀ n, volume (Ψ '' A n) = ∫⁻ z in A n, ENNReal.ofReal |(Ψ' z).det| := fun n =>
    (lintegral_abs_det_fderiv_eq_addHaar_image volume (hAm n)
      (fun z hz => (hΨ' z (hAU n hz)).mono (hAU n)) (hinj.mono (hAU n))).symm
  have hvolA : ∀ n, volume (A n) = volume (ball (0 : EuclideanSpace ℝ ι) (ρ n)) * volume (ball (eH T0) (ρ n)) :=
    fun n => by rw [Measure.volume_eq_prod, Measure.prod_prod]
  have hAt : ∀ n, volume (A n) < ⊤ := fun n => by rw [hAb n]; exact measure_ball_lt_top
  have hA0 : ∀ n, 0 < volume (A n) := fun n => by rw [hAb n]; exact measure_ball_pos _ _ (hρp n)
  have hΨt : ∀ n, volume (Ψ '' A n) < ⊤ := by
    intro n
    rw [hvolΨ n]
    calc ∫⁻ z in A n, ENNReal.ofReal |(Ψ' z).det| ≤ ∫⁻ _ in A n, ENNReal.ofReal (d + 1) :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun z hz =>
            ENNReal.ofReal_le_ofReal (le_of_lt (hAS n hz).1.2)))
      _ = ENNReal.ofReal (d + 1) * volume (A n) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hAt n)
  have hμB : ∀ n, μinf (BoxT X u' a (V n) (W n)) = ENNReal.ofReal cμ * volume (Ψ '' A n) := fun n => by
    rw [hBox n, ← Measure.map_apply eT.continuous.measurable (hΨm n), hμ, Measure.smul_apply, smul_eq_mul]
  have hνW : ∀ n, νinf (W n) = ENNReal.ofReal cν * volume (ball (eH T0) (ρ n)) := fun n => by
    rw [hW, ← Measure.map_apply eH.continuous.measurable measurableSet_ball, hν, Measure.smul_apply, smul_eq_mul]
  have hBy0 : ∀ n, 0 < volume (ball (eH T0) (ρ n)) := fun n => measure_ball_pos _ _ (hρp n)
  have hBx0 : ∀ n, 0 < volume (ball (0 : EuclideanSpace ℝ ι) (ρ n)) := fun n => measure_ball_pos _ _ (hρp n)
  refine ⟨V, W, fun n => (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal, fun n => ?_, ?_, ?_, ?_⟩
  · obtain ⟨g1, g2, g3⟩ := hG0 (ρ n) (hρp n) (hρ0' n)
    refine ⟨measurableSet_ball.preimage eH.continuous.measurable, fun T hT' => (hWp n T hT').1, ?_, ?_,
      fun T hT' => (hWp n T hT').2.1, ?_, ?_, ?_, g1, g2, g3, ENNReal.toReal_pos (hBx0 n).ne' measure_ball_lt_top.ne⟩
    · rw [hνW n]; exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hcν).ne' (hBy0 n).ne'
    · rw [hνW n]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
    · rw [hBox n]; exact eT.continuous.measurable (hΨm n)
    · rintro y ⟨T, hTW, g, -, rfl⟩
      have hinj : Function.Injective (Matrix.mulVecLin
          ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := by
        intro x x' h
        have h2 := congrArg (fun v => Matrix.mulVec (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g)⁻¹ : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) v) h
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using h2
      exact LinearIndependent.map' (hWp n T hTW).2.2 _ (LinearMap.ker_eq_bot.2 hinj)
    · rw [hμB n]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hΨt n)
  · intro U' hU'
    have h1 : eH.symm ⁻¹' U' ∈ 𝓝 (eH T0) := by
      apply eH.symm.continuous.continuousAt.preimage_mem_nhds
      rw [eH.symm_apply_apply]; exact hU'
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 h1
    filter_upwards [hρlim.eventually (gt_mem_nhds hε)] with n hn
    intro T hTW
    have h2 : eH T ∈ ball (eH T0) ε := ball_subset_ball hn.le hTW
    have h3 := hεs h2
    simpa [eH.symm_apply_apply] using h3
  · exact hGl ρ hρp hρlim
  · have hi := img_ratio (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) hΨ' hinj hdet A hAm hAU
      hA0 hAt (fun V' hV' => by
        obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hV'
        filter_upwards [hρlim.eventually (gt_mem_nhds hε)] with n hn
        rw [hAb n]; exact (ball_subset_ball hn.le).trans hεs)
    have hval : cμ / cν * d = tVal X u' := by rw [← harith]; ring
    change Tendsto _ atTop (𝓝 (tVal X u'))
    rw [← hval]
    refine (hi.const_mul (cμ / cν)).congr fun n => ?_
    have hx : 0 < (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal :=
      ENNReal.toReal_pos (hBx0 n).ne' measure_ball_lt_top.ne
    have hy : 0 < (volume (ball (eH T0) (ρ n))).toReal := ENNReal.toReal_pos (hBy0 n).ne' measure_ball_lt_top.ne
    rw [hμB n, hνW n, hvolA n, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hcμ.le, ENNReal.toReal_ofReal hcν.le]
    field_simp

end PI.AprimeInfW
end
end
