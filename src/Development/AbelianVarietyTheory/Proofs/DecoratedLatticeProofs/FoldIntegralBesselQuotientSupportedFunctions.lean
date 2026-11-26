module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.WeilQuotientGlobalAssumptions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsBuiltPlaceOfCompactTest

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Mi.BesHaar

open scoped NNReal ENNReal

noncomputable def prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) :
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) ≃ₜ*
      besGrp B.d B.o where
  toFun p := ⟨(iotaX X h).symm ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)), by
    rw [((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _), ContinuousMulEquiv.apply_symm_apply]
    exact ⟨p.1.2, p.2.2⟩⟩
  invFun s := (⟨(iotaX X h s.1).1, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).1⟩,
    ⟨(iotaX X h s.1).2, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).2⟩)
  left_inv p := by
    ext <;> simp
  right_inv s := by
    ext
    simp
  map_mul' p q := by
    ext
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul]
    rw [← map_mul]
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ((iotaX X h).symm.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
      (iotaX X h).continuous.comp continuous_subtype_val
    exact ((continuous_fst.comp hc).subtype_mk _).prodMk ((continuous_snd.comp hc).subtype_mk _)

theorem iota_prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    (p : Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) :
    iotaX X h (prodEquiv X h B p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) := by
  show iotaX X h ((iotaX X h).symm _) = _
  simp

theorem lintegral_besGrp_eq : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))), μSf.IsHaarMeasure → SigmaFinite μSf → IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) → ∃ c : ℝ, 0 < c ∧ ∀ Φ : X.B.I.GA → ENNReal, Measurable Φ → ∫⁻ s, Φ (iotaX X h s.1) ∂B.lev.μR = ENNReal.ofReal c * ∫⁻ a, ∫⁻ t, Φ (a, t.1) ∂μSf ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X h u ψ A B μSf hSf hσf hS
  haveI := hSf
  haveI := hσf
  haveI : SFinite μSf := by
    haveI : ∀ n, Fact (μSf (disjointed (spanningSets μSf) n) < ⊤) :=
      fun n => ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μSf n)⟩
    exact ⟨⟨fun n => μSf.restrict (disjointed (spanningSets μSf) n), fun _ => inferInstance,
      (sum_restrict_disjointed_spanningSets μSf μSf).symm⟩⟩
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hSi : IsClosed ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u
  haveI : LocallyCompactSpace (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) := hSi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hHaar', -, -⟩ := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS
  haveI := hHaar'
  have hmap := Formalism.L2.SG.Pf.map_comap_subgroup (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS.2.2.1
  set μS' := (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).comap ((↑) : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) → X.B.I.Ginf) with hμS'
  haveI : SigmaFinite μS' := inferInstance
  let e := GlobalTheory.Core.Mi.BesHaar.prodEquiv X h B
  haveI : LocallyCompactSpace ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : (B.lev.μR.map e.symm).IsHaarMeasure := e.symm.isHaarMeasure_map B.lev.μR
  haveI : (μS'.prod μSf).IsHaarMeasure := Measure.prod.instIsHaarMeasure μS' μSf
  have hcpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (B.lev.μR.map e.symm) (μS'.prod μSf)
  set c : ℝ≥0 := (B.lev.μR.map e.symm).haarScalarFactor (μS'.prod μSf) with hc
  have hme : Measurable (e : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) → besGrp B.d B.o) := e.continuous.measurable
  have hEq : B.lev.μR = (c • μS'.prod μSf).map e := by
    rw [hc, ← Measure.isMulLeftInvariant_eq_smul, Measure.map_map hme (show Measurable (e.symm : besGrp B.d B.o → (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) from e.symm.continuous.measurable)]
    simp
  refine ⟨(c : ℝ), hcpos, fun Φ hΦ => ?_⟩
  have hv : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hΦ' : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) := hΦ.comp hv
  have hin : Measurable (fun a : X.B.I.Ginf => ∫⁻ t, Φ (a, (t : X.B.I.Gf)) ∂μSf) := by
    have : Measurable (Function.uncurry fun (a : X.B.I.Ginf) (t : Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ (a, (t : X.B.I.Gf))) :=
      hΦ.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
    exact this.lintegral_prod_right'
  have hΦι : Measurable (fun s : besGrp B.d B.o => Φ (iotaX X h s.1)) :=
    hΦ.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [hEq, lintegral_map hΦι hme]
  have hιe : ∀ p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), iotaX X h (e p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) :=
    GlobalTheory.Core.Mi.BesHaar.iota_prodEquiv X h B
  simp_rw [hιe]
  rw [lintegral_smul_measure, lintegral_prod _ hΦ'.aemeasurable, ← hmap,
    lintegral_map hin measurable_subtype_coe, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.Core.Mi.BesHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_besselGroup_haar_eq_const_mul_prod : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))), μSf.IsHaarMeasure → SigmaFinite μSf → IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) → ∃ c : ℝ, 0 < c ∧ ∀ Φ : X.B.I.GA → ENNReal, Measurable Φ → ∫⁻ s, Φ (iotaX X h s.1) ∂B.lev.μR = ENNReal.ofReal c * ∫⁻ a, ∫⁻ t, Φ (a, t.1) ∂μSf ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  first | exact @GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq | exact GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq | (intros; apply GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MuSHaar

open scoped Pointwise

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Sinf Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem muN_conj (h : X.B.I.Ginf) (hh : h ∈ Hinf X u) :
    (X.muN u).map (fun x => h * x * h⁻¹) = X.muN u := by
  have hNc : IsClosed (X.NinfU u) := isClosed_ninfU X u
  have hHc : IsCompact ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := hinf_compact X u
  obtain ⟨-, hfin, hpos⟩ := haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (isClosed_ninfU X u)
    (X.muN u) (X.muN_haar u)
  have hgN : QPK.IsGrp (X.NinfU u) :=
    ⟨(NinfSub X.eR (X.zR u)).one_mem, fun a ha b hb => (NinfSub X.eR (X.zR u)).mul_mem ha hb,
      fun a ha => (NinfSub X.eR (X.zR u)).inv_mem ha⟩
  have hgH : QPK.IsGrp ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) :=
    ⟨(Hinf X u).one_mem, fun a ha b hb => (Hinf X u).mul_mem ha hb, fun a ha => (Hinf X u).inv_mem ha⟩
  exact QPK.conjugation_invariant_measure X.B.I.Ginf (X.NinfU u) _ hNc hHc hgN hgH
    (fun h hh m hm => conj_ninf X u hh hm) (X.muN u) (X.muN_haar u) ⟨fun K hK => hfin K hK⟩
    (fun U hU hne => (hpos U hU hne).ne') h hh

theorem muS_compact {K : Set X.B.I.Ginf} (hK : IsCompact K) :
    ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) K < ⊤ := by
  haveI := (X.muN_haar u).1
  haveI := (X.muH_haar u).1
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  set L : Set X.B.I.Ginf := (K * ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)⁻¹) ∩ X.NinfU u with hL
  have hLc : IsCompact L := (hK.mul (hinf_compact X u).inv).inter_right (isClosed_ninfU X u)
  rw [Measure.map_apply hmul hK.isClosed.measurableSet]
  calc ((X.muN u).prod (X.muH u)) ((fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) ⁻¹' K)
      ≤ ((X.muN u).prod (X.muH u)) (L ×ˢ Set.univ) := by
        refine measure_mono_ae ?_
        filter_upwards [ae_NH X u] with p hp hpK
        refine ⟨⟨?_, hp.1⟩, Set.mem_univ _⟩
        have e : p.1 = (p.1 * p.2) * p.2⁻¹ := by group
        rw [e]
        exact Set.mul_mem_mul hpK (Set.inv_mem_inv.2 hp.2)
    _ = X.muN u L * X.muH u Set.univ := Measure.prod_prod _ _
    _ < ⊤ := ENNReal.mul_lt_top (muN_compact X u hLc) (hFinite_holds X u)

theorem muS_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X u
  obtain ⟨hNσ, hN0, -, hNinv⟩ := X.muN_haar u
  obtain ⟨hHσ, hH0, -, hHinv⟩ := X.muH_haar u
  haveI := hNσ
  haveI := hHσ
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : IsFiniteMeasureOnCompacts (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) :=
      ⟨fun K hK => muS_compact X u hK⟩
    infer_instance
  · intro h0
    have h1 := congrArg (fun μ : Measure X.B.I.Ginf => μ Set.univ) h0
    simp only [Measure.map_apply hmul MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply] at h1
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero,
      Measure.measure_univ_eq_zero] at h1
    exact h1.elim hN0 hH0
  · exact ae_iff.1 (Formalism.L2.SG.WuDecayPf.muSOn X u)
  · intro s hs
    obtain ⟨h0, hh0, n0, hn0, rfl⟩ := levi X u hs
    have hf : (X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹) = X.muN u := by
      have e : (fun x => h0 * (n0 * x) * h0⁻¹) = (fun x => h0 * x * h0⁻¹) ∘ (fun x => n0 * x) := rfl
      rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), hNinv n0 hn0, muN_conj X u h0 hh0]
    have hg : (X.muH u).map (fun y => h0 * y) = X.muH u := hHinv h0 hh0
    have hfm : Measurable (fun x : X.B.I.Ginf => h0 * (n0 * x) * h0⁻¹) := by fun_prop
    have hgm : Measurable (fun y : X.B.I.Ginf => h0 * y) := by fun_prop
    calc (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).map (fun x => h0 * n0 * x)
        = ((X.muN u).prod (X.muH u)).map ((fun x => h0 * n0 * x) ∘ (fun p => p.1 * p.2)) :=
          Measure.map_map (by fun_prop) hmul
      _ = ((X.muN u).prod (X.muH u)).map ((fun p => p.1 * p.2) ∘
            Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y)) := by
          congr 1; funext p; simp only [Function.comp, Prod.map]; group
      _ = (((X.muN u).prod (X.muH u)).map
            (Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y))).map (fun p => p.1 * p.2) :=
          (Measure.map_map hmul (hfm.prodMap hgm)).symm
      _ = (((X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹)).prod ((X.muH u).map (fun y => h0 * y))).map
            (fun p => p.1 * p.2) := by rw [Measure.map_prod_map _ _ hfm hgm]
      _ = ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) := by rw [hf, hg]

end GlobalTheory.MuSHaar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  first | exact @GlobalTheory.MuSHaar.muS_isHaarOnSet | exact GlobalTheory.MuSHaar.muS_isHaarOnSet | (intros; apply GlobalTheory.MuSHaar.muS_isHaarOnSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarFiniteAdeleDisintegrationStabilizerCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarFiniteAdeleDisintegrationStabilizerCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology

theorem exists_idem_of_subspace {E : Type} [Field E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    ∃ e : Matrix (Fin n) (Fin n) E, e * e = e ∧ ∀ x, x ∈ W ↔ e *ᵥ x = x := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  obtain ⟨p, hp⟩ : ∃ p : Matrix (Fin n) (Fin n) E, ∀ x, p *ᵥ x = Submodule.projection W W' hc x :=
    ⟨LinearMap.toMatrix' _, fun x => LinearMap.toMatrix'_mulVec _ x⟩
  have h1 : ∀ x, p *ᵥ x ∈ W := fun x => hp x ▸ Submodule.projection_apply_mem hc x
  have h2 : ∀ x ∈ W, p *ᵥ x = x := fun x hx => (hp x).trans (Submodule.projection_apply_of_mem_left hc hx)
  refine ⟨p, Matrix.ext_iff_mulVec.2 fun y => by rw [← Matrix.mulVec_mulVec, h2 _ (h1 y)], fun x =>
    ⟨fun hx => h2 x hx, fun hx => hx ▸ h1 x⟩⟩

theorem span_incl_eq (I : AutInst) (T : Set (Fin I.n → I.E)) :
    Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T) =
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
        ((fun w i => GlobalTheory.UnipApprox.inc I (w i)) '' (Submodule.span I.E T : Set (Fin I.n → I.E))) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((0 : Fin I.n → I.E) i)) = 0 := by ext; simp
      beta_reduce; rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((x + y) i)) =
          (fun i => GlobalTheory.UnipApprox.inc I (x i)) + fun i => GlobalTheory.UnipApprox.inc I (y i) := by ext; simp
      rw [SetLike.mem_coe] at hx hy; beta_reduce at hx hy ⊢; rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((a • x) i)) =
          GlobalTheory.UnipApprox.inc I a • fun i => GlobalTheory.UnipApprox.inc I (x i) := by ext; simp
      rw [SetLike.mem_coe] at hx; beta_reduce at hx ⊢; rw [this]; exact Submodule.smul_mem _ _ hx

theorem isClosed_cond (I : AutInst) (v : Fin I.n → I.E) (T : Set (Fin I.n → I.E)) :
    IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} := by
  obtain ⟨t, hr, h2, -, -, -, hind⟩ := GlobalTheory.UnipApprox.exists_top I
  obtain ⟨e, he, hW⟩ := exists_idem_of_subspace (Submodule.span I.E T)
  have hset : {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} =
      {x | e.map (GlobalTheory.UnipApprox.inc I) *ᵥ ((I.fmat x - 1) *ᵥ incl I v) = (I.fmat x - 1) *ᵥ incl I v} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [span_incl_eq]
    exact GlobalTheory.UnipApprox.mem_span_iff (GlobalTheory.UnipApprox.inc I) he _ hW _
  rw [hset]
  have hc : Continuous fun x : I.Gf => I.fmat x := Units.continuous_val.comp hind.continuous
  have hc2 : Continuous fun x : I.Gf => (I.fmat x - 1) *ᵥ incl I v :=
    (hc.sub continuous_const).matrix_mulVec continuous_const
  exact isClosed_eq (continuous_const.matrix_mulVec hc2) hc2

theorem isClosed_sfin (I : AutInst) {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    IsClosed (Sfin I e z) := by
  have h1 : ∀ a : Fin r, IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I (e a) ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => incl I (e b)) '' {b | b.1 < a.1})} := by
    intro a
    have := isClosed_cond I (e a) (e '' {b : Fin r | b.1 < a.1})
    rwa [Set.image_image] at this
  have h2 : IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I z ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (e b))} := by
    have := isClosed_cond I z (Set.range e)
    rwa [← Set.range_comp] at this
  unfold Sfin
  rw [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter h1).inter h2

end GlobalTheory.SfinHaar

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology MeasureTheory

theorem disint_finPart : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    ∃ μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), μSf.IsHaarMeasure ∧ SigmaFinite μSf ∧
      ∃ c : ℝ, 0 < c ∧ ∀ φ : X.B.I.Gf → ENNReal, Measurable φ →
        (∀ x, φ x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x = s * X.xu u * k) →
        ∫⁻ x, φ x ∂X.B.μf = ENNReal.ofReal c * ∫⁻ t, ∫⁻ k in X.K2, φ (t.1 * X.xu u * k) ∂X.B.μf ∂μSf := by
  intro D X u
  set G := X.B.I.Gf
  set S := Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u) with hSdef
  set K := X.K2 with hKdef
  set x := X.xu u with hxdef
  haveI : SecondCountableTopology G := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : X.B.μf.IsHaarMeasure := X.B.haar
  have hKg := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKt := Formalism.L2.SG.Pf.level_subgroup_compact_open X
  have hK1 : (1 : G) ∈ K := hKg.1
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := hKg.2.1
  have hKinv : ∀ a ∈ K, a⁻¹ ∈ K := hKg.2.2.1
  have hKo : IsOpen K := hKt.1
  have hKc : IsCompact K := hKt.2
  haveI : LocallyCompactSpace G := hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds hK1)
  have hSc : IsClosed (S : Set G) := isClosed_sfin X.B.I X.eR (X.zR u)

  set C : Set G := {g | x⁻¹ * g * x ∈ K} with hCdef
  have hCeq : C = (fun k => x * k * x⁻¹) '' K := by
    ext g
    constructor
    · intro hg; exact ⟨x⁻¹ * g * x, hg, by group⟩
    · rintro ⟨k, hk, rfl⟩
      show x⁻¹ * (x * k * x⁻¹) * x ∈ K
      simpa [mul_assoc] using hk
  have hCc : IsCompact C := hCeq ▸ hKc.image ((continuous_const_mul _).mul continuous_const)
  have hCo : IsOpen C := hKo.preimage ((continuous_const_mul _).mul continuous_const)
  set H : Set S := Subtype.val ⁻¹' C with hHdef
  have hHc : IsCompact H := hSc.isClosedEmbedding_subtypeVal.isCompact_preimage hCc
  have hHo : IsOpen H := hCo.preimage continuous_subtype_val
  have hH1 : (1 : S) ∈ H := by
    show x⁻¹ * ((1 : S) : G) * x ∈ K
    simpa using hK1
  haveI : LocallyCompactSpace S := hHc.locallyCompactSpace_of_mem_nhds_of_group (hHo.mem_nhds hH1)
  let K₀ : TopologicalSpace.PositiveCompacts S := ⟨⟨H, hHc⟩, ⟨1, hHo.subset_interior_iff.2 le_rfl hH1⟩⟩
  set ν : Measure S := Measure.haarMeasure K₀ with hνdef
  haveI : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  haveI : SigmaFinite ν := Measure.IsHaarMeasure.sigmaFinite _
  haveI : SFinite ν := by
    haveI : ∀ n, Fact (ν (disjointed (spanningSets ν) n) < ⊤) :=
      fun n => ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top ν n)⟩
    exact ⟨⟨fun n => ν.restrict (disjointed (spanningSets ν) n), fun _ => inferInstance,
      (sum_restrict_disjointed_spanningSets ν ν).symm⟩⟩
  have hνH : ν H = 1 := Measure.haarMeasure_self
  refine ⟨ν, inferInstance, inferInstance, 1, one_pos, fun φ hφ hsupp => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]

  set Z : Set (S × G) := {p | x⁻¹ * ((p.1 : G)⁻¹ * p.2) ∈ K} with hZdef
  have hZo : IsOpen Z := hKo.preimage
    (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd))
  have hZm : MeasurableSet Z := hZo.measurableSet
  have hKm : MeasurableSet K := hKo.measurableSet
  let F : S → G → ENNReal := fun t g => φ g * Z.indicator 1 (t, g)
  have hF : Measurable (Function.uncurry F) :=
    (hφ.comp measurable_snd).mul (measurable_one.indicator hZm)

  have hA : ∀ t : S, ∫⁻ g, F t g ∂X.B.μf = ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf := by
    intro t
    rw [← lintegral_mul_left_eq_self _ ((t : G) * x), ← lintegral_indicator hKm]
    refine lintegral_congr fun k => ?_
    have e : x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) = k := by group
    by_cases hk : k ∈ K
    · have : ((t, (t : G) * x * k) : S × G) ∈ Z := by show x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hk, Pi.one_apply, mul_one]
    · have : ((t, (t : G) * x * k) : S × G) ∉ Z := by show ¬ x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hk, mul_zero]

  have hC' : ∀ g, ∫⁻ t, F t g ∂ν = φ g := by
    intro g
    by_cases h0 : φ g = 0
    · simp [F, h0]
    obtain ⟨s, hs, k, hk, rfl⟩ := hsupp g h0
    have hset : {t : S | (t, s * x * k) ∈ Z} = (fun t => (⟨s, hs⟩ : S)⁻¹ * t) ⁻¹' H := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      show x⁻¹ * ((t : G)⁻¹ * (s * x * k)) ∈ K ↔ x⁻¹ * (s⁻¹ * (t : G)) * x ∈ K
      have e : x⁻¹ * ((t : G)⁻¹ * (s * x * k)) = (x⁻¹ * (s⁻¹ * (t : G)) * x)⁻¹ * k := by group
      rw [e]
      constructor
      · intro h
        have := hKinv _ (hKmul _ h _ (hKinv _ hk))
        simpa using this
      · intro h
        exact hKmul _ (hKinv _ h) _ hk
    have hmeas : MeasurableSet {t : S | (t, s * x * k) ∈ Z} :=
      hZm.preimage (measurable_id.prodMk measurable_const)
    calc ∫⁻ t, F t (s * x * k) ∂ν = ∫⁻ t, φ (s * x * k) * {t : S | (t, s * x * k) ∈ Z}.indicator 1 t ∂ν := by
          refine lintegral_congr fun t => ?_
          simp only [F]
          congr 1
      _ = φ (s * x * k) * ν {t : S | (t, s * x * k) ∈ Z} := by
          rw [lintegral_const_mul _ (measurable_one.indicator hmeas), lintegral_indicator_one hmeas]
      _ = φ (s * x * k) := by
          rw [hset, measure_preimage_mul, hνH, mul_one]
  calc ∫⁻ g, φ g ∂X.B.μf = ∫⁻ g, ∫⁻ t, F t g ∂ν ∂X.B.μf := lintegral_congr fun g => (hC' g).symm
    _ = ∫⁻ t, ∫⁻ g, F t g ∂X.B.μf ∂ν := (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = ∫⁻ t, ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf ∂ν := lintegral_congr fun t => hA t

end GlobalTheory.SfinHaar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarFiniteAdeleDisintegrationStabilizerCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_finite_adele_disintegration_stabilizer_compact : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), ∃ μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), μSf.IsHaarMeasure ∧ SigmaFinite μSf ∧ ∃ c : ℝ, 0 < c ∧ ∀ φ : X.B.I.Gf → ENNReal, Measurable φ → (∀ x, φ x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x = s * X.xu u * k) → ∫⁻ x, φ x ∂X.B.μf = ENNReal.ofReal c * ∫⁻ t, ∫⁻ k in X.K2, φ (t.1 * X.xu u * k) ∂X.B.μf ∂μSf := by
  first | exact @GlobalTheory.SfinHaar.disint_finPart | exact GlobalTheory.SfinHaar.disint_finPart | (intros; apply GlobalTheory.SfinHaar.disint_finPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Disint

theorem disint : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B
  obtain ⟨μSf, hHaar, hσ, c₁, hc₁, hfin⟩ := GlobalTheory.T.haar_finite_adele_disintegration_stabilizer_compact D X u
  obtain ⟨c₃, hc₃, hR⟩ := GlobalTheory.T.lintegral_besselGroup_haar_eq_const_mul_prod D X h u ψ A B μSf hHaar hσ (GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet D X u)
  refine ⟨c₁ / c₃, div_pos hc₁ hc₃, ?_⟩
  intro G hGm hsupp
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI := hσ
  set μS := ((X.muN u).prod (X.muH u)).map (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) with hμS

  set g : X.B.I.Ginf → ENNReal := fun x => ∫⁻ t, ∫⁻ k in X.K2, G (x, t.1 * X.xu u * k) ∂X.B.μf ∂μSf with hgdef
  have hg : Measurable g := by
    have hΨ : Measurable (fun p : (X.B.I.Ginf × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) × X.B.I.Gf =>
        G (p.1.1, p.1.2.1 * X.xu u * p.2)) :=
      hGm.comp (measurable_fst.fst.prodMk
        (((measurable_subtype_coe.comp measurable_fst.snd).mul_const _).mul measurable_snd))
    exact (hΨ.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)).lintegral_prod_right' (ν := μSf)
  have hL : ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := by
    have e0 : X.B.I.muA X.B.μf = (Formalism.L2.SG.ProjRows.muInf X.B.I).prod X.B.μf := rfl
    rw [e0, lintegral_prod _ hGm.aemeasurable]
    have e1 : ∀ x, ∫⁻ z, G (x, z) ∂X.B.μf = ENNReal.ofReal c₁ * g x := fun x =>
      hfin (fun z => G (x, z)) (hGm.comp measurable_prodMk_left) (fun z hz => hsupp (x, z) hz)
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, X.nuQ_weil u g hg]
  have hRy : ∀ y : X.B.I.Ginf, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR =
      ENNReal.ofReal c₃ * ∫⁻ a, g (a * y) ∂μS := by
    intro y
    set Φ : X.B.I.GA → ENNReal := fun p => ∫⁻ k in X.K2, G (p.1 * y, p.2 * X.xu u * k) ∂X.B.μf with hΦ
    have hΦm : Measurable Φ := by
      have : Measurable (fun q : X.B.I.GA × X.B.I.Gf => G (q.1.1 * y, q.1.2 * X.xu u * q.2)) :=
        hGm.comp ((measurable_fst.fst.mul_const y).prodMk ((measurable_fst.snd.mul_const _).mul measurable_snd))
      exact this.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)
    have e : ∀ s : besGrp B.d B.o, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf = Φ (iotaX X h s.1) := by
      intro s
      refine lintegral_congr fun k => ?_
      congr 1
      ext <;> simp
    simp_rw [e]
    rw [hR Φ hΦm]
  calc ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := hL
    _ = ENNReal.ofReal (c₁ / c₃) * (ENNReal.ofReal c₃ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (div_pos hc₁ hc₃).le, div_mul_cancel₀ _ hc₃.ne']
    _ = _ := by
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (lintegral_congr fun y => hRy y).symm

end GlobalTheory.Core.Mi.Disint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarMeasure_disintegration_besselGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.Disint.disint | exact GlobalTheory.Core.Mi.Disint.disint | (intros; apply GlobalTheory.Core.Mi.Disint.disint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unfold

theorem lintegral_unfold : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ f : X.B.I.GA → ENNReal, Measurable f → ∫⁻ s, f (iotaX X h s.1) ∂B.lev.μR = ∫⁻ s in 𝓢, ∑' σ : Srat X u, f ((σ : X.B.I.GA) * iotaX X h s.1) ∂B.lev.μR := by
  intro D X h u ψ A B 𝓢 h𝓢 f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (D.sp.Y 0).gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (D.sp.Y 0).gram
  have hH : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have hgrp := (GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).2
  have : Countable (GQ (D.sp.Y 0)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (D.sp.Y 0).gram
  have : Countable ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) := Function.Injective.countable
    (f := fun x : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) => (⟨x.1.1, x.2⟩ : GQ (D.sp.Y 0))) fun a b e =>
      Subtype.ext (Subtype.ext (congrArg (Subtype.val : GQ (D.sp.Y 0) → GA D (D.sp.Y 0)) e))
  have : SMulInvariantMeasure ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (besGrp B.d B.o) B.lev.μR :=
    ⟨fun γ S _ => by
      show B.lev.μR ((fun y => (γ : besGrp B.d B.o) * y) ⁻¹' S) = B.lev.μR S
      exact measure_preimage_mul _ (γ : besGrp B.d B.o) S⟩
  have hιm : Measurable (fun s : besGrp B.d B.o => f (iotaX X h s.1)) :=
    hf.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [h𝓢.lintegral_eq_tsum'' (fun s => f (iotaX X h s.1))]
  rw [← lintegral_tsum (f := fun (γ : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (x : besGrp B.d B.o) => f (iotaX X h (γ • x).1))
    (fun γ => (hιm.comp (measurable_const_smul γ)).aemeasurable)]
  refine lintegral_congr fun s => ?_
  let e : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) ≃ Srat X u := Equiv.ofBijective
    (fun γ => ⟨iotaX X h γ.1.1, (hgrp _).1 ⟨Subgroup.mem_subgroupOf.1 γ.2, γ.1.2⟩⟩)
    ⟨fun a b e => Subtype.ext (Subtype.ext ((iotaX X h).injective (congrArg Subtype.val e))), fun σ => by
      have hm := (hgrp ((iotaX X h).symm σ)).2 (by simpa using σ.2)
      exact ⟨⟨⟨_, hm.2⟩, Subgroup.mem_subgroupOf.2 hm.1⟩, Subtype.ext (by simp)⟩⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun γ => ?_
  show f (iotaX X h ((γ : besGrp B.d B.o) * s).1) = f (iotaX X h γ.1.1 * iotaX X h s.1)
  rw [Subgroup.coe_mul, map_mul]

end GlobalTheory.Core.Mi.Unfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_besselGroup_unfold_fundamental_domain : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ f : X.B.I.GA → ENNReal, Measurable f → ∫⁻ s, f (iotaX X h s.1) ∂B.lev.μR = ∫⁻ s in 𝓢, ∑' σ : Srat X u, f ((σ : X.B.I.GA) * iotaX X h s.1) ∂B.lev.μR := by
  first | exact @GlobalTheory.Core.Mi.Unfold.lintegral_unfold | exact GlobalTheory.Core.Mi.Unfold.lintegral_unfold | (intros; apply GlobalTheory.Core.Mi.Unfold.lintegral_unfold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselRationalCutoffFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselRationalCutoffFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem exists_cutoff_srat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  intro D X u Fs hFs
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  haveI : DiscreteTopology (Srat X u) := Formalism.L2.SG.Pf.srat_discrete X u
  haveI : Countable (Srat X u) := Formalism.L2.SG.Pf.countable_of_discrete _
  obtain ⟨_, hleft, _⟩ := Formalism.L2.SG.EvalTOntoExt.instances X
  obtain ⟨F', hF'm, h1, h2⟩ := Formalism.L2.SG.Pf.exists_strictFund (Srat X u)
  have hF' := Formalism.L2.SG.Pf.isFund_of_strict (Srat X u) hF'm h1 h2 (X.B.I.muA X.B.μf)
  refine ⟨F'.indicator 1, measurable_one.indicator hF'm, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := h1 x
    rw [tsum_eq_single (⟨s, hs⟩ : Srat X u)]
    · simp [Set.indicator_of_mem hsx]
    · intro t ht
      have hne : ((t : X.B.I.GA) * x) ∉ F' := by
        intro htx
        apply ht
        have := h2 _ hsx ((t : X.B.I.GA) * s⁻¹) ((Srat X u).mul_mem t.2 ((Srat X u).inv_mem hs))
          (by simpa [mul_assoc] using htx)
        exact Subtype.ext (by simpa [mul_inv_eq_one] using this)
      simp [Set.indicator_of_notMem hne]
  · intro F hFm hFinv
    rw [hFs.setLIntegral_eq hF' F (fun g x => by simpa [Subgroup.smul_def, smul_eq_mul] using hFinv g g.2 x)]
    rw [← lintegral_indicator hF'm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ F' <;> simp [Set.indicator, hx]

end GlobalTheory.Core.Mi.Fold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselRationalCutoffFundamentalDomainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_besselRational_cutoff_fundamentalDomain : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  first | exact @GlobalTheory.Core.Mi.Fold.exists_cutoff_srat | exact GlobalTheory.Core.Mi.Fold.exists_cutoff_srat | (intros; apply GlobalTheory.Core.Mi.Fold.exists_cutoff_srat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem fold_quot : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℝ, 0 < c ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) → (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B 𝓢 h𝓢 Fs hFs
  obtain ⟨c₁, hc₁, hL1⟩ := GlobalTheory.T.haarMeasure_disintegration_besselGroup D X h u ψ A B
  obtain ⟨β, hβm, hβ1, hβF⟩ := GlobalTheory.T.exists_besselRational_cutoff_fundamentalDomain D X u Fs hFs
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hK0 : X.B.μf X.K2 ≠ 0 := hK.2.2.1.ne'
  have hKT : X.B.μf X.K2 ≠ ⊤ := hK.2.2.2.ne
  refine ⟨c₁ * (X.B.μf X.K2).toReal, mul_pos hc₁ (ENNReal.toReal_pos hK0 hKT), ?_⟩
  intro F hFm hFl hFr hFsupp
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D D.R.rS B.lev).1
  haveI : SigmaFinite B.lev.μR := inferInstance
  have hK2m : MeasurableSet X.K2 := (Formalism.L2.SG.Pf.DstarIdxPf.isOpen_levelSubgroup' X).measurableSet
  have hι : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
    (iotaX X h).continuous.comp continuous_subtype_val

  have key : ∀ y : X.B.I.Ginf,
      ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) * F (iotaX X h s.1 * (y, X.xu u) * (1, k))
          ∂X.B.μf ∂B.lev.μR =
        X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR := by
    intro y
    set g : X.B.I.GA := (y, X.xu u) with hg
    have e1 : ∀ s : besGrp B.d B.o,
        ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g * (1, k)) ∂X.B.μf =
          ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂X.B.μf := by
      intro s
      refine setLIntegral_congr_fun hK2m (fun k hk => ?_)
      rw [hFr k hk]
    simp_rw [e1]
    have hmeas : Measurable (Function.uncurry fun (s : besGrp B.d B.o) (k : X.B.I.Gf) =>
        β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g)) := by
      have c1 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g * (1, p.2)) :=
        ((hι.comp continuous_fst).mul continuous_const).mul (continuous_const.prodMk continuous_snd)
      have c2 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g) :=
        (hι.comp continuous_fst).mul continuous_const
      exact (hβm.comp c1.measurable).mul (hFm.comp c2.measurable)
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have e2 : ∀ k ∈ X.K2, ∫⁻ s, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂B.lev.μR =
        ∫⁻ s in 𝓢, F (iotaX X h s.1 * g) ∂B.lev.μR := by
      intro k hk
      have hf : Measurable (fun x : X.B.I.GA => β (x * g * (1, k)) * F (x * g)) :=
        (hβm.comp ((continuous_id.mul continuous_const).mul continuous_const).measurable).mul
          (hFm.comp (continuous_id.mul continuous_const).measurable)
      rw [GlobalTheory.T.lintegral_besselGroup_unfold_fundamental_domain D X h u ψ A B 𝓢 h𝓢 _ hf]
      refine lintegral_congr fun s => ?_
      have e3 : ∀ σ : Srat X u, β ((σ : X.B.I.GA) * iotaX X h s.1 * g * (1, k)) * F ((σ : X.B.I.GA) * iotaX X h s.1 * g) =
          β ((σ : X.B.I.GA) * (iotaX X h s.1 * g * (1, k))) * F (iotaX X h s.1 * g) := by
        intro σ
        rw [mul_assoc (σ : X.B.I.GA) (iotaX X h s.1) g, hFl _ σ.2, mul_assoc (σ : X.B.I.GA) (iotaX X h s.1 * g)]
      simp only [e3]
      rw [ENNReal.tsum_mul_right, hβ1, one_mul]
    rw [setLIntegral_congr_fun hK2m (fun k hk => e2 k hk), setLIntegral_const, mul_comm]
  calc ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := hβF F hFm hFl
    _ = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) *
          F (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
        refine hL1 (fun x => β x * F x) (hβm.mul hFm) (fun x hx => hFsupp x ?_)
        intro h0; exact hx (by rw [h0, mul_zero])
    _ = ENNReal.ofReal c₁ * ∫⁻ y, X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
        congr 1; exact lintegral_congr key
    _ = _ := by
        rw [lintegral_const_mul' _ _ hKT, ← mul_assoc, ENNReal.ofReal_mul hc₁.le, ENNReal.ofReal_toReal hKT]

end GlobalTheory.Core.Mi.Fold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fold_integral_besselQuotient_supportedFunctions : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℝ, 0 < c ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) → (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.Fold.fold_quot | exact GlobalTheory.Core.Mi.Fold.fold_quot | (intros; apply GlobalTheory.Core.Mi.Fold.fold_quot <;> assumption)
end
