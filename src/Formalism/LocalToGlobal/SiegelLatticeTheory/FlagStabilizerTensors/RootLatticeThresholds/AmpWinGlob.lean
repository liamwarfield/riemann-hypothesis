module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsLowUnitHBaseVector
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalAmpRoot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalBetaInf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSB

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants
  Formalism.L2.SG.Pf.Choice Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.WuDec

namespace Formalism.L2.SG.Pf.AmpWinGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word)

def muNv (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) := muNl C (X.pl v) v

def muHv (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) := muHl C u (X.pl v) v

theorem place_all (hLF : LocFactor C) (hB : WuBessel C) (v : InfinitePlace X.B.I.F) :
    SigmaFinite (muNv C v) ∧ SigmaFinite (muHv C u v) ∧ QPK.InvOn (muNv C v) (Nloc X u v) ∧
      QPK.InvOn (muHv C u v) (Hloc X u v) ∧ muHv C u v Set.univ = 1 ∧
      QPK.mulMap (muNv C v) (muHv C u v) (QPK.prodSet (Nloc X u v) (Hloc X u v))ᶜ = 0 ∧
      ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNv C v) (muHv C u v)) = 1) ∧
        ∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) =
          l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v)) := by
  have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w →
      SigmaFinite (muNl C τ w) ∧ SigmaFinite (muHl C u τ w) ∧ QPK.InvOn (muNl C τ w) (Nloc X u w) ∧
      QPK.InvOn (muHl C u τ w) (Hloc X u w) ∧ muHl C u τ w Set.univ = 1 ∧
      QPK.mulMap (muNl C τ w) (muHl C u τ w) (QPK.prodSet (Nloc X u w) (Hloc X u w))ᶜ = 0 ∧
      ∃ β : Formalism.REAL.UJ (X.B.I.ε w) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ w) (muHl C u τ w)) = 1) ∧
        ∫⁻ y, β y * ‖X.Wloc u w y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε w)) = l2SG (C.nuS u τ) (phiOf hB u τ) := by
    rintro τ w rfl
    have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
    have hH1 : muHl C u τ (vOf X τ) Set.univ = 1 := by
      have h : (muHl C u τ (vOf X τ)).map (eT C τ (vOf X τ)) Set.univ = C.muW u τ Set.univ := by
        rw [map_muHl C u τ]
      rw [Measure.map_apply (eT_emb C τ (vOf X τ)).measurable MeasurableSet.univ, Set.preimage_univ,
        C.muW_one u τ] at h
      exact h
    have hconc : QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))
        (QPK.prodSet (Nloc X u (vOf X τ)) (Hloc X u (vOf X τ)))ᶜ = 0 := by
      have hHH : Hloc X u (vOf X τ) = Hfix X u (vOf X τ) := Hloc_eq X u (vOf X τ)
      rw [hHH]
      exact (invOn_mulMap C u τ).2.2.1
    obtain ⟨β, hβm, hβ1, hid⟩ := loc_main C u τ hLF hB
    exact ⟨sf_muNl C τ hθ, sf_muHl C u τ, invOn_muNl C u τ, invOn_muHl C u τ, hH1, hconc, β, hβm, hβ1, hid⟩
  exact key (X.pl v) v (X.pl.symm_apply_apply v)

theorem map_trInf (hsf : ∀ v, SigmaFinite (muNv C v)) (hθ : 0 < θ) :
    MeasurableEmbedding (Formalism.L2.SG.LoopTerm.trInf C) ∧
      (Measure.pi (muNv C)).map (Formalism.L2.SG.LoopTerm.trInf C) = Formalism.L2.SG.LoopTerm.dnB D θ := by
  have hPemb : MeasurableEmbedding
      (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) :=
    (Topology.IsClosedEmbedding.piMap fun τ =>
      Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (X.pl.symm τ)) (C.isT τ).2.1).measurableEmbedding
  have htr : Formalism.L2.SG.LoopTerm.trInf C = (Pi.map (fun τ => eT C τ (X.pl.symm τ)) :
      (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) ∘
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
    funext x τ
    rfl
  refine ⟨htr ▸ hPemb.comp (MeasurableEquiv.measurableEmbedding _), ?_⟩
  rw [htr, ← Measure.map_map hPemb.measurable (MeasurableEquiv.measurable _)]
  have h1 : (Measure.pi (muNv C)).map (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm =
      Measure.pi (fun τ => muNv C (X.pl.symm τ)) :=
    ((measurePreserving_piCongrLeft (muNv C) X.pl.symm).symm _).map_eq
  have h2 : (fun τ => muNv C (X.pl.symm τ)) = fun τ => muNl C τ (X.pl.symm τ) := by
    funext τ
    show muNl C (X.pl (X.pl.symm τ)) (X.pl.symm τ) = muNl C τ (X.pl.symm τ)
    rw [Equiv.apply_symm_apply]
  rw [h1, h2]
  have hmap : ∀ τ, (muNl C τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)) = muNB D θ := fun τ => map_muNl C τ hθ
  have : ∀ τ, SigmaFinite ((muNl C τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ))) := fun τ => by
    rw [hmap τ]; exact (muNB_haar (D := D) hθ).1
  refine (Measure.pi_map_pi (μ := fun τ => muNl C τ (X.pl.symm τ)) (f := fun τ => eT C τ (X.pl.symm τ))
    (fun τ => (eT_emb C τ (X.pl.symm τ)).measurable.aemeasurable)).trans ?_
  simp_rw [hmap]
  rfl

theorem massU_of (Y : Formalism.L2.SG.Full.Full X) (hLF : LocFactor C) (hB : WuBessel C) :
    Formalism.L2.SG.Pf.AmpWin.MassU Y u C hB := by
  have hθ : 0 < θ := by
    obtain ⟨τ⟩ := Formalism.L2.SG.LoopTerm.tau_nonempty D
    exact Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  choose hsfN hsfH hN hH hH1 hconc β hβm hβ1 hloc using place_all C u hLF hB

  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; exact Iff.rfl
  have hpiH : Set.pi Set.univ (Hloc X u) = Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := X.muN_haar u
  obtain ⟨k1, k2, k3, k4⟩ := X.muH_haar u
  have hHfix : ∀ v, Hloc X u v = Hfix X u v := fun v => Hloc_eq X u v
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Nloc X u))
    (isClosed_set_pi fun v _ => (place_facts X u v).1) (QPK.isGrp_pi _ fun v => (place_facts X u v).2.2.1)
    (X.muN u) (Measure.pi (muNv C)) ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    (QPK.invOn_pi _ _ hN)
  obtain ⟨cH, hcH0, hcHt, hcH⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Hloc X u))
    (isClosed_set_pi fun v _ => by rw [hHfix]; exact (place_facts X u v).2.1.isClosed)
    (QPK.isGrp_pi _ fun v => by rw [hHfix]; exact (place_facts X u v).2.2.2.1)
    (X.muH u) (Measure.pi (muHv C u)) ⟨k1, k2, by rw [hpiH]; exact k3, by rw [hpiH]; exact k4⟩
    (QPK.invOn_pi _ _ hH)

  set F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun v y => ‖X.Wloc u v y‖ₑ ^ 2 with hF_def
  have hFm : ∀ v, Measurable (F v) := fun v => (X.Wloc_cont u v).enorm.measurable.pow_const 2
  have hFinv : ∀ v, ∀ m ∈ Nloc X u v, ∀ h ∈ Hloc X u v, ∀ x, F v (m * h * x) = F v x := by
    intro v m hm h hh x
    have hs := mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)
    show ‖X.Wloc u v (m * h * x)‖ₑ ^ 2 = ‖X.Wloc u v x‖ₑ ^ 2
    rw [← enorm_norm (X.Wloc u v (m * h * x)), norm_Wloc_inv X u v hs, enorm_norm]
  set f : X.B.I.Ginf → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hf_def
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := X.nuQ_weil u f hfm
  have hL1 : ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ y, β v y * F v y ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
    QPK.lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))
  have hin : ∀ x, ∫⁻ s, f (s * x) ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) =
      (cN * cH) * ∏ v, F v (x v) := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      hcN, hcH, Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have e1 : ∀ p : X.B.I.Ginf × X.B.I.Ginf,
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [e1]
    rw [QPK.lintegral_pi_prod_mul (muNv C) (muHv C u) (fun v z => β v (z * x v) * F v (z * x v))
      (fun v => ((hβm v).comp (measurable_mul_const _)).mul ((hFm v).comp (measurable_mul_const _)))]
    have e2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(QPK.mulMap (muNv C v) (muHv C u v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(QPK.mulMap (muNv C v) (muHv C u v)), s ∈ QPK.prodSet (Nloc X u v) (Hloc X u v) :=
        mem_ae_iff.mpr (hconc v)
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        simp only [hFinv v m hm h hh])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [e2]
    ring
  simp_rw [hin] at key
  have hPm : Measurable (fun x : X.B.I.Ginf => ∏ v, F v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hFm v).comp (measurable_pi_apply v)
  rw [lintegral_const_mul _ hPm, hL1] at key
  have hW1 : ∫⁻ x, ∏ v, F v (x v) ∂(X.nuQ u) = 1 := by
    rw [← (X.Wu_spec u).2.2.2.2]
    refine lintegral_congr fun x => ?_
    rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu X u x, Finset.prod_pow]
  rw [hW1, mul_one] at key

  have hprod : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = cN * cH := by
    rw [← key]
    refine (Fintype.prod_equiv X.pl (fun v => l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v))) _
      (fun v => rfl)).symm.trans ?_
    exact Finset.prod_congr rfl fun v _ => (hloc v).symm

  obtain ⟨hemb, hmapT⟩ := map_trInf C (fun v => hsfN v) hθ
  have hcov : Measure.pi (muNv C) (Y.FN u) =
      Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) := by
    rw [← hmapT, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  have hNF : X.muN u (Y.FN u) = cN * Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) := by
    rw [hcN, Measure.smul_apply, smul_eq_mul, hcov]
  have hHU : X.muH u Set.univ = cH := by
    rw [hcH, Measure.smul_apply, smul_eq_mul, ← Set.pi_univ, Measure.pi_pi]
    rw [Finset.prod_eq_one fun v _ => hH1 v, mul_one]
  unfold Formalism.L2.SG.Pf.AmpWin.MassU Formalism.L2.SG.LoopTerm.covN
  rw [hNF, hHU, ← ENNReal.toReal_prod, hprod, ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

theorem ampWin_of_loc (Y : Formalism.L2.SG.Full.Full X) (u' : D.what₂.Word) (hLF : LocFactor C) (hB : WuBessel C) :
    Formalism.L2.SG.Pf.AmpWin.AmpWinP Y u u' C hB :=
  Formalism.L2.SG.Pf.AmpWin.ampWin_of Y u u' C hB (massU_of C u Y hLF hB) (massU_of C u' Y hLF hB)
    (fun τ => Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ) (fun τ => Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ)

theorem K0_mem_covWin_of_locFactor_wuBessel (Y : Formalism.L2.SG.Full.Full X) (u' : D.what₂.Word) (hLF : LocFactor C) (hB : WuBessel C)
    (hV : 0 < X.volK2)
    (hc : 0 < Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') {large₂} {C1 : ℝ}
    (hW : Formalism.L2.SG.LoopTerm.CovWinN (Y := Y) C large₂ C1 u u') :
    0 < Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB ∧
      Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB) := by
  have hA := ampWin_of_loc C u Y u' hLF hB
  exact ⟨Formalism.L2.SG.Pf.AmpWin.minWeight_pos Y u u' C hB hA hV hc, Formalism.L2.SG.Pf.AmpWin.K0_mem_covWin_of_ampWin Y u u' C hB hA hV hW⟩

end Formalism.L2.SG.Pf.AmpWinGlob
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmplitudeBoundsAllChoicesUniform
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.Pf.OOCore3 Formalism.L2.SG.Pf.LocNorm
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AmplitudeBoundsAllChoices {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ θ : ℝ, 0 < θ ∧ normWin D large₂ C1 θ ∧ ∀ (C : Choice X θ) (hB : WuBessel C),
    (∃ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl ∧ LocUniqP u u' C hB νl) ∧
    0 < K0 Y u u' C hB ∧ WinK large₂ C1 (K0 Y u u' C hB) ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def AmplitudeBoundsAllChoicesUniform : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → AmplitudeBoundsAllChoices large₂ Y u u' ν C1 Cn Ire

end Formalism.L2.SG.Pf.ThmBChain6
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

def HaarTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsHaarOn (RStab D.R.k D.R.rS (gB C τ γ)) (muRB C τ μRv)

def QuotTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsQuotLoc μRv ν →
    PI.BesselPeriodGGP.IsQuotMeas (locW C u u' τ).μG
      ((muRB C τ μRv).map (fun x i j => ((gB C τ γ)⁻¹ * Matrix.of x * gB C τ γ) i j))
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ))

def PinHypAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) : Prop :=
  0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C6.IsRelevant (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
    (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) ∧
  IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
    μRv ∧ IsQuotLoc μRv ν

def CutAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
          (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x))) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (fcAt C u u' τ a b ξ ξ' c) p) (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).μSS

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSF
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gap

def GapEv {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ y : ℝ, ∀ x, y ≤ x → ∀ i : Fm.Ix x, Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i)

def CG (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ GapEv Fm

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def selG : SSel (CG 𝒞) := fun Fm h => sel Fm h.1

def yFG : ∀ {eps : ℝ} (Fm : FamP eps), CG 𝒞 Fm → ℝ := fun _ h => Classical.choose h.2

theorem gap_of {eps : ℝ} {Fm : FamP eps} (h : CG 𝒞 Fm) {x : ℝ} (hx : yFG Fm h ≤ x) (i : Fm.Ix x) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
  Classical.choose_spec h.2 x hx i

theorem hyFG (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) : YFOK (selG sel) yFG := by
  intro eps Fm hc x hx h0 hy i
  have hg := gap_of hc hy i
  exact ⟨hFX _ _ hg, (hWu _ hg _).1⟩

def CX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Formalism.L2.SG.LocWSOf.Choice X 1 :=
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  Classical.choice (Formalism.L2.SG.Pf.choiceExists X 1 one_pos)


theorem closed_sub {𝒞' : FamClass} (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm)
    {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) : Closed 𝒞' P := by
  obtain ⟨e, he, H⟩ := h
  exact ⟨e, he, fun eps h1 h2 => by
    obtain ⟨K, hK⟩ := H eps h1 h2
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (hs Fm hc) hL⟩⟩

variable (C0 : ℝ)

theorem loopRowS_of_sub (hG : Closed 𝒞 fun Fm _ => 𝒞 Fm → GapEv Fm) (h : LoopRowS C0 (CG 𝒞) (selG sel)) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  obtain ⟨e1, he1, H1⟩ := h aF
  obtain ⟨e2, he2, H2⟩ := hG
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  refine ⟨K1.sup K2, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  intro hc'
  have hg := hK2 Fm CH hc hL2 hc'
  exact hK1 Fm CH ⟨hc', hg⟩ hL1 ⟨hc', hg⟩

end Gap

section PartC

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def RMeasExAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (u u' : D.what₂.Word),
    (∀ τ, GoodW D τ u u' 1 (Formalism.L2.SG.LocWSOf.locW C u u' τ)) → LoopTerm.RMeasEx hI C u u'

def JFactNAll : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF))
    (C : Formalism.L2.SG.LocWSOf.Choice X 1) (hB : Formalism.L2.SG.LocWSOf.WuBessel C) (u u' : D.what₂.Word),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D → LoopTerm.JFactN hI C hB u u'


variable (C0 : ℝ)

end PartC

end Formalism.L2.SG.LoopsTies
end
end
