module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocNorm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFam


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem midVolumeChain_of_standingHypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT ep0 CV : ℝ} (hT : Ties D)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (he : 0 ≤ ep0) (hCV : 0 ≤ CV) :
    LocalBesselAndTopKernel.MidVolumeChain D large₂ ep0 CV := by
  intro τ
  rw [Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hx : 0 ≤ CV * D.R.k * D.R.m * large₂.sc.L := by positivity
  have h1 : 1 ≤ Real.exp (CV * D.R.k * D.R.m * large₂.sc.L) := Real.one_le_exp hx
  constructor
  · nlinarith
  · nlinarith


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem familyTopBound_of_one_le_sCl {eps : ℝ} (Fm : FamP eps) (h1 : 1 ≤ sCl Fm) (C0 Cg cb Cu cT CT ep0 CV : ℝ) (he : 0 ≤ ep0)
    (hCV : 0 ≤ CV) : LocalBesselAndTopKernel.FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV := by
  refine ⟨0, fun x _ i hh => ?_⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
  exact midVolumeChain_of_standingHypotheses (Fm.ties x i) hh.2.1 (by nlinarith) he hCV


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem localSplitExponents_of_forty_le_sCl {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) (C0 Cg cb Cu cT CT : ℝ) :
    LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT 1 :=
  Formalism.MainNotions.BridgeLemma.family_critical_level_lower_bound Fm (ep0 := 1 / 3) (CV := 0) h40 (by norm_num) le_rfl
    (familyTopBound_of_one_le_sCl Fm (by linarith) C0 Cg cb Cu cT CT (1 / 3) 0 (by norm_num) le_rfl)


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem secondSizeStatement_of_famP {eps : ℝ} (Fm : FamP eps) : LocalBesselAndTopKernel.SecondSizeStatement Fm := fun x i =>
  Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio (Fm.D x i)


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem familyBesselBoundFirstPart_of_ranksF {eps : ℝ} (Fm : FamP eps) {C0 Cg cb Cu cT CT : ℝ} (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT :=
  Formalism.MainNotions.BridgeLemma.level_formula_family Fm C0 Cg cb Cu cT CT (secondSizeStatement_of_famP Fm)
    (Formalism.MainNotions.BridgeLemma.mass_two_bound_family_holds Fm) hR


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem tFrame_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 :=
  Formalism.MainNotions.BridgeLemma.level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith) (familyBesselBoundFirstPart_of_ranksF Fm hR)
    (localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

def aSz (C0 : ℝ) : List ℝ → ℝ := fun _ => Real.exp (3 / 4) * (C0 * Real.exp 1)

theorem one_le_aSz {C0 : ℝ} (h1 : 1 ≤ C0) (l : List ℝ) : 1 ≤ aSz C0 l := by
  unfold aSz
  have a := Real.one_le_exp (show (0 : ℝ) ≤ 3 / 4 by norm_num)
  have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
  have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
  nlinarith


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem sizes3b_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ} (h1 : 1 ≤ C0)
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    OwnEv Fm fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
      Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) := by
  have hb : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4)) := Formalism.MainNotions.BridgeLemma.family_critical_level_ratio Fm h40 le_rfl
  have hc : LocalBesselAndTopKernel.FamilyLowestKType Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4) * (C0 * Real.exp 1)) :=
    Formalism.MainNotions.BridgeLemma.family_level_ratio_bound Fm C0 Cg cb Cu cT CT _ _ le_rfl (familyBesselBoundFirstPart_of_ranksF Fm hR) hb
  have hA := one_le_aSz h1 Fm.cOut
  have hC1 : Real.exp (3 / 4) ≤ aSz C0 Fm.cOut := by
    unfold aSz
    have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
    have := Real.exp_pos (3 / 4)
    nlinarith
  exact Formalism.MainNotions.sizes3bF Fm C0 Cg cb Cu cT CT _ _ _ (Real.exp_pos _).le hC1 le_rfl hb hc


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem szRowsAt_of_ties {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) :
    Formalism.L2.SG.Pf.SzHypOf.SzRowsAt D :=
  ⟨Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio D, hR, Formalism.MainNotions.BridgeLemma.sza_spl_of_data hD,
    fun τ => Formalism.L2.SG.Pf.SzHypFD.fdl_of_ties hT hH hCL τ⟩

section Rows

open Formalism.L2.SG.ThmSOwn

variable (C0 : ℝ)

def RanksRow (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => PX.RanksF Fm C0 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem hTF_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 => tFrame_of_ranks Fm h2 hR


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem hA_of_ranks {𝒞 : FamClass} (h1 : 1 ≤ C0) (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => 1 ≤ aSz C0 Fm.cOut ∧ OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 =>
    ⟨one_le_aSz h1 _, sizes3b_of_ranks Fm h2 h1 hR⟩


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem hRw_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.L2.SG.Pf.SzHypOf.SzRowsAt (Fm.D x i) :=
  closed_with hRk (fun _ => 0) (fun _ => 1) fun Fm _ _ hR _ _ h2 => by
    obtain ⟨x0, H⟩ := hR
    refine ⟨x0, fun x hx i hh => ?_⟩
    have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
    have h2' : 1 ≤ sCl Fm := h2
    exact szRowsAt_of_ties (Fm.ties x i) hh.1 hh.2.1 (by nlinarith) (H x hx i hh)

end Rows

end Formalism.L2.SG.Pf.SzHypFam
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
noncomputable section

open scoped Classical
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.LoopBPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X}

theorem isFundR_fundOf {u u' : D.what₂.Word} (s : Formalism.L2.SG.PackageTie2.TT Y u u') : LoopTerm.IsFundR s (TermOp.FundOf s) := by
  obtain ⟨hm, hex, huniq⟩ := KappaOffDiagonal.fundOf_spec (Closed.FundExistsC_holds D X Y u u') s
  refine ⟨hm, fun r _ => ?_⟩
  obtain ⟨q, hq, hqr⟩ := hex r
  refine ⟨q, ⟨hq, hqr⟩, fun q' hq' => ?_⟩
  have hmem : q' * q⁻¹ ∈ TermOp.ROinf s :=
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).mul_mem hq'.1
      ((TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).inv_mem hq)
  have e : q' * q⁻¹ * (q * r) = q' * r := by group
  have h1 := huniq (q * r) hqr (q' * q⁻¹) hmem (by rw [e]; exact hq'.2)
  exact mul_inv_eq_one.1 h1

theorem pinAll_holds (u u' : D.what₂.Word) : LoopTerm.PinAll (Y := Y) u u' := by
  intro s hrel hG
  have hAt := LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'
  have hRD := Pf.RowForm.RealDecompL.realDecompC_of X Y u u' hAt
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := Pf.RowForm.realDecompC_gamW X Y u u' hRD s hrel hG
  obtain ⟨μw, hH, hmap⟩ := NGPin.pinned_at X u u' (NGPin.pinHaarEx_of_place NGPin.placeHaar_holds) hpt
  obtain ⟨w0, hw0⟩ := hAt s.toTerm hG hrel
  have hw : s.toTerm.atPt (PairVal.ptOf s.toTerm) := PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  refine ⟨⟨PairVal.ptOf s.toTerm, μw.map (fun y => g * y * g⁻¹), TermOp.FundOf s⟩, hw, ?_, isFundR_fundOf s⟩
  exact ⟨RealObj.gamW X u u' (PairVal.ptOf s.toTerm), g, g', μw, NGPin.isPtRep_gamW X u u' hpt, hg, hg', hdec, hH,
    hmap, rfl⟩

section Covol

open Set TermOp TermOp.Vanish

theorem roinf_sub_rset {u u' : D.what₂.Word} (s : Formalism.L2.SG.PackageTie2.TT Y u u') {q : X.B.I.Ginf} (hq : q ∈ ROinf s) : q ∈ Rset s := by
  have hs0 : q ∈ ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin := hq
  obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
  have hl : RatLink X (s.pt⁻¹ * z * s.pt) (s.lin⁻¹ * n * s.lin) :=
    ratLink_mul X (ratLink_mul X (ratLink_inv X s.rep.2.1) hz) s.rep.2.1
  have hs2 := Pf.nLamNinf_holds D X u' s.lam' _ _ hl hn'
  rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
  exact ⟨hzs ▸ Pf.nLamNinf_holds D X u s.lam z n hz hn, hs2⟩

theorem stCoord_cont (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) :
    Continuous (RealObj.stCoord X u' w γ) := by
  unfold RealObj.stCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun v => continuous_pi fun p => continuous_const.mul ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp
    ((continuous_const.mul continuous_id).mul continuous_const)))

theorem muStab_compact (w : Point D.host.E (D.R.rS + 1)) {C : Set (InfinitePlace X.B.I.F → RealObj.FreeE w → ℂ)}
    (hC : IsCompact C) : RealObj.muStab X w C < ⊤ := by
  have e : RealObj.muStab X w = Measure.pi fun _ => Measure.pi fun _ =>
      ((D.host.ka / (X.B.g : ℝ) / Real.pi).toNNReal) • (volume : Measure ℂ) := rfl
  rw [e]
  exact hC.measure_lt_top

theorem covolPos_holds (u u' : D.what₂.Word) : LoopTerm.CovolPos (Y := Y) u u' := by
  intro s hrel hG w μR K hw hP hK
  obtain ⟨γw, g, g', μw, hrep, hg, hg', hdec, hH, hmap, rfl⟩ := hP
  obtain ⟨hσ, h0, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  have := TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  have hcc : Continuous fun y : X.B.I.Ginf => g * y * g⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
  have hcm := hcc.measurable
  have hRm : MeasurableSet (Rset s) := (Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : (μw.map fun y => g * y * g⁻¹) (Rset s)ᶜ = 0 := by
    rw [Measure.map_apply hcm hRm.compl]
    apply measure_mono_null _ hconc
    intro y hy hySt
    exact hy (LoopTerm.stInf_conj hg hg' hdec hySt)
  have hinv : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹).map (fun x => q * x) = μw.map fun y => g * y * g⁻¹ := by
    intro q hq
    have hq' := LoopTerm.stInf_conj_inv hg hg' hdec (roinf_sub_rset s hq)
    rw [Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, ∀ B, MeasurableSet B →
      (μw.map fun y => g * y * g⁻¹) ((fun x => q * x) ⁻¹' B) = (μw.map fun y => g * y * g⁻¹) B := by
    intro q hq B hB
    rw [← Measure.map_apply (measurable_const_mul q) hB, hinv q hq]

  have hpos : (μw.map fun y => g * y * g⁻¹) K ≠ 0 := by
    intro hK0
    have hd := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
      (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) Set.univ K MeasurableSet.univ hKm hKu
    have hz : (μw.map fun y => g * y * g⁻¹) Set.univ = 0 := by
      rw [hd]
      have : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
          (μw.map fun y => g * y * g⁻¹) (Set.univ ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K) = 0 := by
        intro q
        rw [Set.univ_inter, hpre q q.2 K hKm, hK0]
      simp only [this, tsum_zero]
    rw [Measure.measure_univ_eq_zero, Measure.map_eq_zero_iff hcm.aemeasurable] at hz
    exact h0 hz

  obtain ⟨K0, hK0c, hK0⟩ := rational_cocompact_holds D X Y u u' s
  have hK0m : MeasurableSet K0 := hK0c.isClosed.measurableSet
  have h1 : (μw.map fun y => g * y * g⁻¹) K ≤ ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
    calc (μw.map fun y => g * y * g⁻¹) K = (μw.map fun y => g * y * g⁻¹) (K ∩ Rset s) :=
          (measure_inter_conull hRc).symm
      _ ≤ (μw.map fun y => g * y * g⁻¹) (⋃ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
            K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hK0 r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
          X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hB : MeasurableSet (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
        X.B.I.Ginf) * x) ⁻¹' K) := hK0m.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hB]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) K0 K hK0m hKm hKu
  have h4 : ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) K0 := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin)).tsum_eq
      (fun q => (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  have hC : IsCompact ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0) := by
    have e : (fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0 = (fun k => g⁻¹ * k * g) '' K0 := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy; exact ⟨g * y * g⁻¹, hy, by group⟩
      · rintro ⟨k, hk, rfl⟩; convert hk using 1; group
    rw [e]
    exact hK0c.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hfin : (μw.map fun y => g * y * g⁻¹) K0 < ⊤ := by
    rw [Measure.map_apply hcm hK0m]
    have hsc := stCoord_cont u' w γw
    have hI : IsCompact (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := hC.image hsc
    calc μw ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)
        ≤ μw (RealObj.stCoord X u' w γw ⁻¹' (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0))) :=
          measure_mono (Set.subset_preimage_image _ _)
      _ = RealObj.muStab X w (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := by
          rw [← hmap, Measure.map_apply hsc.measurable hI.isClosed.measurableSet]
      _ < ⊤ := muStab_compact w hI
  exact ENNReal.toReal_pos hpos (lt_of_le_of_lt (h1.trans_eq h4) hfin).ne

end Covol

end Formalism.L2.SG.Pf.LoopBPin
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWin
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.AmpWin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

def kap (τ : D.what₂.Tau) : ℝ := Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)

def AmpWinP : Prop :=
  (∏ τ, kap u u' C hB τ) * c0X X u (Y.FN u) * c0X X u' (Y.FN u') =
    X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')

def MassU : Prop :=
  (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal =
    Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal

end Defs

section Lemmas

variable {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hB : WuBessel C)

theorem cOf_pos {u : D.what₂.Word} {τ : D.what₂.Tau} (h0 : l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0)
    (ht : l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤) : 0 < cOf hB u τ := by
  have hl : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos h0 ht.ne
  have hd : 0 < Module.finrank ℂ (X.Vloc u (vOf X τ)) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (X.Vloc u (vOf X τ))) with h | h
    · exfalso
      have : Subsingleton (X.Vloc u (vOf X τ)) := Module.finrank_zero_iff.1 h
      apply h0
      unfold l2SG
      simp [Subsingleton.elim (phiOf hB u τ _) 0]
    · exact h
  unfold cOf
  exact div_pos hl (by exact_mod_cast hd)

theorem kap_eq {u u' : D.what₂.Word} {τ : D.what₂.Tau} (hc : 0 < cOf hB u τ) (hc' : 0 < cOf hB u' τ) :
    kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := by
  unfold kap Formalism.L2.SG.Pf.LocNorm.aT sclOf
  have hb : cOf hB u' τ = (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal / ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := rfl
  have hd0 : (0 : ℝ) ≤ ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hb] at hc' ⊢
  generalize cOf hB u τ = a at hc ⊢
  generalize (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal = L at hc' ⊢
  generalize ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) = d at hd0 hc' ⊢
  have hd : 0 < d := lt_of_le_of_ne hd0 (fun h => by rw [← h, div_zero] at hc'; exact lt_irrefl _ hc')
  have hL : 0 < L := by
    have h1 := mul_pos hc' hd
    rwa [div_mul_cancel₀ _ hd.ne'] at h1
  have hx : 0 ≤ a * d / L := div_nonneg (mul_nonneg hc.le hd.le) hL.le
  first
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (simp only [Complex.normSq_mul, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp)

theorem finrank_tau (u : D.what₂.Word) :
    (Module.finrank ℂ (X.Vpi u) : ℝ) = ∏ τ, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact (Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl).symm

end Lemmas

section Main

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

theorem poincareConstant_of_mass (hM : MassU Y u C hB) :
    c0X X u (Y.FN u) = X.volK2 * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, cOf hB u τ := by
  unfold c0X
  unfold MassU at hM
  rw [mul_assoc X.volK2, hM, finrank_tau u]
  have hP : ∏ τ, cOf hB u τ = (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) / ∏ τ, ((Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℕ) : ℝ) := by
    rw [← Finset.prod_div_distrib]
    rfl
  rw [hP]
  ring

theorem ampWin_of (hM : MassU Y u C hB) (hM' : MassU Y u' C hB)
    (hl : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤)
    (hl' : ∀ τ, l2SG (C.nuS u' τ) (phiOf hB u' τ) ≠ 0 ∧ l2SG (C.nuS u' τ) (phiOf hB u' τ) < ⊤) :
    AmpWinP Y u u' C hB := by
  unfold AmpWinP
  have hc : ∀ τ, 0 < cOf hB u τ := fun τ => cOf_pos hB (hl τ).1 (hl τ).2
  have hc' : ∀ τ, 0 < cOf hB u' τ := fun τ => cOf_pos hB (hl' τ).1 (hl' τ).2
  have hk : ∀ τ, kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := fun τ => kap_eq hB (hc τ) (hc' τ)
  have hP : (∏ τ, kap u u' C hB τ) * (∏ τ, cOf hB u τ) * (∏ τ, cOf hB u' τ) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    have h1 := (hc τ).ne'
    have h2 := (hc' τ).ne'
    rw [hk τ]
    field_simp
  rw [poincareConstant_of_mass _ _ _ _ hM, poincareConstant_of_mass _ _ _ _ hM']
  linear_combination (X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')) * hP

theorem poincareConstant_nonneg (w : D.what₂.Word) : 0 ≤ c0X X w (Y.FN w) := by
  unfold c0X
  first
    | positivity
    | (have := X.levelVolume_pos; positivity)
    | (have := X.volK2_nonneg; positivity)
    | (unfold HidaSetting.volK2; positivity)
    | (unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2; done)

theorem K0_eq_covN_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) :
    Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB =
      Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' := by
  have ha := poincareConstant_nonneg Y u
  have hb := poincareConstant_nonneg Y u'
  unfold Formalism.L2.SG.Pf.LocNorm.K0 Formalism.L2.SG.Pf.OOCore3.sclV TermOp.scl
  unfold AmpWinP at hA
  have hkap : ∀ τ, kap u u' C hB τ = Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ) := fun τ => rfl
  simp only [hkap] at hA
  generalize (∏ τ, Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)) = P at hA ⊢
  generalize c0X X u (Y.FN u) = a at ha hA ⊢
  generalize c0X X u' (Y.FN u') = b at hb hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u = m at hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' = m' at hA ⊢
  generalize X.volK2 = V at hA hV ⊢
  clear hkap
  rw [Complex.normSq_ofReal]
  rcases (mul_nonneg ha hb).eq_or_lt with h0 | h0
  · rw [← h0, Real.sqrt_zero, inv_zero, zero_mul, mul_zero, div_zero]
    have h1 : V ^ 2 * (m * m') = 0 := by rw [← hA, mul_assoc, ← h0, mul_zero]
    exact ((mul_eq_zero.mp h1).resolve_left (pow_pos hV 2).ne').symm
  · have hs : (√(a * b)) ^ 2 = a * b := Real.sq_sqrt h0.le
    have hs0 : √(a * b) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
    have hden : (√(a * b))⁻¹ * V * ((√(a * b))⁻¹ * V) = V ^ 2 / (a * b) := by
      first
        | rw [inv_mul_eq_div, div_mul_div_comm, ← sq, ← sq, hs]
        | (field_simp; rw [hs]; ring)
        | (field_simp; rw [Real.mul_self_sqrt h0.le]; ring)
    rw [hden, div_div_eq_mul_div, div_eq_iff (pow_pos hV 2).ne']
    linarith [hA]

theorem minWeight_pos (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2)
    (hc : 0 < Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') :
    0 < Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  exact hc

theorem K0_mem_covWin_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) {large₂} {C1 : ℝ}
    (hW : Formalism.L2.SG.LoopTerm.CovWinN (Y := Y) C large₂ C1 u u') :
    Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB) := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  first
    | exact hW
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; exact hW)
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; done)

end Main

end Formalism.L2.SG.Pf.AmpWin
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NGLeaves
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.NGLeaves

open Formalism.BasicNotions Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

theorem nondegenerate_gram_tuple : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 = PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

end Formalism.L2.SG.NGLeaves
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTTypes
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

def CapFromHC : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (u : Fin k → ℝ) (π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π → ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) →
    PI.UpqRep.IsHCTypeW k r z u π →
    Formalism.FourierDecayAlt.Q.CapParam k r z π (fun i => if h : i - 1 < k then u ⟨i - 1, h⟩ else 0)

section Block

variable {k r : ℕ}

theorem mvs {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem blockW_fix (h : Matrix (Fin k) (Fin k) ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ (r ≤ j.val ∧ j.val < r + k)) :
    Formalism.MainNotions.S.blockW k r h *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j := by
  funext i
  unfold Formalism.QuantumDeterminants.bvec
  rw [mvs]
  unfold Formalism.MainNotions.S.blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dite_eq_left hi, dite_eq_right hj, Pi.single_apply, if_neg]
    intro e; rw [e] at hi; exact hj hi
  · rw [dite_eq_right hi, Pi.single_apply]

theorem blockW_UH (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (Formalism.MainNotions.S.blockW k r h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.QuantumDeterminants.Hpk k r
  have hs : hᴴ * h = 1 := Matrix.mem_unitaryGroup_iff'.mp hh
  have e1 : (Formalism.MainNotions.S.blockW k r h)ᴴ = Formalism.MainNotions.S.blockW k r hᴴ := PI.HwUniqW.blockW_conjTranspose h
  have e2 : Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r h * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.Hpk_blockW_comm h
  have e3 : Formalism.MainNotions.S.blockW k r hᴴ * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r (hᴴ * h) :=
    PI.HwUniqW.blockW_mul hᴴ h
  have e4 : Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := PI.HwUniqW.blockW_one
  rw [e1, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, e3, hs, e4, Matrix.one_mul]

theorem conj_blockW_mem {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g) (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g * Formalism.MainNotions.S.blockW k r h * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨hgU, hge, hgz⟩ := hg
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hgU
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hgU
  have hinv : ∀ x, g *ᵥ x = x → g⁻¹ *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  have hfix : ∀ x, g *ᵥ x = x → Formalism.MainNotions.S.blockW k r h *ᵥ x = x → (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) *ᵥ x = x :=
    fun x h1 h2 => by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv x h1, h2, h1]
  refine ⟨PI.HwUniqW.mul_mem_UH (PI.HwUniqW.mul_mem_UH hgU (blockW_UH h hh)) (PI.HwUniqW.inv_mem_UH hgU),
    fun a => ⟨hfix _ (hge a).1 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.eI]; omega)),
      hfix _ (hge a).2 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.esI]; omega))⟩, ?_⟩
  have hx : ∀ x, g⁻¹ *ᵥ (g *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  rw [← hgz, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul,
    blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.wI, Fin.val_last]; omega)]

end Block

theorem isType_of_hc (hcap : CapFromHC) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)}
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hHC : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, ‖π h x‖ = ‖x‖) ∧ ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z))
    (w : ℕ → ℝ) (hw : ∀ i ∈ Finset.Icc 1 k, w i = if h : i - 1 < k then u ⟨i - 1, h⟩ else 0) :
    Formalism.FourierDecayAlt.Q.IsType k r z π w := by
  obtain ⟨g, hg, hU⟩ := hHC
  refine ⟨hU.1, hrep.1, hrep.2.2, hrep.2.1, fun S hS => ?_, ?_⟩
  · have hK := hU.2.2.2.2.2.1 S le_top (fun h hh v hv => hS _ (conj_blockW_mem hg h hh.1) v hv)
    exact hK
  · intro Bs hBs x v
    rw [hcap Wp k r z u π hz hT hrep.1 hrep.2.2 ⟨g, hg, hU⟩ Bs hBs x v]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by rw [hw i hi]

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorCR
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.LocF

section Gen

open Classical

variable {k r : ℕ}

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem uMat_toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : uMat (toUJn M hM) = M := rfl

theorem cond_tr {n : ℕ} {ε : Fin n → Bool} {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    (Q * m * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * m * Qi) = Formalism.REAL.Jm ε := by
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk k r * m = Formalism.QuantumDeterminants.Hpk k r := hm
  have hq := qiHqi ε h2 hg
  calc (Q * m * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * m * Qi) = Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * m) * Qi := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hg, hm', hq]

def wTg {n : ℕ} {ε : Fin n → Bool} {V : Type} [Zero V] (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (W : Formalism.REAL.UJ ε → V)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : V :=
  if h : ∃ γ : Formalism.REAL.UJ ε, uMat γ = Q * m * Qi then W h.choose else 0

theorem wTg_eq {n : ℕ} {ε : Fin n → Bool} {V : Type} [Zero V] {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (W : Formalism.REAL.UJ ε → V)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (γ : Formalism.REAL.UJ ε) (hγ : uMat γ = Q * m * Qi) :
    wTg Q Qi W m = W γ := by
  have hex : ∃ γ : Formalism.REAL.UJ ε, uMat γ = Q * m * Qi := ⟨γ, hγ⟩
  unfold wTg
  rw [dite_eq_left hex]
  congr 1
  apply Subtype.ext; apply Units.ext
  exact hex.choose_spec.trans hγ.symm

theorem continuousOn_wTg {n : ℕ} {ε : Fin n → Bool} {V : Type} [TopologicalSpace V] [Zero V]
    {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) {W : Formalism.REAL.UJ ε → V} (hW : Continuous W) :
    ContinuousOn (wTg Q Qi W) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  set G : Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → Formalism.REAL.UJ ε := fun p => toUJn (Q * p.1 * Qi) (cond_tr h2 hg p.2)
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · show Continuous fun p : Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) => Q * p.1 * Qi
      exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
    · show Continuous fun p : Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) =>
        Formalism.REAL.Jm ε * (Q * p.1 * Qi)ᴴ * Formalism.REAL.Jm ε
      exact (continuous_const.matrix_mul (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
        continuous_const).matrix_conjTranspose)).matrix_mul continuous_const
  have : (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)).domRestrict (wTg Q Qi W) = W ∘ G := by
    funext p
    show wTg Q Qi W p.1 = W (G p)
    exact wTg_eq W (G p) (uMat_toUJn _ _)
  rw [this]
  exact hW.comp hG

end Gen

section Rep

open Classical Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

theorem reprod_gen {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (W : Formalism.REAL.UJ ε → V)
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x) :
    ∀ x' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
        eFun ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) (fun M => σ (Q * M * Qi)) w
          (Matrix.of g) • wTg Q Qi W (x' * Matrix.of g))
        ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) ∧
      rconv ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ)))
        (eFun ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) (fun M => σ (Q * M * Qi)) w)
        (wTg Q Qi W) x' = wTg Q Qi W x' := by
  subst hn
  have hCP : CayPair ε Q Qi := ⟨hg, qi_eq rfl ε h2 hg⟩
  have hmap : (fun γ : Formalism.REAL.UJ ε => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ)) = cM Qi Q := rfl
  rw [hmap]
  intro x' hx'
  set x : Formalism.REAL.UJ ε := toUJn (Q * x' * Qi) (cond_tr h2 hg hx') with hxdef
  have hx'eq : (Matrix.of (cM Qi Q x) : Matrix _ _ ℂ) = x' := by
    show Qi * uMat x * Q = x'
    rw [uMat_toUJn]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hWc : ∀ γ : Formalism.REAL.UJ ε, wTg Q Qi W (Matrix.of (cM Qi Q γ)) = W γ := by
    intro γ
    refine wTg_eq W γ ?_
    show uMat γ = Q * (Qi * uMat γ * Q) * Qi
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  obtain ⟨hint, hval⟩ := hWr x
  have embG := cM_measEmb (ε := ε) (A := Qi) (B := Q) (A' := Q) (B' := Qi) h2 h2
  have hfd := fdegH_map hCP σ w
  have hσg : ∀ g : Formalism.REAL.UJ ε, σ (Q * (Matrix.of (cM Qi Q g) : Matrix _ _ ℂ) * Qi) = σ (uMat g) := by
    intro g
    show σ (Q * (Qi * uMat g * Q) * Qi) = σ (uMat g)
    congr 1; simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have hprod : ∀ g : Formalism.REAL.UJ ε, (Matrix.of (cM Qi Q x) : Matrix _ _ ℂ) * Matrix.of (cM Qi Q g) =
      Matrix.of (cM Qi Q (x * g)) := fun g => cMprod hCP _ x g
  have hpt : ∀ g : Formalism.REAL.UJ ε, eFun ((Formalism.REAL.muG ε).map (cM Qi Q)) (fun M => σ (Q * M * Qi)) w
      (Matrix.of (cM Qi Q g)) • wTg Q Qi W (x' * Matrix.of (cM Qi Q g)) =
      (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g) := by
    intro g
    simp only [eFun]
    rw [hfd, hσg, ← hx'eq, hprod, hWc]
  refine ⟨?_, ?_⟩
  · exact embG.integrable_map_iff.mpr (hint.congr (ae_of_all _ fun g => (hpt g).symm))
  · unfold rconv
    rw [embG.integral_map, integral_congr_ae (ae_of_all _ hpt), hval, ← hx'eq, hWc]

end Rep

section Steps

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem local_continuity_all : ContAll := by
  intro D X θ C u τ
  exact continuousOn_wTg (C.isT τ).2.1 (C.isT τ).2.2.1 (X.Wloc_cont u _)


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem local_reproduction_all : ReprodAll := by
  intro D hG X θ C u τ
  obtain ⟨μS, νl, Cc, hQ⟩ := Formalism.L2.SG.Pf.WuDec.quotAll_of Formalism.L2.SG.Closed.QuotProdK_holds
    Formalism.L2.SG.Pf.WFL.locHNProps_holds Formalism.L2.SG.Closed.NUnimodLoc_holds D X u
  have hR := Formalism.L2.SG.Pf.WuDec.locReprodStep_of Formalism.L2.SG.Pf.WuDec.local_scalar_reduction D hG X u μS νl Cc hQ (vOf X τ)
  exact reprod_gen (n_eq' X) (X.B.I.ε (vOf X τ)) (C.isT τ).1 (C.isT τ).2.1 (C.isT τ).2.2.1 (X.B.σ (vOf X τ))
    (X.B.w (vOf X τ)) (X.Wloc u (vOf X τ)) hR

end Steps

end Formalism.L2.SG.Pf.LocF
end
end
