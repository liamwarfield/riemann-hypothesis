module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqAna
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqVanish
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, (Y.tO u u).vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u →L[ℂ] X.Vpi u),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u w)) Set.univ (X.Wu u) (X.Wu u)
                (Formalism.L2.SG.RealObj.gamW X u u w)).comp B)

theorem stepTermVanishG_of_form (h : FormGC) : StepTermVanishG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dite_eq_left hex] at hJ
  have hJw : Jw Y u u ν hex.choose = 0 :=
    Formalism.L2.SG.NGVanish.hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u →L[ℂ] X.Vpi u)
      (B : X.Vpi u →L[ℂ] X.Vpi u), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

end Formalism.L2.SG.Pf.MainEqVanish
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClassHolds
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass

namespace Formalism.L2.SG.Pf

theorem liftIotaEqC_holds : LiftIotaEqC :=
  fun _ _ Y u _ s₁ s₂ _ _ _ _ hr =>
    Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (lam_eq Y u hr) (lam'_eq Y u hr) (congrArg (fun r => r.2.2) hr)

theorem stepClassG_holds : StepClassG := stepClassG_of_liftIota liftIotaEqC_holds

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem rep_at_pt (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    ∃ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), Gval (lf D (X.Fu u)) F' ≠ 0 ∧
      IsInCell (ZhatOM (Zhat (X.Fu u) F'.fl)) (Formalism.L2.SG.PairVal.ptOf t.toTerm) ∧
      ∃ n ∈ SRat (lf D (X.Fu u)), ∃ m ∈ SRat (lf D (X.Fu u')),
        ∀ a, F'.fl.fvec a = (n * t.lin * m) ((X.Fu u').fvec a) := by
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hcell⟩ := at_ptOf Y t hG
  refine ⟨F', hGv, hcell, ?_⟩
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨F', hP⟩ := hmk.symm
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hrow _ _).1 hmk'
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hrel
  refine ⟨n, NLam_SRat hn, t.lin⁻¹ * m * t.lin, NLam_transport Y t hm, fun a => ?_⟩
  have := hfr a
  show F'.fl.fvec a = n (t.lin (t.lin.symm (m (t.lin ((X.Fu u').fvec a)))))
  rw [LinearEquiv.apply_symm_apply]
  rw [← frame_fvec Y t a]
  exact this

theorem ptdc_core (t1 t2 : TauC Y u u') (hN1 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t1))
    (hp : ptPN t1 = ptPN t2) :
    ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s' := by
  have hN2 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t2) := by rw [← hp]; exact hN1
  obtain ⟨F1, hG1, hc1, n1, hn1, m1, hm1, hF1⟩ := rep_at_pt Y t1 hN1
  obtain ⟨F2, hG2, hc2, n2, hn2, m2, hm2, hF2⟩ := rep_at_pt Y t2 hN2
  have hw : Formalism.L2.SG.PairVal.ptOf t1.toTerm = Formalism.L2.SG.PairVal.ptOf t2.toTerm := toPts_inj _ _ hp
  rw [hw] at hc1
  obtain ⟨g, hg, ⟨M, hM, hgM⟩, U, hU, hgU⟩ := same_cell (X.Fu u) F1.fl F2.fl hG1 hG2 _ hc1 hc2

  have hgs : g.symm ∈ SRat (lf D (X.Fu u)) := by
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u) (g.symm : (VS D).V →ₗ[D.host.E] (VS D).V) M hM hgM
    exact ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hg, hf, hz⟩
  have hgS : g ∈ SRat (lf D (X.Fu u)) := by simpa using SRat_inv (lf D (X.Fu u)) hgs
  set ρ1 := n1 * t1.lin * m1 with hρ1
  set ρ2 := n2 * t2.lin * m2 with hρ2
  set s'' := ρ2⁻¹ * g * ρ1 with hs''
  have hs''v : ∀ b, s''.symm ((X.Fu u').fvec b) = ∑ c, U c b • (X.Fu u').fvec c := by
    intro b
    apply s''.injective
    rw [LinearEquiv.apply_symm_apply, hs'']
    show (X.Fu u').fvec b = ρ2.symm (g (ρ1 (∑ c, U c b • (X.Fu u').fvec c)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
    have e1 : ∀ c, ρ1 ((X.Fu u').fvec c) = F1.fl.fvec c := fun c => (hF1 c).symm
    simp only [e1]
    rw [hgU b, hF2 b]
    simp
  have hs''S : s'' ∈ SRat (lf D (X.Fu u')) := by
    have hs''i : s'' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
      refine (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem ?_) hg) ?_
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn2.1 t2.rep.2.2.1) hm2.1
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn1.1 t1.rep.2.2.1) hm1.1
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u') (s''.symm : (VS D).V →ₗ[D.host.E] (VS D).V) U hU hs''v
    have : s''.symm ∈ SRat (lf D (X.Fu u')) := ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hs''i, hf, hz⟩
    simpa using SRat_inv (lf D (X.Fu u')) this
  refine ⟨n2⁻¹ * g * n1, SRat_mul _ (SRat_mul _ (SRat_inv _ hn2) hgS) hn1,
    m1 * s''⁻¹ * m2⁻¹, SRat_mul _ (SRat_mul _ hm1 (SRat_inv _ hs''S)) (SRat_inv _ hm2), ?_⟩
  have e : ρ2 = g * ρ1 * s''⁻¹ := by rw [hs'']; group
  rw [hρ2, hρ1] at e
  calc t2.lin = n2⁻¹ * (n2 * t2.lin * m2) * m2⁻¹ := by group
    _ = n2⁻¹ * (g * (n1 * t1.lin * m1) * s''⁻¹) * m2⁻¹ := by rw [e]
    _ = n2⁻¹ * g * n1 * t1.lin * (m1 * s''⁻¹ * m2⁻¹) := by group

theorem NmlPtDC_holds : NmlPtDC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ γ hγ t1 t2 _ _ h1 h2 _ => ?_⟩
  subst h1
  exact ptdc_core Y t1 t2 hγ h2.symm

theorem NmlSep_holds : NmlSep := nmlSep_of NmlPtDC_holds normalsLemmaG3_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqLoc
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalInputLeG {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : PN.LocalNG Cl Nu, L.Basic ∧ ZAt L C1 r ∧
    L.MassRatioAt C0 r ∧ L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = weightedGenericAmplitudeSq L x.1 x.2) ∧ N.Hh γ = L.Htot ∧
    0 < L.ngenTot ∧ L.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ

theorem localInputG_of_le {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) (h : LocalInputLeG X N C1 C0 AAre)
    (hng : ∀ γ, N.ngen γ = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ) : LocalInputG X N C1 C0 := by
  intro γ hγ S
  obtain ⟨L, hB, hZ, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ / L.ngenTot := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    rw [hc, le_div_iff₀ hpos, one_mul]
    exact hle
  have hV0 : 0 ≤ L.V0 := hB.2.2.2.2.2.1
  refine ⟨{ L with V0 := L.V0 * c }, ?_, hZ, hM, ?_, ?_, hH, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB
    unfold Formalism.FourierDecayAlt.PN.LocalNG.Basic
    exact ⟨h1, h2, h3, h4, h5, mul_nonneg h6 (by linarith), h7⟩
  · intro d S' hS'
    have h0 := hU d S' hS'
    have hw : 0 ≤ L.V0 * ∏ p, L.wt p (d p) :=
      mul_nonneg hV0 (Finset.prod_nonneg fun p _ => hB.1 p (d p))
    calc ∑ x ∈ S', L.rw x.1 ≤ L.V0 * ∏ p, L.wt p (d p) := h0
      _ ≤ L.V0 * c * ∏ p, L.wt p (d p) := by nlinarith
  · intro x hx
    rw [ha x hx]
    first
      | rfl
      | (unfold Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq Formalism.L2.SG.Pf.MainEqCut.ampGen; rfl)
      | (cases hd : L.dat x.1 x.2 <;> simp [Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq, Formalism.L2.SG.Pf.MainEqCut.ampGen, hd])
  · show N.ngen γ = L.V0 * c * ∏ p, L.ngen p
    rw [hng γ]
    have e : L.ngenTot = L.V0 * ∏ p, L.ngen p := rfl
    have hne : L.ngenTot ≠ 0 := hpos.ne'
    rw [show L.V0 * c * ∏ p, L.ngen p = L.ngenTot * c by rw [e]; ring, hc, mul_div_assoc',
      mul_div_cancel_left₀ _ hne]

def StepLocPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLeG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

end Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqLoc

theorem stepLocGenPinnedG_of_loc (h : StepLocPinnedG) : StepLocGenPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, H⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  obtain ⟨s, hs1, hs2, hs3, hloc⟩ :=
    H C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  let AAre : ℝ := PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA
  let N0 := NOfG Y u (sc s ν) ν (fun _ => 0)
  let ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => AAre * 2 * N0.Hh γ ^ PN.eN D.R.rS * N0.n γ
  refine ⟨s, ng, 2, hs1, hs2, hs3, by norm_num, le_refl _, ?_, ?_⟩
  · exact localInputG_of_le _ _ C1 C0n AAre hloc (fun γ => rfl)
  · intro γ _
    refine ⟨?_, le_refl _⟩
    change 0 ≤ Formalism.L2.SG.RowsConc.nPt _ _ _ γ
    unfold Formalism.L2.SG.RowsConc.nPt
    apply Finset.prod_nonneg
    intro w _
    apply mul_nonneg
    · exact pow_nonneg (mul_nonneg (inv_nonneg.2 (Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _))
        (w.1.nonneg _)) _
    · apply Finset.prod_nonneg
      intro a _
      exact Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _

end Formalism.L2.SG.Pf
end
end
