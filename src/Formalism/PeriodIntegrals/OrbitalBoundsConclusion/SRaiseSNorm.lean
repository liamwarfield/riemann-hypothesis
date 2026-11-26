module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.ConstantOneMemNonvanishing
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

noncomputable section

def c1 (r : ℕ) : Fin r → ℂ := fun _ => 1

theorem constant_one_mem_nonvanishing (r : ℕ) : c1 r ∈ OmX r := fun _ => one_ne_zero

def AtCSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → Gauge.GC.CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π : M.Ty P,
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ X0 ∈ Line P Bs Pr π ζ,
      ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = X0 ∧
        ‖B.hsVec ((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
            (NF.muZ P.k P.r Bs.μsec ζ))‖ ^ 2 = M.Nrm P l π * ‖B.hsVec X0‖ ^ 2 ∧
        ∀ ρ : M.Ty P, M.Up P l π ρ →
          (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
            (NF.muZ P.k P.r Bs.μsec ζ) ∈ Line P Bs Pr ρ ζ

def LineMove : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (μ' : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (hμ' : IsSection P.k P.r Bs.z Bs.z' μ'),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → ∀ ζ ∈ Gauge.GC.Ann P, ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
    NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ' ζ * h' →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ σ : M.Ty P,
    ∀ Y ∈ Line P { Bs with μsec := μ', sec := hμ' } Pr σ ζ, (Bs.π h).comp (Y.comp (Bs.π' h')) ∈ Line P Bs Pr σ ζ

section aux

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem conj_back {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r Bs.z)
    (hh' : h' ∈ UWset k r Bs.z') (Y : Wq →L[ℂ] Wp) :
    (Bs.π h⁻¹).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' h'⁻¹)) = Y := by
  have hhi := LieBracketMultiplication.uw_inv hh
  have hh'i := LieBracketMultiplication.uw_inv hh'
  have e1 : (Bs.π h⁻¹).comp (Bs.π h) = 1 := by
    rw [← Bs.π_rep.2 _ hhi _ hh, NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
  have e2 : (Bs.π' h').comp (Bs.π' h'⁻¹) = 1 := by
    rw [← Bs.π'_rep.2 _ hh' _ hh'i, NFRadRedS.uw_mul_inv hh', Bs.π'_rep.1]
  ext v
  have k1 := DFunLike.congr_fun e1 (Y (Bs.π' h' (Bs.π' h'⁻¹ v)))
  have k2 := DFunLike.congr_fun e2 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at k1 k2 ⊢
  rw [k1, k2]

theorem conj_fwd {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r Bs.z)
    (hh' : h' ∈ UWset k r Bs.z') (Y : Wq →L[ℂ] Wp) :
    (Bs.π h).comp (((Bs.π h⁻¹).comp (Y.comp (Bs.π' h'⁻¹))).comp (Bs.π' h')) = Y := by
  have hhi := LieBracketMultiplication.uw_inv hh
  have hh'i := LieBracketMultiplication.uw_inv hh'
  have e1 : (Bs.π h).comp (Bs.π h⁻¹) = 1 := by
    rw [← Bs.π_rep.2 _ hh _ hhi, NFRadRedS.uw_mul_inv hh, Bs.π_rep.1]
  have e2 : (Bs.π' h'⁻¹).comp (Bs.π' h') = 1 := by
    rw [← Bs.π'_rep.2 _ hh'i _ hh', NFRadRedS.uw_inv_mul hh', Bs.π'_rep.1]
  ext v
  have k1 := DFunLike.congr_fun e1 (Y (Bs.π' h'⁻¹ (Bs.π' h' v)))
  have k2 := DFunLike.congr_fun e2 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at k1 k2 ⊢
  rw [k2] at k1
  rw [k2, k1]

end aux

theorem core (hC : AtCSec) (hM : LineMove) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hk : 2 ≤ P.k) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hA : ActHyp P Bs X d)
    (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) (S : ℂ → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)))
    (hS : IsSSPt P Bs d l S) (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp))
    (hPr : PRho.PRhoSpec P Bs.z Bs.π Pr) (π : M.Ty P) (ζ : ℂ) (hζ : ζ ∈ Gauge.GC.Ann P)
    (Xf : Wq →L[ℂ] Wp) (hXf : Xf ∈ Line P Bs Pr π ζ) :
    ‖B.hsVec (S ζ Xf)‖ ^ 2 = M.Nrm P l π * ‖B.hsVec Xf‖ ^ 2 ∧
      ∀ ρ : M.Ty P, M.Up P l π ρ → S ζ Xf ∈ Line P Bs Pr ρ ζ := by
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  have hq : ((c1 P.r, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
    ⟨constant_one_mem_nonvanishing P.r, by rw [hTz]; exact hζ⟩
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
  obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hcs0.1
    hdom.2.1 hdom.2.2
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hq.2] at he
  change NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' at he
  change ((c1 P.r, NF.muZ P.k P.r μ0 ζ) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' at hdom0
  have hhi := LieBracketMultiplication.uw_inv hh
  have hh'i := LieBracketMultiplication.uw_inv hh'
  have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
    rw [he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
      Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
  set X0 := (Bs.π h⁻¹).comp (Xf.comp (Bs.π' h'⁻¹)) with hX0def
  have hX0 : X0 ∈ Line P Bs0 Pr π ζ :=
    hM Wp Wq P Bs0 Bs.μsec Bs.sec hpl ζ hζ h⁻¹ hhi h'⁻¹ hh'i hback Pr hPr π Xf hXf
  obtain ⟨Φ, hΦ, hN, hL⟩ := hC Wp Wq P Bs0 hk hcs0 X d hA l hl Pr hPr π ζ hζ X0 hX0
  have hΦf : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = Xf := by
    rw [he, Φ.2.2.2 (c1 P.r, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh']
    change (Bs.π h).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs0.μsec ζ)).comp (Bs.π' h')) = Xf
    rw [hΦ, hX0def]
    exact conj_fwd Bs hh hh' Xf
  set Y0 := ((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
    (NF.muZ P.k P.r μ0 ζ)) with hY0def
  have hSv : S ζ Xf = (Bs.π h).comp (Y0.comp (Bs.π' h')) := by
    rw [← hΦf, ← hS Φ (c1 P.r) (constant_one_mem_nonvanishing P.r) ζ hζ, he]
    exact ((d.SS l).1 Φ).2.2.2 (c1 P.r, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
  have hnX : ‖B.hsVec X0‖ = ‖B.hsVec Xf‖ := Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_CinL Bs hhi hh' Xf
  have hnY : ‖B.hsVec Y0‖ = ‖B.hsVec (S ζ Xf)‖ := by
    have e : Y0 = Dx2.VV.CinL Bs h⁻¹ h' (S ζ Xf) := by
      rw [Dx2.VV.CinL_apply, hSv]
      exact (conj_back Bs hh hh' Y0).symm
    rw [e]
    exact Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_CinL Bs hhi hh' _
  refine ⟨?_, fun ρ hUp => ?_⟩
  · rw [← hnY, ← hnX]
    exact hN
  · rw [hSv]
    exact hM Wp Wq P Bs μ0 hcs0.1 hpl ζ hζ h hh h' hh' he Pr hPr ρ Y0 (hL ρ hUp)

theorem sRaise_of (hC : AtCSec) (hM : LineMove) : SRaise := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr π ρ hUp ζ hζ Xf hXf
  exact (core hC hM P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hXf).2 ρ hUp

theorem sNorm_of (hC : AtCSec) (hM : LineMove) : SNorm := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hXf
  exact (core hC hM P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hXf).1

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.LineMove
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

noncomputable section

theorem line_move_formula : LineMove := by
  intro Wp Wq _ _ _ _ _ _ P Bs μ' hμ' _hpl ζ _hζ h hh h' hh' he Pr hPr σ Y hY
  obtain ⟨hYF, hYP⟩ := hY
  have hhi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh
  have hh'i := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh'
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2, hpe⟩ := hp
    have hq1 : h⁻¹ * p.1 * h ∈ UWset P.k P.r Bs.z :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hhi hp1) hh
    have hq2 : h' * p.2 * h'⁻¹ ∈ UWset P.k P.r Bs.z' :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh' hp2) hh'i
    have hback : NF.muZ P.k P.r μ' ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
      rw [he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
        Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
    have hq : ((h⁻¹ * p.1 * h, h' * p.2 * h'⁻¹) : Q.Mx P.k P.r × Q.Mx P.k P.r) ∈
        NF.Stab P.k P.r Bs.z Bs.z' μ' ζ := by
      refine ⟨hq1, hq2, ?_⟩
      change h⁻¹ * p.1 * h * NF.muZ P.k P.r μ' ζ * (h' * p.2 * h'⁻¹) = NF.muZ P.k P.r μ' ζ
      have e : h⁻¹ * p.1 * h * NF.muZ P.k P.r μ' ζ * (h' * p.2 * h'⁻¹) =
          h⁻¹ * (p.1 * (h * NF.muZ P.k P.r μ' ζ * h') * p.2) * h'⁻¹ := by
        simp only [Matrix.mul_assoc]
      rw [e, ← he, hpe, ← hback]
    have key : (Bs.π (h⁻¹ * p.1 * h)).comp (Y.comp (Bs.π' (h' * p.2 * h'⁻¹))) = Y := hYF _ hq
    have e1 : (Bs.π p.1).comp (Bs.π h) = (Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h)) := by
      rw [← Bs.π_rep.2 _ hp1 _ hh, ← Bs.π_rep.2 _ hh _ hq1]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, Matrix.one_mul]
    have e2 : (Bs.π' h').comp (Bs.π' p.2) = (Bs.π' (h' * p.2 * h'⁻¹)).comp (Bs.π' h') := by
      rw [← Bs.π'_rep.2 _ hh' _ hp2, ← Bs.π'_rep.2 _ hq2 _ hh']
      congr 1
      rw [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', Matrix.mul_one]
    change (Bs.π p.1).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' p.2)) = (Bs.π h).comp (Y.comp (Bs.π' h'))
    calc (Bs.π p.1).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' p.2))
        = ((Bs.π p.1).comp (Bs.π h)).comp (Y.comp ((Bs.π' h').comp (Bs.π' p.2))) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = ((Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h))).comp (Y.comp ((Bs.π' (h' * p.2 * h'⁻¹)).comp (Bs.π' h'))) := by
          rw [e1, e2]
      _ = (Bs.π h).comp (((Bs.π (h⁻¹ * p.1 * h)).comp (Y.comp (Bs.π' (h' * p.2 * h'⁻¹)))).comp (Bs.π' h')) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (Y.comp (Bs.π' h')) := by rw [key]
  · set a := SSn.nu0 P.k P.r Bs.z Bs.z' μ' ζ with ha
    have hYP' : (Pr σ a).comp Y = Y := hYP
    have hν : SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = h *ᵥ a := by
      rw [ha]
      unfold SSn.nu0 SSn.unitH
      rw [he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh'.2.2,
        Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.TF.prWv_uw Bs.z_mem Bs.T_pos hh, Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1,
        Matrix.mulVec_smul]
    have e0 : (Bs.π h⁻¹).comp (Bs.π h) = 1 := by
      rw [← Bs.π_rep.2 _ hhi _ hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
    have e0' : ∀ T : Wq →L[ℂ] Wp, (Bs.π h⁻¹).comp ((Bs.π h).comp T) = T := by
      intro T
      ext v
      have k1 := DFunLike.congr_fun e0 (T v)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at k1 ⊢
      exact k1
    change (Pr σ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp ((Bs.π h).comp (Y.comp (Bs.π' h'))) =
      (Bs.π h).comp (Y.comp (Bs.π' h'))
    rw [hν, hPr.2.1 h hh σ a]
    calc ((Bs.π h).comp ((Pr σ a).comp (Bs.π h⁻¹))).comp ((Bs.π h).comp (Y.comp (Bs.π' h')))
        = (Bs.π h).comp ((Pr σ a).comp ((Bs.π h⁻¹).comp ((Bs.π h).comp (Y.comp (Bs.π' h'))))) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (((Pr σ a).comp Y).comp (Bs.π' h')) := by
          rw [e0' (Y.comp (Bs.π' h'))]; simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (Y.comp (Bs.π' h')) := by rw [hYP']

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.CrossSectionAtPoint
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.UpRelationSourceUnique
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

noncomputable section

theorem up_relation_source_unique {P : M.Par} {l : ℕ} {a b c : M.Ty P} (h1 : M.Up P l a b) (h2 : M.Up P l c b) : a = c := by
  funext i
  apply Fin.ext
  have e1 := h1 i
  have e2 := h2 i
  omega

theorem up_tgt {P : M.Par} {l : ℕ} {a b c : M.Ty P} (h1 : M.Up P l a b) (h2 : M.Up P l a c) : b = c := by
  funext i
  apply Fin.ext
  have e1 := h1 i
  have e2 := h2 i
  omega

section line

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem line_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) (σ : M.Ty P) (ζ : ℂ) (c : ℂ)
    {E : Wq →L[ℂ] Wp} (hE : E ∈ Line P Bs Pr σ ζ) : c • E ∈ Line P Bs Pr σ ζ := by
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hE.1 p hp]
  · rw [ContinuousLinearMap.comp_smul, hE.2]

theorem lineQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hH : Gauge.GC.GTHyp P Bs X d)
    (Qs : M.Ty P → (Wq →L[ℂ] Wq)) (hQ : Gauge.GC.KapPt P Bs d Qs)
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) (hPr : PRho.PRhoSpec P Bs.z Bs.π Pr)
    (ζ : ℂ) (hζ : ζ ∈ Gauge.GC.Ann P) (σ : M.Ty P) (E : Wq →L[ℂ] Wp)
    (hE : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) :
    E ∈ Line P Bs Pr σ ζ ↔ E.comp (Qs σ) = E := by
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hH.1
  have hk : 2 ≤ P.k := hH.2.1
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp

  have pass : ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z, ν] Fr →
      Q.IsFrameOf P.k P.r [μ⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => μ⁻¹ *ᵥ Fr a) ∧
      ∀ (w : ℂ) (v : Wq), Q.capRep P.k P.r Bs.π Fr w (E v) =
        E (qdet (Qr.EB Bs.π' (fun a => μ⁻¹ *ᵥ Fr a)) w v) := by
    intro Fr hFr
    obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
    have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
      (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
      (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
    refine ⟨hFr', fun w v => ?_⟩
    rw [hpass E hE, hgl']
  constructor
  · intro hL
    obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
    obtain ⟨hFr', hp⟩ := pass Fr hFr
    have hcap : Gauge.GC.CapEig P Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) σ E := by
      intro Yc v
      have hEv : Pr σ ν (E v) = E v := by
        have := DFunLike.congr_fun hL.2 v
        simpa only [ContinuousLinearMap.comp_apply] using this
      have hr := ((hPr.2.2 ν hpos).2.2.2 σ (E v)).1 hEv Fr (by rw [hνfix]; exact hFr)
        (Yc + ((P.k : ℂ) - 2) / 2)
      rw [hp] at hr
      have e : Yc + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Yc := by ring
      rw [e] at hr
      exact hr
    exact (Gauge.GC.lie_eigenvalue_holds Wp Wq P Bs X d hH Qs hQ ζ hζT _ hFr' σ E hE).2 hcap
  · intro hEQ
    refine ⟨hE, ?_⟩
    ext v
    show Pr σ ν (E v) = E v
    refine ((hPr.2.2 ν hpos).2.2.2 σ (E v)).2 fun Fr hFr w => ?_
    rw [hνfix] at hFr
    obtain ⟨hFr', hp⟩ := pass Fr hFr
    have hcap := (Gauge.GC.lie_eigenvalue_holds Wp Wq P Bs X d hH Qs hQ ζ hζT _ hFr' σ E hE).1 hEQ
    have h1 := hcap (w - ((P.k : ℂ) - 2) / 2) v
    rw [sub_add_cancel] at h1
    rw [hp, h1]

end line

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

theorem sum_ite_smul {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (σ : ι) (Q : ι → V) :
    (∑ ρ, (if ρ = σ then (1 : ℂ) else 0) • Q ρ) = Q σ := by
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cross_section_at_point : AtCSec := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk hcs X d hA l hl Pr hPr π ζ hζ X0 hX0
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := hA
  have hH : GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hS, hRel, hQQ⟩
  obtain ⟨e, he, hkF⟩ := gauge_kappa_holds Wp Wq P Bs X d hH
  obtain ⟨Qs, hQ⟩ := gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  obtain ⟨s, t, hst, hSL⟩ := gTSSLocal_of_radT radial_torus_local_holds Wp Wq P Bs X d hH e he hkF
  have hadj := second_shift_adjoint_pointwise Wp Wq P Bs X d hH e he hkF s t hst hSL l hl
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  have hζT : P.TT < Complex.normSq ζ := hζ

  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hq : ((c1 P.r, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨constant_one_mem_nonvanishing P.r, by rw [hTz]; exact hζ⟩
  have hΨ : ∀ ρ, (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ := by
    intro ρ
    have h := congrFun (hΨr ρ) (c1 P.r, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hval : ∀ Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro Z
    have hmem := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Z.2).2.1
      (c1 P.r, ζ) hq
    simpa only [NF.radR, Set.indicator_of_mem hq] using hmem
  have hexp := (he.2 ζ hζT).2.2
  have hδ : ∀ ρ σ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e σ ζ)) = if ρ = σ then (1 : ℂ) else 0 :=
    (he.2 ζ hζT).2.1
  let q : MA.Qp P.r P.TT := ⟨(c1 P.r, ζ), fun _ => one_ne_zero, hζT⟩
  set w : ℂ := ((wR P.k P.TT ζ : ℝ) : ℂ) with hwdef
  have hw : w ≠ 0 := wRc_ne P hζ
  have hraw : ∀ (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P), rawR P Bs.μsec e Z ρ q =
      w * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (Z (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ))) := fun Z ρ => rfl
  have hrawΨ : ∀ σ ρ, rawR P Bs.μsec e (Ψ σ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
      w * (if ρ = σ then (1 : ℂ) else 0) := by
    intro σ ρ
    rw [hraw, hΨ σ, hδ]
  have hmulapply : ∀ (A C : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      (A * C).1 Z = A.1 (C.1 Z) := fun A C Z => rfl

  have hκpt : ∀ (f : M.Ty P → ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      (((d.κ f).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
          (NF.muZ P.k P.r Bs.μsec ζ) =
        ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ)).comp (∑ ρ, f ρ • Qs ρ) :=
    fun f Z => hQ.2.2.2 f Z q

  have hK0 : ∀ σ, e σ ζ ∈ Line P Bs Pr σ ζ := by
    intro σ
    refine (lineQ P Bs X d hH Qs hQ Pr hPr ζ hζ σ (e σ ζ) ((he.2 ζ hζT).1 σ)).2 ?_
    have h1 := hκpt (fun ρ => if ρ = σ then (1 : ℂ) else 0) (Ψ σ)
    rw [sum_ite_smul, hΨ σ] at h1
    rw [← h1, hexp _ (hval _)]
    have hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((((d.κ (fun ρ => if ρ = σ then (1 : ℂ) else 0)).1 (Ψ σ) :
        Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ))) =
        if ρ = σ then (1 : ℂ) else 0 := by
      intro ρ
      have h2 := SSAdjH.kap_pt P Bs hpl hk e he d hkF (fun ρ => if ρ = σ then (1 : ℂ) else 0) (Ψ σ) ρ q
      rw [hraw, hrawΨ] at h2
      by_cases hρ : ρ = σ
      · rw [if_pos hρ] at h2 ⊢
        apply mul_left_cancel₀ hw
        rw [h2]; ring
      · rw [if_neg hρ] at h2 ⊢
        apply mul_left_cancel₀ hw
        rw [h2]; ring
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  set a : M.Ty P → ℂ := fun σ => inner ℂ (B.hsVec (e σ ζ)) (B.hsVec X0) with hadef
  let Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ∑ σ, a σ • Ψ σ
  have hsumv : ∀ (G : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      ((∑ ρ, G ρ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        ∑ ρ, (G ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g := by
    intro G c g
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  have hΦv : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = X0 := by
    rw [hsumv]
    conv_rhs => rw [hexp X0 hX0.1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hΨ σ]
  have hrawΦ : ∀ ρ, rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = w * a ρ := by
    intro ρ
    rw [hraw, hΦv]

  have hXQ : X0.comp (Qs π) = X0 := (lineQ P Bs X d hH Qs hQ Pr hPr ζ hζ π X0 hX0.1).1 hX0
  have hK1 : ∀ σ, σ ≠ π → a σ = 0 := by
    intro σ hσ
    have h1 := hκpt (fun ρ => if ρ = π then (1 : ℂ) else 0) Φ
    rw [sum_ite_smul, hΦv, hXQ] at h1
    have h2 := SSAdjH.kap_pt P Bs hpl hk e he d hkF (fun ρ => if ρ = π then (1 : ℂ) else 0) Φ σ q
    rw [hraw, h1, hrawΦ, if_neg hσ, zero_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left hw

  have hSSΨ : ∀ σ, rawR P Bs.μsec e ((((d.SS l).1 (Ψ π) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = s l σ π ζ * w := by
    intro σ
    rw [(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl (Ψ π) σ q).1]
    simp only [hrawΨ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

  have hK2 : ∀ ρ', ¬ M.Up P l π ρ' → s l ρ' π ζ = 0 := by
    intro ρ' hn
    have hcond : ∀ ρ ρ'', M.Up P l ρ ρ'' →
        (fun x => if M.Up P l π x then (1 : ℂ) else 0) ρ'' = (fun x => if x = π then (1 : ℂ) else 0) ρ := by
      intro ρ ρ'' hU
      dsimp only
      by_cases hρ : ρ = π
      · subst hρ
        rw [if_pos hU, if_pos rfl]
      · have hn2 : ¬ M.Up P l π ρ'' := fun h2 => hρ (up_relation_source_unique hU h2)
        rw [if_neg hn2, if_neg hρ]
    have heq := hRel.2.2.2.1 l _ _ hcond
    have hz := congrArg (fun A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => A.1 (Ψ π)) heq
    simp only [hmulapply] at hz
    have h3 := congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q) hz
    try dsimp only at h3
    rw [SSAdjH.kap_pt P Bs hpl hk e he d hkF, hSSΨ,
      (SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl _ ρ' q).1] at h3
    try dsimp only at h3
    rw [if_neg hn, zero_mul] at h3
    rw [Finset.sum_eq_single π (fun b _ hb => by
        rw [SSAdjH.kap_pt P Bs hpl hk e he d hkF, hrawΨ]; try dsimp only
        rw [if_neg hb]; ring)
      (fun h => absurd (Finset.mem_univ π) h)] at h3
    rw [SSAdjH.kap_pt P Bs hpl hk e he d hkF, hrawΨ] at h3
    try dsimp only at h3
    have h4 : s l ρ' π ζ * w = 0 := by
      have h5 : (0 : ℂ) = s l ρ' π ζ * ((if π = π then (1 : ℂ) else 0) * (w * if π = π then (1 : ℂ) else 0)) := h3
      rw [if_pos rfl] at h5
      linear_combination -h5
    exact (mul_eq_zero.1 h4).resolve_right hw

  have hK3 : ∑ σ, star (s l σ π ζ) * s l σ π ζ = ((M.Nrm P l π : ℝ) : ℂ) := by
    have heq := hRel.2.2.2.2.2 l hl
    have hz := congrArg (fun A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => A.1 (Ψ π)) heq
    simp only [hmulapply] at hz
    have h3 := congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) π q) hz
    try dsimp only at h3
    rw [(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl _ π q).2, SSAdjH.kap_pt P Bs hpl hk e he d hkF,
      hrawΨ] at h3
    try dsimp only at h3
    rw [if_pos rfl] at h3
    have h4 : ∀ σ, t l π σ q.1.2 * rawR P Bs.μsec e ((((d.SS l).1 (Ψ π) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = (star (s l σ π ζ) * s l σ π ζ) * w := by
      intro σ
      rw [hSSΨ σ, show t l π σ q.1.2 = star (s l σ π ζ) from hadj π σ ζ hζ]
      ring
    rw [Finset.sum_congr rfl (fun σ _ => h4 σ), ← Finset.sum_mul] at h3
    apply mul_right_cancel₀ hw
    rw [h3]
    ring

  have hY : ∀ ρ', rawR P Bs.μsec e ((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q = s l ρ' π ζ * (w * a π) := by
    intro ρ'
    rw [(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl Φ ρ' q).1, Finset.sum_eq_single π
      (fun b _ hb => by rw [hrawΦ, hK1 b hb]; ring) (fun h => absurd (Finset.mem_univ π) h), hrawΦ]
  set Y := (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
    (NF.muZ P.k P.r Bs.μsec ζ) with hYdef
  refine ⟨Φ, hΦv, ?_, fun ρ hUp => ?_⟩
  · have hp1 := SSAdjH.hs_pair P Bs hpl hk e he ((d.SS l).1 Φ) ((d.SS l).1 Φ) q
    simp only [hY] at hp1
    have hp2 := SSAdjH.hs_pair P Bs hpl hk e he Φ Φ q
    simp only [hrawΦ] at hp2
    rw [Finset.sum_eq_single π (fun b _ hb => by rw [hK1 b hb]; simp)
      (fun h => absurd (Finset.mem_univ π) h)] at hp2
    have hp2' : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0) = star (w * a π) * (w * a π) := by
      rw [← hΦv]
      exact hp2
    have hp1' : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec Y) (B.hsVec Y) =
        ∑ σ, star (s l σ π ζ * (w * a π)) * (s l σ π ζ * (w * a π)) := hp1
    have hsum1 : ∑ σ, star (s l σ π ζ * (w * a π)) * (s l σ π ζ * (w * a π)) =
        (star (w * a π) * (w * a π)) * ((M.Nrm P l π : ℝ) : ℂ) := by
      rw [← hK3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [star_mul']
      ring
    have hW2 : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have := SSTr.wR_pos P hζT
      exact_mod_cast (pow_pos this 2).ne'
    have key : inner ℂ (B.hsVec Y) (B.hsVec Y) = ((M.Nrm P l π : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0) := by
      apply mul_left_cancel₀ hW2
      rw [hp1', hsum1, show ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * (((M.Nrm P l π : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0)) =
        ((M.Nrm P l π : ℝ) : ℂ) * (((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0)) by ring, hp2']
      ring
    have k2 := congrArg Complex.re key
    rw [Complex.re_ofReal_mul] at k2
    show ‖B.hsVec Y‖ ^ 2 = M.Nrm P l π * ‖B.hsVec X0‖ ^ 2
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact k2
  · have hc0 : ∀ ρ', ρ' ≠ ρ → inner ℂ (B.hsVec (e ρ' ζ)) (B.hsVec Y) = 0 := by
      intro ρ' hne
      have hn : ¬ M.Up P l π ρ' := fun h2 => hne (up_tgt hUp h2).symm
      have h := hY ρ'
      rw [hraw, hK2 ρ' hn, zero_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hw
    have hYe : Y = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Y) • e ρ ζ := by
      conv_lhs => rw [hexp Y (hval _)]
      rw [Finset.sum_eq_single ρ (fun b _ hb => by rw [hc0 b hb, zero_smul])
        (fun h => absurd (Finset.mem_univ ρ) h)]
    show Y ∈ Line P Bs Pr ρ ζ
    rw [hYe]
    exact line_smul P Bs Pr ρ ζ _ (hK0 ρ)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

theorem s_raise_section : SRaise := SR.sRaise_of SR.cross_section_at_point SR.line_move_formula

theorem s_norm_section : SNorm := SR.sNorm_of SR.cross_section_at_point SR.line_move_formula

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
