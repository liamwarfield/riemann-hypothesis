module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r ℂ ℂ where
  z := D.z
  z' := D.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := D.μG
  μW := D.μW
  μN := D.μN
  μW' := D.μW'
  μsec := D.μsec
  χ := D.χ
  k_pos := D.k_pos
  z_mem := D.z_mem
  z'_mem := D.z'_mem
  T_pos := D.T_pos
  T'_pos := D.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := D.haarG
  haarW := D.haarW
  haarN := D.haarN
  haarW' := D.haarW'
  sec := D.sec
  χ_smooth := D.χ_smooth
  χ_supp := D.χ_supp
  χ_int := D.χ_int

theorem hpk_eq (k r : ℕ) : PI.UpqRep.Hpk k r = Formalism.QuantumDeterminants.Hpk k r := rfl

theorem sigma_contOn {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPunit⟩, hDS⟩ := hσ
  have hc := hDS.2.2.1.2.2 v
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hmaps : Set.MapsTo (fun g : Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by
    intro g hg
    show (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹) = PI.UpqRep.Jm ε
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hJ : (P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ = PI.UpqRep.Jm ε := by
      rw [← hpk_eq, ← hPJ]
      have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
      have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
      calc (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹
          = ((P⁻¹)ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
        _ = PI.UpqRep.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    have hPPh : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * gᴴ * Pᴴ * ((P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹) * (P * g * P⁻¹) := by
          rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pᴴ (P⁻¹)ᴴ, hPPh, Matrix.one_mul]
          rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
      _ = PI.UpqRep.Jm ε := by rw [hg', hJ]
  have hcont : Continuous (fun g : Mx k r => P * g * P⁻¹) := by fun_prop
  have := hc.comp hcont.continuousOn hmaps
  refine this.congr ?_
  intro g _
  show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.mul_one]

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def Ann (P : M.Par) : Set ℂ := {ζ : ℂ | P.TT < Complex.normSq ζ}

def fnZ (P : M.Par) (f : ℂ → ℂ) : MA.SmQ P.r P.TT := MA.toSm P (fun q => f q.1.2)

def dzQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzP).1 f

def dzbQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzbP).1 f

def modA (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * star ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))

def modB (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))

def ConnF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P),
    trR P Bs e (d.L.nab.1 Φ) ρ = dzQ P (trR P Bs e Φ ρ) + fnZ P (A ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e (d.L.nabs.1 Φ) ρ = -dzbQ P (trR P Bs e Φ ρ) + fnZ P (B ρ) * trR P Bs e Φ ρ

def SmAB (P : M.Par) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A ρ) (Ann P) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B ρ) (Ann P)

def PhaseEq (P : M.Par) (A B u : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 ∧
    A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ = modA P ρ ζ ∧ B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ = modB P ρ ζ

end preds

def GTCLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ A B : M.Ty P → ℂ → ℂ, SmAB P A B ∧ ConnF P Bs d e A B

def GTCReal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)

def GTCCurv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0

def GTCHol : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A ρ w) 0 R).im = Real.pi * n

def GTCAnnulus : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ), 0 ≤ TT → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (NF.dZb α ζ).re = 0) →
    (∀ R : ℝ, 0 < R → TT < R ^ 2 → ∃ n : ℤ, (circleIntegral α 0 R).im = Real.pi * n) →
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = α ζ ∧ star (u ζ) * NF.dZb u ζ = -star (α ζ)

def GTCGauge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B u : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → PhaseEq P A B u →
        IsFrameB P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) ∧ KapF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) ∧
          NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ)

def GTCTT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → 0 ≤ P.TT

def GTCPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∃ u, PhaseEq P A B u

theorem modA_smooth (P : M.Par) (ρ : M.Ty P) (hTT : 0 ≤ P.TT) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'

theorem star_modA (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : star (modA P ρ ζ) = modB P ρ ζ := by
  simp only [modA, modB]
  first
  | (rw [star_div₀, star_mul', star_sub, star_star]; simp [Complex.conj_ofReal]; done)
  | (simp [map_div₀, Complex.conj_ofReal]; done)
  | (rw [star_div₀, star_mul', star_sub, star_star]
     simp only [Complex.star_def, Complex.conj_ofReal]; done)

def GTCPhaseOfCut : Prop := GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTCTT → GTCPhase

theorem gTCPhase_of_cut : GTCPhaseOfCut := by
  intro hR hC hH hA hT Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn
  have hTT := hT Wp Wq P Bs X d hyp
  have hex : ∀ ρ : M.Ty P, ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | P.TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = modA P ρ ζ - A ρ ζ ∧
          star (u ζ) * NF.dZb u ζ = -star (modA P ρ ζ - A ρ ζ) := by
    intro ρ
    refine hA P.TT (fun w => modA P ρ w - A ρ w) hTT ((modA_smooth P ρ hTT).sub (hAB ρ).1) ?_ ?_
    · intro ζ hζ
      exact hC Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
    · intro R hR0 hR2
      exact hH Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR2
  choose u hu using hex
  refine ⟨u, fun ρ => ⟨(hu ρ).1, fun ζ hζ => ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := (hu ρ).2 ζ hζ
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]; ring
  · rw [h3, hR Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ, star_sub, star_modA]; ring

def GTConnOfCut : Prop := GTCLocal → GTCPhase → GTCGauge → GTConn

theorem gTConn_of_cut : GTConnOfCut := by
  intro hL hP hG Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk
  obtain ⟨A, B', hAB, hC⟩ := hL Wp Wq P Bs X d hH e he hk
  obtain ⟨u, hu⟩ := hP Wp Wq P Bs X d hH e he hk A B' hAB hC
  exact ⟨_, hG Wp Wq P Bs X d hH e he hk A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

open scoped ContDiff

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jdh_ckOn_of_contDiff {k r : ℕ} {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {f : B.Mat k r → E'}
    (hf : ContDiff ℝ ∞ f) (UU : Set (B.Mat k r)) : B.CkOn ⊤ UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩

theorem jdh_opOrder_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o : ℕ) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ Tm ∈ Θ, Tm.word.length ≤ o) : B.opOrder Θ ≤ o := by
  unfold B.opOrder
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (List.mem_cons_self ..)) (ih fun Tm hTm => h Tm (List.mem_cons_of_mem _ hTm))

theorem jdh_pd_star {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) :
    U.IsPolyDeg κ (fun g => star (P g)) := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  · show star (P g) = _
    rw [he g, MvPolynomial.eval_rename, MvPolynomial.eval_map]
    show (starRingEnd ℂ) (MvPolynomial.eval₂ (RingHom.id ℂ) _ q) = _
    rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem polynomial_decay_admissible : JDPolyOK := by
  intro k r Wp Wq _ _ _ _ _ o κ Θ hΘ
  let Lm : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
  have hLm : ∀ c : ℂ, Lm c = c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun c => by
    simp [Lm]

  have key : ∀ Tm ∈ Θ, ∃ P : B.Mat k r → ℂ, U.IsPolyDeg κ P ∧ ContDiff ℝ ∞ P ∧
      Tm.coef = (fun g => Lm (P g)) ∧ Tm.coefAdj = (fun g => Lm (star (P g))) := by
    intro Tm hTm
    obtain ⟨-, P, hP, hc, ha⟩ := hΘ Tm hTm
    exact ⟨P, hP, (poly_adm (n := 0) hP).1, funext fun g => by rw [hc g, hLm],
      funext fun g => by rw [ha g, hLm]⟩
  have smooth : ∀ Tm ∈ Θ, ContDiff ℝ ∞ Tm.coef ∧ ContDiff ℝ ∞ Tm.coefAdj := by
    intro Tm hTm
    obtain ⟨P, -, hc, e1, e2⟩ := key Tm hTm
    refine ⟨?_, ?_⟩
    · rw [e1]; exact (Lm.restrictScalars ℝ).contDiff.comp hc
    · rw [e2]
      have hs : ContDiff ℝ ∞ (fun g => star (P g)) := by
        have := (Complex.conjCLE.contDiff (n := ∞)).comp hc
        simpa [Function.comp_def, Complex.conjCLE_apply] using this
      exact (Lm.restrictScalars ℝ).contDiff.comp hs
  refine ⟨fun UU Tm hTm => ⟨jdh_ckOn_of_contDiff (smooth Tm hTm).1 UU, jdh_ckOn_of_contDiff (smooth Tm hTm).2 UU⟩,
    fun d hd Tm hTm => ⟨jdh_ckOn_of_contDiff (smooth Tm hTm).1 _, jdh_ckOn_of_contDiff (smooth Tm hTm).2 _,
      fun m => ?_⟩, jdh_opOrder_le o Θ fun Tm hTm => (hΘ Tm hTm).1⟩
  obtain ⟨P, hP, -, e1, e2⟩ := key Tm hTm
  obtain ⟨⟨C, hC0, hUB⟩, -⟩ :=
    ubl_clm (Lm.restrictScalars ℝ) (subset_refl (GV k r)) (ubl_poly hP (GV k r) (subset_refl _) m 0)
  obtain ⟨⟨C', hC0', hUB'⟩, -⟩ :=
    ubl_clm (Lm.restrictScalars ℝ) (subset_refl (GV k r)) (ubl_poly (jdh_pd_star hP) (GV k r) (subset_refl _) m 0)
  refine ⟨max C C', fun u w hu hw hl g hg => ?_⟩
  have hg1 : 1 ≤ gN g := gN_ge_one hg
  have hpow : gN g ^ κ ≤ gN g ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hd0 : 0 ≤ gN g ^ d := Real.rpow_nonneg (by linarith) _
  constructor
  · rw [e1, dLR_eq]
    have hb := hUB (wL u ++ wR w) ⟨u, w, hu, hw, hl, rfl⟩ g hg
    simp only [zero_mul, add_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0))
  · rw [e2, dLR_eq]
    have hb := hUB' (wL u ++ wR w) ⟨u, w, hu, hw, hl, rfl⟩ g hg
    simp only [zero_mul, add_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC0').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd0))

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi
namespace Formalism.FourierDecayAlt.P

theorem exists_auxiliary_xi : Formalism.FourierDecayAlt.B.XiExists := ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GenTransferKapCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def KapPt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) : Prop :=
  (∀ ρ σ, (Qr ρ).comp (Qr σ) = if ρ = σ then Qr ρ else 0) ∧ (∑ ρ, Qr ρ = 1) ∧
  (∀ ρ (v w : Wq), inner ℂ (Qr ρ v) w = inner ℂ v (Qr ρ w)) ∧
  ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT),
    (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (∑ ρ, f ρ • Qr ρ)

end preds

def GTKPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr

def GTKLine : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ ρ : M.Ty P,
      ∃ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, E.comp (Qr ρ) = E ∧
        inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) ∧
        ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Z.comp (Qr ρ) = Z →
          Z = inner ℂ (B.hsVec E) (B.hsVec Z) • E

def GTKapOfCut : Prop := GTKPt → GTKLine → GTKap

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableGerm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section germ

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem deriv_const_smul_any (c : ℂ) (h : ℝ → E') (t : ℝ) :
    deriv (fun s => c • h s) t = c • deriv h t := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hd : DifferentiableAt ℝ h t
  · exact deriv_const_smul c hd
  · have hd' : ¬ DifferentiableAt ℝ (fun s => c • h s) t := by
      intro h'
      apply hd
      have e : h = fun s => c⁻¹ • (c • h s) := by
        funext s
        simp [smul_smul, inv_mul_cancel₀ hc]
      rw [e]
      exact h'.const_smul c⁻¹
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', smul_zero]

theorem rdV_smul (X : B.Mat k r) (c : ℂ) (f : B.Mat k r → E') :
    RdV X (c • f) = c • RdV X f := by
  funext g
  exact deriv_const_smul_any c (fun t => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

theorem rw_smul (w : List (B.Mat k r)) (c : ℂ) (f : B.Mat k r → E') :
    B.Rw w (c • f) = c • B.Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (B.Rw w (c • f)) = c • RdV X (B.Rw w f)
    rw [ih, rdV_smul]

theorem rdV_local {X : B.Mat k r} (hX : B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) {g : B.Mat k r} (hg : g ∈ U)
    (hgG : g ∈ B.GV k r) : RdV X f g = RdV X f' g := by
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hev] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem rw_local (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG

theorem sum_map_smul' {ι M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (l : List ι) (φ : ι → M) :
    (l.map fun i => c • φ i).sum = c • (l.map φ).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, smul_add]

end germ

theorem germ_operators_holds : GermOps := by
  intro k r Wp Wq _ _ _ _ _ Θ
  refine ⟨fun U f f' hU he g hg hgG => ⟨?_, ?_⟩, fun c f g => ⟨?_, ?_⟩⟩
  · unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word T.word_lie hU he g hg hgG]
  · unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hU
      (f := fun x => T.coefAdj x (f x)) (f' := fun x => T.coefAdj x (f' x))
      (fun x hx hxG => by simp only [he x hx hxG]) g hg hgG]
  · unfold B.opApply
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_smul, Pi.smul_apply, map_smul]
  · unfold B.opAdj
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    have e : (fun x => T.coefAdj x ((c • f) x)) = c • (fun x => T.coefAdj x (f x)) := by
      funext x; simp
    rw [e, rw_smul, Pi.smul_apply, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdOfLargeConstant
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem xi_eq_xiTau_one_one {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    JF.xiP D p = B.xiTau D (1, 1) p := by
  have hs : ∀ x : ℝ, star (Complex.exp (Complex.I * (x : ℂ))) = Complex.exp (-(Complex.I * (x : ℂ))) := by
    intro x
    show (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ))) = _
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  simp only [JF.xiP, B.xiTau, psi, B.lam, hs]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jAFFStable_of_parts (hG : GermOps) (hE : ExtLoc) (hS : SmoothOps) (hA : AdjComm) (hQ : EquivOps)
    (hO : OmPDom) : JAFFStable := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v Θ hΘ J hJ
  obtain ⟨hDom, hPos⟩ := hO E Wp Wq S T v
  have hG' := hG S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Θ
  have hsupp : ∀ f' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), tsupport f' ⊆ OmP S T v →
      B.SuppIn (B.GPos (T v).base) f' := by
    intro f' hs x hx
    have hxG : x ∈ B.GV S.G.k S.G.r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := S.G.k) (r := S.G.r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f' := closure_mono (by exact fun y hy => hy.2) hx
    exact hPos x (hs hxT) hxG
  constructor
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opApply Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).1) (fun c f₁ g _ => (hG'.2 c f₁ g).1)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).1) ?_ J hJ
    intro f₁ hf _ _ p hp g hg hgG
    exact hΘ.2 p hp f₁ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hf) g (hPos g hg hgG)
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opAdj Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).2) (fun c f₁ g _ => (hG'.2 c f₁ g).2)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).2) ?_ J hJ
    intro f₁ hf hc hs p hp g hg hgG
    exact hA _ _ _ _ (T v).base Θ hΘ.1 hΘ.2 f₁ hf hc (hsupp f₁ hs) p hp g (hPos g hg hgG)

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormPos
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def rrC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ :=
  fun v ε i w P Q =>
    ((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P * D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
      D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ) *
      (p v).RR (F v ε) i w (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q)

def setC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : C.HidaSetting E Wp Wq :=
  KB.withRR S (rrC S p F)

end defs

def FormPos : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x ε, 0 < ε →
    (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → 0 ≤ p.form j hj w x x

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def FundG : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A A' : B.Mat k r → (Wq →L[ℂ] Wp)), ContinuousOn A (B.GV k r) → ContinuousOn A' (B.GV k r) →
    (∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ → B.SuppIn (B.GPos D) φ →
      ∫ x : Mt k r, B.hsInner (A (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
        ∫ x : Mt k r, B.hsInner (A' (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG) →
    ∀ g ∈ B.GPos D, A g = A' g

def AdjCont : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ContinuousOn (B.opAdj Θ (B.rho D p f)) (B.GV k r) ∧
        ContinuousOn (B.rho D p (B.opAdj Θ f)) (B.GV k r)

def AdjInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ →
        B.SuppIn (B.GPos D) φ →
        ∫ x : Mt k r, B.hsInner (B.opAdj Θ (B.rho D p f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
          ∫ x : Mt k r, B.hsInner (B.rho D p (B.opAdj Θ f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG

theorem adjComm_of_parts (hF : FundG) (hC : AdjCont) (hI : AdjInt) : AdjComm := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp g hg
  obtain ⟨c1, c2⟩ := hC k r Wp Wq D Θ hs f hf hfc hfs p hp
  exact hF k r Wp Wq D _ _ c1 c2 (fun φ h1 h2 h3 => hI k r Wp Wq D Θ hs hc f hf hfc hfs p hp φ h1 h2 h3) g hg

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OmpCofLPd
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.TLC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem omp_adj_pd (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg r (fun g => star (adjugate (Zhat k r z z' g) a b)) := by
  have e : (fun g => star (adjugate (Zhat k r z z' g) a b)) = fun g =>
      (fun _ => ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ)))) g *
        (((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ).det := by
    funext g
    rw [adjugate_fin_succ_eq_det_submatrix, star_mul', det_conjTranspose, star_pow, star_neg, star_one]
  rw [e]
  have := pd_mul (pd_const (N := 2 * r + k + 1) ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ))) 0)
    (pd_det (l := r) (fun g => ((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ) fun c d => by
      simpa [conjTranspose_apply] using zhat_star_pd k r z z' _ _)
  simpa using this

theorem omp_cofL_pd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg r (fun g => D.cofL Bs g s) := by
  unfold D.cofL
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega) (pd_mul (omp_adj_pd Bs.z Bs.z' (Fin.last r) a) (pd_const _ 0))

theorem omp_inv_pd (q s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (Hpk k r * gᴴ * Hpk k r) q s) := by
  simp only [Matrix.mul_apply, conjTranspose_apply]
  refine pd_sum _ fun u _ => pd_mono (show 1 + 0 ≤ 1 by omega) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun t _ => pd_mono (show 0 + 1 ≤ 1 by omega) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem omp_poly {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (j : Fin k) :
    U.IsPolyDeg (r + 1) (fun g => omC Bs B0 g j) := by
  unfold omC herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun i _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun q _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (omp_inv_pd q s) (omp_cofL_pd Bs s))

end Formalism.FourierDecayAlt.P.TLC
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermFibreKernels
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propG

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eventually_ne_cocompact (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by
  filter_upwards [(isCompact_singleton : IsCompact ({c} : Set ℂ)).compl_mem_cocompact] with x hx
  simpa using hx

theorem eventually_rate_cocompact (σ : ℂ) (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in cocompact ℂ, C * ‖x + σ‖⁻¹ ≤ δ := by
  have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h := h0.eventually_ge_atTop (‖σ‖ + |C| / δ + 1)
  filter_upwards [h] with x hx
  have h1 : |C| / δ + 1 ≤ ‖x + σ‖ := by
    have := norm_sub_norm_le x (-σ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < ‖x + σ‖ := lt_of_lt_of_le (by positivity) h1
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  have h2 : |C| = δ * (|C| / δ) := by
    first
    | (field_simp; ring)
    | field_simp
  calc C ≤ |C| := le_abs_self C
    _ = δ * (|C| / δ) := h2
    _ ≤ δ * ‖x + σ‖ := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        linarith

theorem integral_sq_sub_le {μ : Measure ℂ} {u a : ℂ → H} {ab : ℂ → ℝ} (hu : MemLp u 2 μ) (ha : MemLp a 2 μ)
    (hab : MemLp ab 2 μ) (hd : ∀ᵐ D ∂μ, ‖a D‖ ≤ ab D) :
    ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
  have i1 : Integrable (fun D => ‖u D - a D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.sub ha).aestronglyMeasurable).1 (hu.sub ha)
  have i2 : Integrable (fun D => ‖u D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have i3 : Integrable (fun D => ab D ^ 2) μ := (memLp_two_iff_integrable_sq hab.aestronglyMeasurable).1 hab
  calc ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ ∫ D, (2 * ‖u D‖ ^ 2 + 2 * ab D ^ 2) ∂μ := by
        refine integral_mono_ae i1 ((i2.const_mul 2).add (i3.const_mul 2)) ?_
        filter_upwards [hd] with D hD
        have h1 : ‖u D - a D‖ ≤ ‖u D‖ + ‖a D‖ := norm_sub_le _ _
        have h2 : 0 ≤ ‖a D‖ := norm_nonneg _
        have h3 : 0 ≤ ‖u D - a D‖ := norm_nonneg _
        have e1 : ‖u D - a D‖ ^ 2 ≤ (‖u D‖ + ‖a D‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
        have e2 : ‖a D‖ ^ 2 ≤ ab D ^ 2 := pow_le_pow_left₀ h2 hD 2
        nlinarith [sq_nonneg (‖u D‖ - ‖a D‖)]
    _ = 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]

variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}

end propG

end

end Formalism.FourierDecayAlt.P.PBK
end
