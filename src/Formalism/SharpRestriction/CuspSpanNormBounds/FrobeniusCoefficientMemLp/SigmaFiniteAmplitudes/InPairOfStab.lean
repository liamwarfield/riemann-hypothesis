module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfUnfold
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.IntegralRankOneProd
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NormPiLeOne
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.MeasurableMulInvInv
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NormPsiOne
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.BesselIntg
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

section Defs

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp]

def aVec (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p1 : Mt k r × Mt k r) : Wp :=
  (psi k r z c (Matrix.of p1.2) * ⟪v, σ ((Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t) w0⟫_ℂ) •
    π (Matrix.of p1.1) ξ

end Defs

def Psi (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) (x : Mt k r) :
    L.Wq →L[ℂ] L.Wp :=
  (innerSL ℂ (aVec L.z' L.c L.π' L.σ w0 v' ξ' (Matrix.of x) p.2)).smulRight
    (aVec L.z L.c L.π L.σ w0 v ξ (γ * Matrix.of x) p.1)

def InPair (L : LocBessel k r) (p : PairSp k r) : Prop :=
  Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧
    Matrix.of p.2.2 ∈ Nset k r

theorem uh_of_uw {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h ∈ UH (Hpk k r) := hh.1

theorem uh_of_n {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    n ∈ UH (Hpk k r) := hn.1

theorem Psi_eq (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) (x : Mt k r) :
    Psi L w0 v v' ξ ξ' γ p x =
      ((psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2))) *
        (⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ *
          star ⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ)) •
        (innerSL ℂ (L.π' (Matrix.of p.2.1) ξ')).smulRight (L.π (Matrix.of p.1.1) ξ) := by
  ext η'
  simp only [Psi, aVec, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, _root_.smul_apply,
    inner_smul_left, starRingEnd_apply, star_mul', smul_smul, Matrix.mul_assoc]
  congr 1
  ring

theorem schur_step (L : LocBessel k r) {μG : Measure (Mt k r)}
    (hμG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) {d : ℝ} (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {p : PairSp k r} (hp : InPair L p) :
    Integrable (fun x => Psi L w0 v v' ξ ξ' γ p x) μG ∧
      ∫ x, Psi L w0 v v' ξ ξ' γ p x ∂μG =
        ((d : ℂ))⁻¹ • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hhU := uh_of_uw hh
  have hnU := uh_of_n hn
  have hh'U := uh_of_uw hh'
  have hn'U := uh_of_n hn'
  have hhi := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hhU
  have hni := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hnU
  have hh'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh'U
  have hn'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hn'U
  set A := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ with hA
  set B := (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ with hB
  set M := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 with hM
  have hAU : A ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhi hni) hγ
  have hBU : B ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hh'i hn'i
  have hMU : M ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hAU hn'U) hh'U
  have hMB : M * B = A := by
    rw [hM, hB, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.of p.2.1) (Matrix.of p.2.1)⁻¹, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hh'U).1,
      Matrix.one_mul, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hn'U).1, Matrix.mul_one]

  let F : Mt k r → ℂ := fun y => ⟪L.σ M⁻¹ v, L.σ (Matrix.of y) w0⟫_ℂ * star ⟪v', L.σ (Matrix.of y) w0⟫_ℂ
  obtain ⟨hFi, hFe⟩ := hSch w0 (L.σ M⁻¹ v) w0 v'
  have hFe' : ∫ y, F y ∂μG = ⟪v, L.σ M v'⟫_ℂ / (d : ℂ) := by
    show ∫ y, ⟪L.σ M⁻¹ v, L.σ (Matrix.of y) w0⟫_ℂ * star ⟪v', L.σ (Matrix.of y) w0⟫_ℂ ∂μG = _
    rw [hFe, hw1, one_mul, ← Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_inner hσ hMU v v']
  have hlm : Measurable (lmulM (k := k) (r := r) B) :=
    Formalism.FourierDecayAlt.P.B7.meas_mulM (f := fun _ => ((B : Matrix _ _ ℂ) : Mt k r)) measurable_const measurable_id
  have hmp : MeasurePreserving (lmulM (k := k) (r := r) B) μG μG := ⟨hlm, hμG.2.2.2 B hBU⟩
  have hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UH (Hpk k r) := Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_sk hμG
  have hfeq : ∀ᵐ x ∂μG, ⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ =
      F (lmulM B x) := by
    filter_upwards [hae] with x hx
    have hBx : B * Matrix.of x ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hBU hx
    have e1 : L.σ (A * Matrix.of x) = (L.σ M).comp (L.σ (B * Matrix.of x)) := by
      rw [← hMB, Matrix.mul_assoc]
      exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hMU hBx
    show _ = ⟪L.σ M⁻¹ v, L.σ (B * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ
    rw [e1, ContinuousLinearMap.comp_apply, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_inner hσ hMU]
  have hfi : Integrable (fun x : Mt k r =>
      ⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ) μG := by
    have h1 : Integrable (F ∘ lmulM B) μG := (hmp.integrable_comp hFi.aestronglyMeasurable).mpr hFi
    exact h1.congr (hfeq.mono fun x hx => hx.symm)
  have hfint : ∫ x, ⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪v, L.σ M v'⟫_ℂ / (d : ℂ) := by
    rw [integral_congr_ae hfeq, ← hFe']
    exact (integral_map hlm.aemeasurable (by rw [hmp.map_eq]; exact hFi.aestronglyMeasurable)).symm.trans
      (by rw [hmp.map_eq])

  set c : ℂ := psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2)) with hc
  set K : L.Wq →L[ℂ] L.Wp :=
    (innerSL ℂ (L.π' (Matrix.of p.2.1) ξ')).smulRight (L.π (Matrix.of p.1.1) ξ) with hK
  have hPsi : (fun x => Psi L w0 v v' ξ ξ' γ p x) = fun x : Mt k r =>
      (c * (⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ)) • K := by
    funext x
    rw [Psi_eq]
  refine ⟨?_, ?_⟩
  · rw [hPsi]
    exact (hfi.const_mul c).smul_const K
  · rw [hPsi, integral_smul_const, integral_const_mul, hfint]
    ext η'
    have hpi : ⟪ξ', L.π' (Matrix.of p.2.1)⁻¹ η'⟫_ℂ = ⟪L.π' (Matrix.of p.2.1) ξ', η'⟫_ℂ := by
      rw [Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_inner L.hz'.2 L.hπ' (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hh').1,
        Formalism.FourierDecayAlt.P.S3dx6.inv_inv_uh hh'U]
    simp only [hK, besselIntg, Formalism.MainNotions.S.Pv.AmpDD.coefF, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.map_smul, smul_smul, hpi]
    congr 1
    rw [← hM]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    ring

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem norm_psi_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ‖psi k r z c g‖ = 1 :=
  Formalism.FourierDecayAlt.P.S3dx6.norm_psi z c g

theorem norm_Psi_le (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {p : PairSp k r} (hp : InPair L p) (x : Mt k r) :
    ‖Psi L w0 v v' ξ ξ' γ p x‖ ≤ ‖ξ‖ * ‖ξ'‖ *
      (‖⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ‖ *
        ‖⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ‖) := by
  rw [Psi_eq, norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, norm_mul, norm_mul,
    norm_mul, norm_star, norm_star, norm_psi_one, norm_psi_one,
    Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz'.2 L.hπ' _ hp.2.2.1, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz.2 L.hπ _ hp.1]
  nlinarith [norm_nonneg ξ, norm_nonneg ξ',
    norm_nonneg ⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ,
    norm_nonneg ⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ]

theorem prod_coef_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (v v' w0 : H)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    {M y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : M ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r)) :
    ‖⟪v, σ (M * y) w0⟫_ℂ‖ * ‖⟪v', σ y w0⟫_ℂ‖ ≤
      (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b)) := by
  have hMy : M * y ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hM hy
  have hMi : M⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hM
  have h1 := hC1 _ hMy
  have h2 := hC2 _ hy
  have hn1 : 0 ≤ Formalism.FourierDecayAlt.B.gN (M * y) ^ (-a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _
  have hn2 : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (-a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _
  have hinv : Formalism.FourierDecayAlt.B.gN (M * y) = Formalism.FourierDecayAlt.B.gN (y⁻¹ * M⁻¹) := by
    rw [← Matrix.mul_inv_rev, ((hNI k r).2 _ hMy).1]
  have hconv := Formalism.FourierDecayAlt.P.S3dx6.conv_pt hNI hb hab hy hMi
  rw [((hNI k r).2 _ hM).1] at hconv
  calc ‖⟪v, σ (M * y) w0⟫_ℂ‖ * ‖⟪v', σ y w0⟫_ℂ‖
      ≤ (|C1| * Formalism.FourierDecayAlt.B.gN (M * y) ^ (-a)) * (|C2| * Formalism.FourierDecayAlt.B.gN y ^ (-a)) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn1))
          (h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn2)) (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) hn1)
    _ = (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (-a) * Formalism.FourierDecayAlt.B.gN (y⁻¹ * M⁻¹) ^ (-a)) := by
        rw [hinv]; ring
    _ ≤ (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b)) :=
        mul_le_mul_of_nonneg_left hconv (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem meas_gN_rpow (e : ℝ) : Measurable fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ e :=
  (Formalism.FourierDecayAlt.P.S3dx6.gN_mt_cont (k := k) (r := r)).measurable.pow_const e

theorem lint_G_bound (L : LocBessel k r) {μG : Measure (Mt k r)}
    (hμG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hI : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {p : PairSp k r} (hp : InPair L p) :
    ∫⁻ x, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ∂μG ≤
      ENNReal.ofReal (‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * (∫ x, Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a) ∂μG) *
        Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) := by
  have hp0 := hp
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hhU := uh_of_uw hh
  have hnU := uh_of_n hn
  have hh'U := uh_of_uw hh'
  have hn'U := uh_of_n hn'
  have hhi := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hhU
  have hni := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hnU
  have hh'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh'U
  have hn'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hn'U
  set A := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ with hA
  set B := (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ with hB
  set M := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 with hM
  have hAU : A ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhi hni) hγ
  have hBU : B ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hh'i hn'i
  have hMU : M ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hAU hn'U) hh'U
  have hMB : M * B = A := by
    rw [hM, hB, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.of p.2.1) (Matrix.of p.2.1)⁻¹, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hh'U).1,
      Matrix.one_mul, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hn'U).1, Matrix.mul_one]
  have hlm : Measurable (lmulM (k := k) (r := r) B) :=
    Formalism.FourierDecayAlt.P.B7.meas_mulM (f := fun _ => ((B : Matrix _ _ ℂ) : Mt k r)) measurable_const measurable_id
  have hmp : MeasurePreserving (lmulM (k := k) (r := r) B) μG μG := ⟨hlm, hμG.2.2.2 B hBU⟩
  set K1 : ℝ := ‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * Formalism.FourierDecayAlt.B.gN M ^ (-b) with hK1
  have hpt : ∀ᵐ x ∂μG, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ≤
      ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a)) := by
    filter_upwards [ae_mem_sk hμG] with x hx
    have hBx : B * Matrix.of x ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hBU hx
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have e1 : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x = M * (B * Matrix.of x) := by
      rw [← Matrix.mul_assoc, hMB]
    calc ‖Psi L w0 v v' ξ ξ' γ p x‖
        ≤ ‖ξ‖ * ‖ξ'‖ * (‖⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ‖ *
          ‖⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ‖) := norm_Psi_le L w0 v v' ξ ξ' γ hp0 x
      _ = ‖ξ‖ * ‖ξ'‖ * (‖⟪v, L.σ (M * (B * Matrix.of x)) w0⟫_ℂ‖ * ‖⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ‖) := by
          rw [e1]
      _ ≤ ‖ξ‖ * ‖ξ'‖ * ((|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN (B * Matrix.of x) ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b))) :=
          mul_le_mul_of_nonneg_left (prod_coef_le hNI hb hab v v' w0 hC1 hC2 hMU hBx)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a) := by
          rw [hK1]; show _ = _ * Formalism.FourierDecayAlt.B.gN (B * Matrix.of x) ^ (b - a); ring
  have hK1n : 0 ≤ K1 := by
    rw [hK1]
    have := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg M) (-b)
    positivity
  have hf : Measurable fun y : Mt k r => ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a)) :=
    ENNReal.measurable_ofReal.comp ((meas_gN_rpow (b - a)).const_mul K1)
  calc ∫⁻ x, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ∂μG
      ≤ ∫⁻ x, ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a)) ∂μG := lintegral_mono_ae hpt
    _ = ∫⁻ y, ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a)) ∂μG := by
        rw [← lintegral_map hf hlm, hmp.map_eq]
    _ = ENNReal.ofReal (∫ y, K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a) ∂μG) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hI.const_mul K1)]
        exact Filter.Eventually.of_forall fun y =>
          mul_nonneg hK1n (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _)
    _ = _ := by
        rw [integral_const_mul, hK1]
        unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj
        rw [← hM]
        ring_nf

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section Ext

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp]

def cM (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v w0 : H) : Mt k r → ℂ :=
  {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}.indicator fun g => ⟪v, σ (Matrix.of g) w0⟫_ℂ

def piV (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (ξ : Wp) : Mt k r → Wp :=
  {h : Mt k r | Matrix.of h ∈ UWset k r z}.indicator fun h => π (Matrix.of h) ξ

def aM (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    (t : Mt k r) (p1 : Mt k r × Mt k r) : Wp :=
  (psi k r z c (Matrix.of p1.2) *
      cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p1.1) (Formalism.FourierDecayAlt.P.B7.invM p1.2)) t)) •
    piV z π ξ p1.1

theorem meas_cM {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v w0 : H) : Measurable (cM (k := k) (r := r) σ v w0) := by
  have h1 : ContinuousOn (fun g : Mt k r => σ (Matrix.of g) w0) {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)} :=
    Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0
  exact Formalism.FourierDecayAlt.P.B7.meas_ind Formalism.FourierDecayAlt.P.B7.isClosed_GV.measurableSet (continuousOn_const.inner h1)

theorem sm_piV [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (ξ : Wp) :
    StronglyMeasurable (piV (k := k) (r := r) z π ξ) := by
  have h1 : ContinuousOn (fun h : Mt k r => π (Matrix.of h) ξ) {h : Mt k r | Matrix.of h ∈ UWset k r z} :=
    Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_cont hT hπ ξ
  exact Formalism.FourierDecayAlt.P.B7.sm_ind (Formalism.FourierDecayAlt.P.B7.isClosed_UW z).measurableSet h1

theorem measurable_mul_inv_inv {α : Type*} [MeasurableSpace α] {f g t : α → Mt k r} (hf : Measurable f)
    (hg : Measurable g) (ht : Measurable t) :
    Measurable fun a => Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM (f a))
      (Formalism.FourierDecayAlt.P.B7.invM (g a))) (t a) :=
  Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf)
    (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hg)) ht

theorem sm_aM [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {α : Type*} [MeasurableSpace α] {t : α → Mt k r} {p1 : α → Mt k r × Mt k r} (ht : Measurable t)
    (hp1 : Measurable p1) :
    StronglyMeasurable fun a => aM z c π σ w0 v ξ (t a) (p1 a) := by
  have hps : Measurable fun a => psi k r z c (Matrix.of (p1 a).2) :=
    (Formalism.FourierDecayAlt.P.S3dx6.continuous_psi z c).measurable.comp (measurable_snd.comp hp1)
  have hc : Measurable fun a => cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM
      (Formalism.FourierDecayAlt.P.B7.invM (p1 a).1) (Formalism.FourierDecayAlt.P.B7.invM (p1 a).2)) (t a)) :=
    (meas_cM hσ v w0).comp (measurable_mul_inv_inv (measurable_fst.comp hp1) (measurable_snd.comp hp1) ht)
  exact (hps.mul hc).stronglyMeasurable.smul ((sm_piV hT hπ ξ).comp_measurable (measurable_fst.comp hp1))

end Ext

def PsiM (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (q : PairSp k r × Mt k r) : L.Wq →L[ℂ] L.Wp :=
  (innerSL ℂ (aM L.z' L.c L.π' L.σ w0 v' ξ' q.2 q.1.2)).smulRight
    (aM L.z L.c L.π L.σ w0 v ξ (Formalism.FourierDecayAlt.P.B7.mulM (γ : Mt k r) q.2) q.1.1)

theorem continuous_rankOne {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    Continuous fun q : E × F => (innerSL ℂ q.1).smulRight q.2 :=
  (ContinuousLinearMap.smulRightL ℂ E F).continuous₂.comp
    (((innerSL ℂ (E := E)).continuous.comp continuous_fst).prodMk continuous_snd)

theorem sm_PsiM (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    StronglyMeasurable (PsiM L w0 v v' ξ ξ' γ) := by
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hb := sm_aM hσ L.hz'.2 L.hπ' L.c w0 v' ξ' (t := fun q : PairSp k r × Mt k r => q.2)
    (p1 := fun q : PairSp k r × Mt k r => q.1.2) measurable_snd (measurable_snd.comp measurable_fst)
  have ha := sm_aM hσ L.hz.2 L.hπ L.c w0 v ξ
    (t := fun q : PairSp k r × Mt k r => Formalism.FourierDecayAlt.P.B7.mulM (γ : Mt k r) q.2)
    (p1 := fun q : PairSp k r × Mt k r => q.1.1)
    (Formalism.FourierDecayAlt.P.B7.meas_mulM measurable_const measurable_snd) (measurable_fst.comp measurable_fst)
  exact continuous_rankOne.comp_stronglyMeasurable (hb.prodMk ha)

theorem PsiM_eq (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {p : PairSp k r} (hp : InPair L p) {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) :
    PsiM L w0 v v' ξ ξ' γ (p, x) = Psi L w0 v v' ξ ξ' γ p x := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have g1 : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (γ * Matrix.of x) ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_uw hh))
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_n hn))) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hγ hx)
  have g2 : (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_uw hh'))
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_n hn'))) hx
  have e1 : cM L.σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p.1.1)
      (Formalism.FourierDecayAlt.P.B7.invM p.1.2)) (Formalism.FourierDecayAlt.P.B7.mulM (γ : Mt k r) x)) =
      ⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (γ * Matrix.of x)) w0⟫_ℂ :=
    Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) g1 _
  have e2 : cM L.σ v' w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p.2.1)
      (Formalism.FourierDecayAlt.P.B7.invM p.2.2)) x) =
      ⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ :=
    Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) g2 _
  have e3 : piV L.z L.π ξ p.1.1 = L.π (Matrix.of p.1.1) ξ :=
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r L.z}) hh _
  have e4 : piV L.z' L.π' ξ' p.2.1 = L.π' (Matrix.of p.2.1) ξ' :=
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r L.z'}) hh' _
  simp only [PsiM, aM, Psi, aVec]
  rw [e1, e2, e3, e4]

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section OneSide

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem op_eq_sum (T : Wp →L[ℂ] Wp) :
    T = ∑ i, (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight (T ((stdOrthonormalBasis ℂ Wp) i)) := by
  ext x
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ Wp).sum_repr' x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]

def piOp (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (h : Mt k r) : Wp →L[ℂ] Wp :=
  ∑ i, (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight (piV z π ((stdOrthonormalBasis ℂ Wp) i) h)

theorem sm_piOp {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) : StronglyMeasurable (piOp (k := k) (r := r) z π) := by
  have hs := Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin (Module.finrank ℂ Wp)))
    (f := fun i (h : Mt k r) => (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight
      (piV z π ((stdOrthonormalBasis ℂ Wp) i) h))
    (fun i _ => (ContinuousLinearMap.smulRightL ℂ Wp Wp
      (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i))).continuous.comp_stronglyMeasurable (sm_piV hT hπ _))
  convert hs using 1
  funext h
  unfold piOp
  rw [Finset.sum_apply]

theorem piOp_eq (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) {h : Mt k r}
    (hh : Matrix.of h ∈ UWset k r z) : piOp z π h = π (Matrix.of h) := by
  rw [op_eq_sum (π (Matrix.of h))]
  unfold piOp
  congr 1
  funext i
  rw [show piV z π ((stdOrthonormalBasis ℂ Wp) i) h = π (Matrix.of h) ((stdOrthonormalBasis ℂ Wp) i) from
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r z}) hh _]

end OneSide

section Be

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem aVec_eq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p1 : Mt k r × Mt k r) :
    aVec z c π σ w0 v ξ t p1 = Formalism.FourierDecayAlt.P.S3dx6.aInt z c π σ w0 v t p1 ξ := rfl

theorem norm_pi_le_one {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : ‖π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h hh, one_mul]

theorem aesm_beInt {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    AEStronglyMeasurable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  let F : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
    (cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) * star (psi k r z c (Matrix.of p.2))) •
      piOp z π (Formalism.FourierDecayAlt.P.B7.invM p.1)
  have hF : StronglyMeasurable F := by
    have hc : Measurable fun p : Mt k r × Mt k r =>
        cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) :=
      (meas_cM hσ v w0).comp (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM measurable_fst measurable_snd)
        measurable_const)
    have hps : Measurable fun p : Mt k r × Mt k r => star (psi k r z c (Matrix.of p.2)) :=
      (continuous_star.comp (Formalism.FourierDecayAlt.P.S3dx6.continuous_psi z c)).measurable.comp measurable_snd
    exact (hc.mul hps).stronglyMeasurable.smul
      ((sm_piOp hT hπ).comp_measurable (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp measurable_fst))
  refine hF.aestronglyMeasurable.congr ?_
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h1', h2'] with p hp1 hp2
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hp1.1 hp2.1
  have hm : Matrix.of p.1 * Matrix.of p.2 * t ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhn ht
  have e1 : cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) =
      ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) (σ t w0)⟫_ℂ := by
    rw [show cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) =
      ⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * t) w0⟫_ℂ from
      Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) hm _]
    rw [hU.2.1 _ hhn _ ht]
    rfl
  have e2 : piOp z π (Formalism.FourierDecayAlt.P.B7.invM p.1) = π (Matrix.of p.1)⁻¹ :=
    piOp_eq z π (h := Formalism.FourierDecayAlt.P.B7.invM p.1) (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp1).1
  show F p = _
  simp only [F, e1, e2]
  rfl

variable [CompleteSpace Wp]

theorem int_beInt_of {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    (hξ : ξ ≠ 0) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μW μW)
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μN μN)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    (ha : Integrable (aVec z c π σ w0 v ξ t) (μW.prod μN)) :
    Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  have hι : MeasurePreserving (Prod.map (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) (μW.prod μN) := hιW.prod hιN
  have hae := aesm_beInt hσ hT hπ c w0 v ht h1 h2
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hcomp : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v ∘ Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) := by
    refine (ha.norm.div_const ‖ξ‖).mono' (hae.comp_measurePreserving hι) ?_
    filter_upwards [h1', h2'] with p hp1 hp2
    rw [Function.comp_apply, Formalism.FourierDecayAlt.P.S3dx6.aInt_eq hz c π hU w0 v ht hp1 hp2, aVec_eq]
    unfold Formalism.FourierDecayAlt.P.S3dx6.aInt
    rw [norm_smul, _root_.smul_apply, norm_smul,
      Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ _ hp1, le_div_iff₀ hξn]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (norm_pi_le_one hT hπ hp1))
      (norm_nonneg ξ)
  exact (hι.integrable_comp hae).mp hcomp

theorem int_a_eq {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μW μW)
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μN μN)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    (l : H → Wp)
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v = (innerSL ℂ (l v)).smulRight (l (σ t w0)))
    (hA : Integrable (aVec z c π σ w0 v ξ t) (μW.prod μN) ∨ ∀ᵐ p ∂(μW.prod μN), aVec z c π σ w0 v ξ t p = 0) :
    ∫ p, aVec z c π σ w0 v ξ t p ∂(μW.prod μN) = ⟪l v, ξ⟫_ℂ • l (σ t w0) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  have hι : MeasurePreserving (Prod.map (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) (μW.prod μN) := hιW.prod hιN
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  have hval : (Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v) ξ = ⟪l v, ξ⟫_ℂ • l (σ t w0) := by
    rw [hbe, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  by_cases hI : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN)
  · have e1 : (Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v) ξ =
        ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ ∂(μW.prod μN) :=
      ContinuousLinearMap.integral_apply hI ξ
    have hg : AEStronglyMeasurable (fun p => Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ)
        (Measure.map (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM) (μW.prod μN)) := by
      rw [hι.map_eq]; exact hI.aestronglyMeasurable.apply_continuousLinearMap ξ
    have e2 : ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ ∂(μW.prod μN) =
        ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM p) ξ
          ∂(μW.prod μN) := by
      rw [← integral_map hι.measurable.aemeasurable hg, hι.map_eq]
    have e3 : ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM p) ξ
          ∂(μW.prod μN) = ∫ p, aVec z c π σ w0 v ξ t p ∂(μW.prod μN) := by
      refine integral_congr_ae ?_
      filter_upwards [h1', h2'] with p hp1 hp2
      rw [Formalism.FourierDecayAlt.P.S3dx6.aInt_eq hz c π hU w0 v ht hp1 hp2, aVec_eq]
    rw [← e3, ← e2, ← e1, hval]
  · have hbe0 : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v = 0 := integral_undef hI
    rw [hbe0, _root_.zero_apply] at hval
    rw [← hval]
    rcases hA with hA | hA
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [aVec]
      · exact absurd (int_beInt_of hσ hz hT hπ c w0 v ξ hξ ht hιW hιN h1 h2 hA) hI
    · exact integral_eq_zero_of_ae hA

end Be

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section Gen

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem enorm_rankOne (w : E) (u : F) : ‖(innerSL ℂ w).smulRight u‖ₑ = ‖w‖ₑ * ‖u‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

theorem rankOne_smul (w : E) (u : F) (c d : ℂ) :
    (innerSL ℂ (d • w)).smulRight (c • u) = (c * star d) • (innerSL ℂ w).smulRight u := by
  ext η
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    _root_.smul_apply, inner_smul_left, smul_smul, starRingEnd_apply]
  congr 1
  ring

theorem integral_inner_left {f : α → E} (hf : Integrable f μ) (η : E) :
    ∫ x, ⟪f x, η⟫_ℂ ∂μ = ⟪∫ x, f x ∂μ, η⟫_ℂ := by
  have h1 : (fun x => ⟪f x, η⟫_ℂ) = fun x => (starRingEnd ℂ) ⟪η, f x⟫_ℂ := by
    funext x; rw [inner_conj_symm]
  rw [h1, integral_conj, integral_inner hf, inner_conj_symm]

theorem integral_rankOne_prod [SFinite μ] [SFinite ν] {a : α → F} {b : β → E} (ha : Integrable a μ)
    (hb : Integrable b ν) (hI : Integrable (fun q : α × β => (innerSL ℂ (b q.2)).smulRight (a q.1)) (μ.prod ν)) :
    ∫ q, (innerSL ℂ (b q.2)).smulRight (a q.1) ∂(μ.prod ν) = (innerSL ℂ (∫ y, b y ∂ν)).smulRight (∫ x, a x ∂μ) := by
  ext η
  rw [ContinuousLinearMap.integral_apply hI η]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hI' : Integrable (fun q : α × β => ⟪b q.2, η⟫_ℂ • a q.1) (μ.prod ν) := by
    simpa only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] using hI.apply_continuousLinearMap η
  rw [integral_prod (fun q : α × β => ⟪b q.2, η⟫_ℂ • a q.1) hI']
  simp only
  simp_rw [integral_smul_const]
  rw [integral_inner_left hb, integral_smul]

end Gen

section Pt

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp]

theorem aM_eq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) {p1 : Mt k r × Mt k r}
    (hp1 : Matrix.of p1.1 ∈ UWset k r z) (hp2 : Matrix.of p1.2 ∈ Nset k r) :
    aM z c π σ w0 v ξ (t : Mt k r) p1 = aVec z c π σ w0 v ξ t p1 := by
  have g : (Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp1.1)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp2.1)) ht
  have e1 : cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p1.1)
      (Formalism.FourierDecayAlt.P.B7.invM p1.2)) (t : Mt k r)) = ⟪v, σ ((Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t) w0⟫_ℂ :=
    Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) g _
  have e2 : piV z π ξ p1.1 = π (Matrix.of p1.1) ξ :=
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r z}) hp1 _
  simp only [aM, aVec]
  rw [e1, e2]

theorem aesm_aVec [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    AEStronglyMeasurable (aVec z c π σ w0 v ξ t) (μW.prod μN) := by
  have hs := sm_aM hσ hT hπ c w0 v ξ (t := fun _ : Mt k r × Mt k r => (t : Mt k r)) (p1 := id)
    measurable_const measurable_id
  refine hs.aestronglyMeasurable.congr ?_
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h1', h2'] with p hp1 hp2
  exact aM_eq z c π σ w0 v ξ ht hp1 hp2

end Pt

theorem rankOne_zero_right {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (w : E) : (innerSL ℂ w).smulRight (0 : F) = 0 := by
  ext η; simp

theorem rankOne_zero_left {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (u : F) : (innerSL ℂ (0 : E)).smulRight u = 0 := by
  ext η; simp

theorem pair_split (L : LocBessel k r) [SFinite L.μW] [SFinite L.μW'] [SFinite L.μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μW L.μW)
    (hιW' : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μW' L.μW')
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μN L.μN)
    (hW1 : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z) (hW1' : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z')
    (hN1 : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r)
    (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {x : Mt k r}
    (hx : Matrix.of x ∈ UH (Hpk k r)) (hγx : γ * Matrix.of x ∈ UH (Hpk k r))
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ (γ * Matrix.of x) w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ (γ * Matrix.of x) w0)))
    (hbe' : Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ (Matrix.of x) w0) v' =
      (innerSL ℂ (l' v')).smulRight (l' (L.σ (Matrix.of x) w0)))
    (hI : Integrable (fun p => Psi L w0 v v' ξ ξ' γ p x) (pairMeas L)) :
    ∫ p, Psi L w0 v v' ξ ξ' γ p x ∂(pairMeas L) =
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) := by
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  set a := aVec L.z L.c L.π L.σ w0 v ξ (γ * Matrix.of x) with ha_def
  set b := aVec L.z' L.c L.π' L.σ w0 v' ξ' (Matrix.of x) with hb_def
  have hPsi : (fun p => Psi L w0 v v' ξ ξ' γ p x) = fun q : PairSp k r => (innerSL ℂ (b q.2)).smulRight (a q.1) := rfl
  have hpm : pairMeas L = (L.μW.prod L.μN).prod (L.μW'.prod L.μN) := rfl
  have haS : AEStronglyMeasurable a (L.μW.prod L.μN) := aesm_aVec hσ L.hz.2 L.hπ L.c w0 v ξ hγx hW1 hN1
  have hbS : AEStronglyMeasurable b (L.μW'.prod L.μN) := aesm_aVec hσ L.hz'.2 L.hπ' L.c w0 v' ξ' hx hW1' hN1
  have ha_eq := fun hA => int_a_eq hσ L.hz.1 L.hz.2 L.hπ L.c w0 v ξ hγx hιW hιN hW1 hN1 l hbe hA
  have hb_eq := fun hB => int_a_eq hσ L.hz'.1 L.hz'.2 L.hπ' L.c w0 v' ξ' hx hιW' hιN hW1' hN1 l' hbe' hB
  have hRHS : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
      (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) =
      (innerSL ℂ (⟪l' v', ξ'⟫_ℂ • l' (L.σ (Matrix.of x) w0))).smulRight (⟪l v, ξ⟫_ℂ • l (L.σ (γ * Matrix.of x) w0)) := by
    rw [rankOne_smul]
    congr 2
    rw [← starRingEnd_apply, inner_conj_symm]
  rw [hRHS, hPsi, hpm]
  rw [hpm, hPsi] at hI
  have hprod : ∫⁻ q : PairSp k r, ‖(innerSL ℂ (b q.2)).smulRight (a q.1)‖ₑ ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)) =
      (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) * ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) := by
    simp_rw [enorm_rankOne, mul_comm (‖b _‖ₑ)]
    exact lintegral_prod_mul haS.enorm hbS.enorm
  have hfin : (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) * ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) < ⊤ := by
    rw [← hprod]; exact hI.2
  by_cases hA0 : ∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN) = 0
  · have hz : ∀ᵐ p ∂(L.μW.prod L.μN), a p = 0 :=
      ((lintegral_eq_zero_iff' haS.enorm).mp hA0).mono fun p hp => enorm_eq_zero.mp hp
    have e := ha_eq (Or.inr hz)
    rw [integral_eq_zero_of_ae hz] at e
    rw [← e, rankOne_zero_right]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hz] with q hq
    rw [hq, rankOne_zero_right]; rfl
  by_cases hB0 : ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) = 0
  · have hz : ∀ᵐ p ∂(L.μW'.prod L.μN), b p = 0 :=
      ((lintegral_eq_zero_iff' hbS.enorm).mp hB0).mono fun p hp => enorm_eq_zero.mp hp
    have e := hb_eq (Or.inr hz)
    rw [integral_eq_zero_of_ae hz] at e
    rw [← e, rankOne_zero_left]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hz] with q hq
    rw [hq, rankOne_zero_left]; rfl
  have hAB := ENNReal.mul_lt_top_iff.mp hfin
  have hlt : (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) < ⊤ ∧ (∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN)) < ⊤ := by
    rcases hAB with h | h | h
    · exact h
    · exact absurd h hA0
    · exact absurd h hB0
  have haI : Integrable a (L.μW.prod L.μN) := ⟨haS, hlt.1⟩
  have hbI : Integrable b (L.μW'.prod L.μN) := ⟨hbS, hlt.2⟩
  rw [integral_rankOne_prod haI hbI hI, ha_eq (Or.inl haI), hb_eq (Or.inl hbI)]

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem inPair_stab (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : PairSp k r} (hp : InPair L p) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) : InPair L (stabAct γ a p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact ⟨h1, WeylGroupFacts.mem_n_mul ha.1 h2, h3, WeylGroupFacts.mem_n_mul ha.2 h4⟩

theorem inPair_of_stab (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : PairSp k r} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (hp : InPair L (stabAct γ a p)) : InPair L p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have key : ∀ b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, b ∈ Nset k r →
      ∀ m : Mt k r, b * of m ∈ Nset k r → of m ∈ Nset k r := by
    intro b hb m hm
    have hu : IsUnit b.det := WeylGroupFacts.isUnit_of_uh hb.1
    have : of m = b⁻¹ * (b * of m) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [this]
    exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hb) hm
  exact ⟨h1, key a ha.1 _ h2, h3, key _ ha.2 _ h4⟩

private theorem psi_mul_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psi k r z c (g * h) = psi k r z c g * psi k r z c h := by
  unfold psi
  rw [WeylGroupFacts.ell_mul z hz ((WeylGroupFacts.nset_iff _).1 hg).2 ((WeylGroupFacts.nset_iff _).1 hh).2, mul_add,
    Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem psi_mul_star_psi_eq_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c g * star (psi k r z c g) = 1 := by
  have h : ‖psi k r z c g‖ = 1 := by
    unfold psi
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [show star (psi k r z c g) = (starRingEnd ℂ) (psi k r z c g) from rfl, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h]
  simp

theorem Psi_stab (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {p : PairSp k r} (hp : InPair L p) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (x : Mt k r) :
    Psi L w0 v v' ξ ξ' γ (stabAct γ a p) x =
      Psi L w0 v v' ξ ξ' γ p (Matrix.of.symm (γ⁻¹ * a⁻¹ * γ * Matrix.of x)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hγu : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hγ
  have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (of fun i j => M i j) = M :=
    fun M => rfl
  rw [Psi_eq, Psi_eq]
  simp only [stabAct, e, Equiv.apply_symm_apply]
  have m1 : (of p.1.1)⁻¹ * (a * of p.1.2)⁻¹ * γ * of x =
      (of p.1.1)⁻¹ * (of p.1.2)⁻¹ * γ * (γ⁻¹ * a⁻¹ * γ * of x) := by
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ γ⁻¹, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul]
  have m2 : (of p.2.1)⁻¹ * (γ⁻¹ * a * γ * of p.2.2)⁻¹ * of x =
      (of p.2.1)⁻¹ * (of p.2.2)⁻¹ * (γ⁻¹ * a⁻¹ * γ * of x) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hγu]
    simp only [Matrix.mul_assoc]
  have hc : psi k r L.z L.c (a * of p.1.2) * star (psi k r L.z' L.c (γ⁻¹ * a * γ * of p.2.2)) =
      psi k r L.z L.c (of p.1.2) * star (psi k r L.z' L.c (of p.2.2)) := by
    rw [psi_mul_of_mem_Nset L.z L.hz.1 L.c ha.1 h2, psi_mul_of_mem_Nset L.z' L.hz'.1 L.c ha.2 h4, star_mul',
      hrel a ha]
    calc psi k r L.z' L.c (γ⁻¹ * a * γ) * psi k r L.z L.c (of p.1.2) *
          (star (psi k r L.z' L.c (γ⁻¹ * a * γ)) * star (psi k r L.z' L.c (of p.2.2)))
        = (psi k r L.z' L.c (γ⁻¹ * a * γ) * star (psi k r L.z' L.c (γ⁻¹ * a * γ))) *
          (psi k r L.z L.c (of p.1.2) * star (psi k r L.z' L.c (of p.2.2))) := by ring
      _ = _ := by rw [psi_mul_star_psi_eq_one, one_mul]
  rw [m1, m2, hc]

end Formalism.MainNotions.S.Pv.AmpDDPf
