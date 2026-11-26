module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UMatInvMul

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MemOmLoc
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SsetOfSloc
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurableSetNotUH
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasMulF
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {k r : ℕ}

def mulF (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem meas_mulF : Measurable (mulF (k := k) (r := r)) :=
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_mulP

theorem muS_eq (μW μN : Measure (Mt k r)) : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map mulF := rfl

theorem muS_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μW μN : Measure (Mt k r)}
    (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW) (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    (Formalism.MainNotions.S.muS μW μN).map Formalism.FourierDecayAlt.B2.invM = Formalism.MainNotions.S.muS μW μN := by
  have sW := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hW
  have sN := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hN
  have hinvm : Measurable (Formalism.FourierDecayAlt.B2.invM : Mt k r → Mt k r) := Formalism.FourierDecayAlt.P.B2x2.invM_meas
  have hWi : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hNi : μN.map Formalism.FourierDecayAlt.B2.invM = μN :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) μN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
  have hNc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN := Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN

  let g : Mt k r → Mt k r → Mt k r := fun h n => mulF (mulF (h, Formalism.FourierDecayAlt.B2.invM n), Formalism.FourierDecayAlt.B2.invM h)
  have hgm : Measurable (Function.uncurry g) :=
    meas_mulF.comp ((meas_mulF.comp (measurable_fst.prodMk (hinvm.comp measurable_snd))).prodMk
      (hinvm.comp measurable_fst))
  have hW0 : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.conc
  have hg : ∀ᵐ h ∂μW, μN.map (g h) = μN := by
    filter_upwards [hW0] with h hh
    have e : g h = conjM (Matrix.of h) ∘ Formalism.FourierDecayAlt.B2.invM := rfl
    rw [e, ← Measure.map_map (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_conj _) hinvm, hNi, hNc _ hh]
  have hmp : MeasurePreserving (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2))
      (μW.prod μN) (μW.prod μN) :=
    MeasurePreserving.skew_product (μb := μW) (μd := μN) ⟨hinvm, hWi⟩ hgm hg
  have hFm : Measurable (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) :=
    (hinvm.comp measurable_fst).prodMk hgm
  have hae : (Formalism.FourierDecayAlt.B2.invM ∘ mulF) =ᵐ[μW.prod μN]
      (mulF ∘ fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
      rw [ae_iff]
      have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
          {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
        ext p; simp
      rw [es, Measure.prod_prod]
      have : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0 := hW.conc
      rw [this, zero_mul]
    filter_upwards [h1] with p hp
    have hu : IsUnit (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det :=
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.det_unit_of_UH hp.1
    have hii : (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ * Matrix.of p.1 = 1 :=
      Matrix.nonsing_inv_mul _ hu
    show ((Matrix.of p.1 * Matrix.of p.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hii, Matrix.one_mul]
  rw [muS_eq, Measure.map_map hinvm meas_mulF, Measure.map_congr hae, ← Measure.map_map meas_mulF hFm, hmp.map_eq]

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def Tm (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)

private theorem muT_ne_zero (D : D7) : Formalism.L2.SG.LocWSOf.muT D ≠ 0 := by
  have hrd : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (half_pos hrd)
  have hg : (D.host.g 0 * D.host.g 1 : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hfr : Formalism.L2.SG.LocWSOf.frS D ≠ 0 := by
    unfold Formalism.L2.SG.LocWSOf.frS
    exact Complex.ofReal_ne_zero.mpr (div_pos hka (by positivity : (0:ℝ) < 2 * Real.pi)).ne'
  have hcf : Formalism.L2.SG.LocWSOf.cfS D ≠ 0 := by
    unfold Formalism.L2.SG.LocWSOf.cfS
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    refine div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero ?_)) hpi
    exact Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr hg)
  unfold Formalism.L2.SG.LocWSOf.muT
  exact div_ne_zero hcf hfr

private theorem torS_mul_torS_inv_eq_one {μ : ℂ} (hμ : μ ≠ 0) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS μ k r * Formalism.L2.SG.LocWSOf.torS μ⁻¹ k r = 1 := by
  unfold Formalism.L2.SG.LocWSOf.torS
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> first | (simp [hμ]; done) | (field_simp; done) | (simp [hμ, inv_pow, star_inv']; done)

private theorem torS_conjTranspose_mul_Hpk_mul_torS_eq_Hpk {μ : ℂ} (hμ : μ ≠ 0) (k r : ℕ) :
    (Formalism.L2.SG.LocWSOf.torS μ k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Formalism.L2.SG.LocWSOf.torS μ k r =
      Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Formalism.L2.SG.LocWSOf.torS, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.star_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> first
    | omega
    | (simp; done)
    | (rw [show 2 * r + k - (j : ℕ) = (i : ℕ) by omega]; simp [hμ]; done)
    | (rw [show 2 * r + k - (i : ℕ) = (j : ℕ) by omega]; simp [hμ]; done)
    | (simp [hμ]; done)

private theorem Qics_mul_Qcs_eq_one (C : Choice X θ) (τ : D.what₂.Tau) : Qics C τ * Qcs C τ = 1 := by
  have hT := C.isT τ
  unfold Formalism.L2.SG.LocWSOf.IsTranspC at hT
  obtain ⟨h1, -, -, -⟩ := hT
  have ht := torS_mul_torS_inv_eq_one (inv_ne_zero (muT_ne_zero D)) D.R.k D.R.rS
  rw [inv_inv] at ht
  unfold Formalism.L2.SG.LocWSOf.Qics Formalism.L2.SG.LocWSOf.Qcs
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.Qi τ), h1, Matrix.one_mul, ht]

private theorem Qcs_mul_Qics_eq_one (C : Choice X θ) (τ : D.what₂.Tau) : Qcs C τ * Qics C τ = 1 := by
  have hT := C.isT τ
  unfold Formalism.L2.SG.LocWSOf.IsTranspC at hT
  obtain ⟨-, h2, -, -⟩ := hT
  unfold Formalism.L2.SG.LocWSOf.Qics Formalism.L2.SG.LocWSOf.Qcs
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) D.R.k D.R.rS),
    torS_mul_torS_inv_eq_one (muT_ne_zero D), Matrix.one_mul, h2]

private theorem Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk (C : Choice X θ) (τ : D.what₂.Tau) :
    (Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
  have hT := C.isT τ
  unfold Formalism.L2.SG.LocWSOf.IsTranspC at hT
  obtain ⟨-, -, h3, -⟩ := hT
  unfold Formalism.L2.SG.LocWSOf.Qcs
  rw [Matrix.conjTranspose_mul]
  calc _ = (Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) D.R.k D.R.rS)ᴴ *
        ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) *
        Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) D.R.k D.R.rS := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h3, torS_conjTranspose_mul_Hpk_mul_torS_eq_Hpk (muT_ne_zero D)]

private theorem of_Tm_eq_Qics_mul_mul_Qcs (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Tm C τ x) = Qics C τ * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * Qcs C τ := rfl

private theorem Qics_mul_Qcs_conj_mul_conj_eq_conj_mul (C : Choice X θ) (τ : D.what₂.Tau) (U V : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    Qics C τ * U * Qcs C τ * (Qics C τ * V * Qcs C τ) = Qics C τ * (U * V) * Qcs C τ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Qcs C τ) (Qics C τ), Qcs_mul_Qics_eq_one, Matrix.one_mul]

private theorem Jm_mul_self_eq_one {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH (C : Choice X θ) (τ : D.what₂.Tau) (m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hm : Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
  have hm' : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  calc (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)
      = (Qics C τ)ᴴ * ((Matrix.of m)ᴴ * ((Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ) * Matrix.of m) * Qics C τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Qics C τ)ᴴ * ((Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ) * Qics C τ := by rw [Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ, hm']
    _ = (Qcs C τ * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Qics C τ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [Qcs_mul_Qics_eq_one C τ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

private theorem Qics_conj_conjTranspose_mul_form_mul_conj_eq (C : Choice X θ) (τ : D.what₂.Tau) (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    (Qics C τ * U * Qcs C τ)ᴴ * ((Qcs C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Qcs C τ) * (Qics C τ * U * Qcs C τ) =
      (Qcs C τ)ᴴ * (Uᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * U) * Qcs C τ := by
  calc _ = (Qcs C τ)ᴴ * (Uᴴ * ((Qcs C τ * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Qics C τ)) * U) * Qcs C τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Qcs_mul_Qics_eq_one C τ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

private theorem of_Tm_mem_UH_Hpk (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Tm C τ x) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hU : ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := x.2
  show (Matrix.of (Tm C τ x))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of (Tm C τ x) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  rw [of_Tm_eq_Qics_mul_mul_Qcs]
  conv_lhs => rw [← Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ]
  rw [Qics_conj_conjTranspose_mul_form_mul_conj_eq C τ, hU, Qcs_conjTranspose_mul_Jm_mul_Qcs_eq_Hpk C τ]

private theorem Qcs_mul_Qics_conj_mul_Qics_eq_self (C : Choice X θ) (τ : D.what₂.Tau) (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    Qcs C τ * (Qics C τ * A * Qcs C τ) * Qics C τ = A := by
  simp only [Matrix.mul_assoc]
  rw [Qcs_mul_Qics_eq_one, Matrix.mul_one, ← Matrix.mul_assoc, Qcs_mul_Qics_eq_one, Matrix.one_mul]

private theorem Qics_mul_Qcs_conj_mul_Qcs_eq_self (C : Choice X θ) (τ : D.what₂.Tau)
    (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    Qics C τ * (Qcs C τ * A * Qics C τ) * Qcs C τ = A := by
  simp only [Matrix.mul_assoc]
  rw [Qics_mul_Qcs_eq_one, Matrix.mul_one, ← Matrix.mul_assoc, Qics_mul_Qcs_eq_one, Matrix.one_mul]

private theorem mem_range_Tm_of_of_mem_UH (C : Choice X θ) (τ : D.what₂.Tau) {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hm : Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : m ∈ Set.range (Tm C τ) := by
  have hU := Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH C τ m hm
  have hl : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ) = 1 := by
    rw [show ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, A * Bᴴ * A * B = A * (Bᴴ * A * B) from fun A B => by
      simp only [Matrix.mul_assoc], hU, Jm_mul_self_eq_one]
  refine ⟨⟨⟨Qcs C τ * Matrix.of m * Qics C τ, Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)),
    (by first | exact Matrix.mul_eq_one_comm.mp (hl) | exact mul_eq_one_comm.mp (hl) | exact Matrix.mul_eq_one_symm (hl) | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hl)), hl⟩, hU⟩, ?_⟩
  apply Matrix.of.injective
  rw [of_Tm_eq_Qics_mul_mul_Qcs]
  exact Qics_mul_Qcs_conj_mul_Qcs_eq_self C τ (Matrix.of m)

private theorem isClosed_setOf_of_mem_UH_Hpk (k r : ℕ) :
    IsClosed {m : Formalism.QuantumDeterminants.Mt k r | Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : Continuous fun m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      mᴴ * Formalism.QuantumDeterminants.Hpk k r * m :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

theorem Tm_emb (C : Choice X θ) (τ : D.what₂.Tau) : MeasurableEmbedding (Tm C τ) := by
  haveI : BorelSpace (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) := ⟨rfl⟩
  have hcont : Continuous (Tm C τ) := by
    have h : Continuous fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => Qics C τ * ((x : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * Qcs C τ :=
      (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
        continuous_const
    exact h
  have hrange : Set.range (Tm C τ) = {m | Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} := by
    ext m
    constructor
    · rintro ⟨x, rfl⟩
      exact of_Tm_mem_UH_Hpk C τ x
    · intro hm
      exact mem_range_Tm_of_of_mem_UH C τ hm
  have hUJ : ∀ m : Set.range (Tm C τ), (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      (Qcs C τ * Matrix.of m.1 * Qics C τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    intro m
    apply Qcs_conj_conjTranspose_Jm_eq_Jm_of_mem_UH C τ
    obtain ⟨x, hx⟩ := m.2
    rw [← hx]
    exact of_Tm_mem_UH_Hpk C τ x
  have hl : ∀ m : Set.range (Tm C τ), Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      (Qcs C τ * Matrix.of m.1 * Qics C τ) = 1 := by
    intro m
    rw [show ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, A * Bᴴ * A * B = A * (Bᴴ * A * B) from fun A B => by
      simp only [Matrix.mul_assoc], hUJ m, Jm_mul_self_eq_one]
  let g : Set.range (Tm C τ) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := fun m =>
    ⟨⟨Qcs C τ * Matrix.of m.1 * Qics C τ, Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Qcs C τ * Matrix.of m.1 * Qics C τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)),
      (by first | exact Matrix.mul_eq_one_comm.mp (hl m) | exact mul_eq_one_comm.mp (hl m) | exact Matrix.mul_eq_one_symm (hl m) | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hl m)), hl m⟩, hUJ m⟩
  have hv : Continuous fun m : Set.range (Tm C τ) => Qcs C τ * Matrix.of m.1 * Qics C τ := by
    have h0 : Continuous fun m : Set.range (Tm C τ) => (Matrix.of m.1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
        (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) := continuous_subtype_val
    exact (continuous_const.matrix_mul h0).matrix_mul continuous_const
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact hv
    · exact (continuous_const.matrix_mul hv.matrix_conjTranspose).matrix_mul continuous_const
  refine MeasurableEmbedding.of_measurable_inverse_on_range hcont.measurable ?_ hg.measurable ?_
  · rw [hrange]
    exact (isClosed_setOf_of_mem_UH_Hpk D.R.k D.R.rS).measurableSet
  · intro x
    apply Subtype.ext
    apply Units.ext
    show Qcs C τ * Matrix.of (Tm C τ x) * Qics C τ = _
    rw [of_Tm_eq_Qics_mul_mul_Qcs]
    exact Qcs_mul_Qics_conj_mul_Qics_eq_self C τ _

theorem Tm_mul (C : Choice X θ) (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Tm C τ (a * b) = mulF (Tm C τ a, Tm C τ b) := by
  apply Matrix.of.injective
  show Matrix.of (Tm C τ (a * b)) = Matrix.of (Tm C τ a) * Matrix.of (Tm C τ b)
  rw [of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs, Qics_mul_Qcs_conj_mul_conj_eq_conj_mul]
  all_goals first | rfl | simp [Subgroup.coe_mul, Units.val_mul]

theorem Tm_inv (C : Choice X θ) (τ : D.what₂.Tau) (a : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Tm C τ a⁻¹ = Formalism.FourierDecayAlt.B2.invM (Tm C τ a) := by
  apply Matrix.of.injective
  show Matrix.of (Tm C τ a⁻¹) = (Matrix.of (Tm C τ a))⁻¹
  rw [of_Tm_eq_Qics_mul_mul_Qcs, of_Tm_eq_Qics_mul_mul_Qcs]
  symm
  apply Matrix.inv_eq_right_inv
  rw [Qics_mul_Qcs_conj_mul_conj_eq_conj_mul]
  simp only [Subgroup.coe_inv, Units.mul_inv, Matrix.mul_one, Qics_mul_Qcs_eq_one]

theorem Tm_mem (C : Choice X θ) (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Tm C τ x) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := of_Tm_mem_UH_Hpk C τ x

theorem mem_range_Tm (C : Choice X θ) (τ : D.what₂.Tau) {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hm : Matrix.of m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : m ∈ Set.range (Tm C τ) := mem_range_Tm_of_of_mem_UH C τ hm

theorem comap_lint (C : Choice X θ) (τ : D.what₂.Tau) {μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hμ : μ {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, F (Tm C τ x) ∂(μ.comap (Tm C τ)) = ∫⁻ m, F m ∂μ := by
  have hE := Tm_emb C τ
  have hae : ∀ᵐ m ∂μ, m ∈ Set.range (Tm C τ) := by
    rw [ae_iff]
    refine measure_mono_null (fun m hm => ?_) hμ
    simp only [Set.mem_setOf_eq] at hm ⊢
    exact fun h => hm (mem_range_Tm C τ h)
  rw [← hE.lintegral_map, hE.map_comap, Measure.restrict_eq_self_of_ae_mem hae]

theorem sigmaFinite_comap (C : Choice X θ) (τ : D.what₂.Tau) {μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    [SigmaFinite μ] (hμ : μ {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0) :
    SigmaFinite (μ.comap (Tm C τ)) := by
  have hE := Tm_emb C τ
  first
    | exact SigmaFinite.of_map _ hE.measurable.aemeasurable (by rw [hE.map_comap]; infer_instance)
    | infer_instance

theorem sFinite_comap (C : Choice X θ) (τ : D.what₂.Tau) {μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    [SFinite μ] : SFinite (μ.comap (Tm C τ)) := by
  have hE := Tm_emb C τ
  first
    | infer_instance
    | (have h : μ.comap (Tm C τ) = Measure.sum (fun n => (sfiniteSeq μ n).comap (Tm C τ)) := by
          ext s hs
          rw [hE.comap_apply, Measure.sum_apply _ hs]
          conv_lhs => rw [← sum_sfiniteSeq μ]
          rw [Measure.sum_apply _ (hE.measurableSet_image.mpr hs)]
          simp only [hE.comap_apply]
       haveI : ∀ n, IsFiniteMeasure ((sfiniteSeq μ n).comap (Tm C τ)) := fun n =>
         ⟨by rw [hE.comap_apply _ Set.univ]; exact measure_lt_top _ _⟩
       rw [h]
       infer_instance)

theorem measurableSet_notUH : MeasurableSet {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS |
    Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} :=
  (isClosed_setOf_of_mem_UH_Hpk D.R.k D.R.rS).measurableSet.compl

theorem quot_conc {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)} (hq : Formalism.MainNotions.S.IsQuotMeas μG μS ν)
    (hG0 : μG {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (hS0 : μS {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0) (hSne : μS ≠ 0) :
    ν {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := by
  have hSm := measurableSet_notUH (D := D)
  set S := {m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} with hSdef
  have key : ∀ s x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, s ∉ S → x ∈ S →
      (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ S := by
    intro s x hs hx hsx
    have hs' : (Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of s = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS :=
      Classical.byContradiction fun h => hs h
    have hsx' : (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of s * Matrix.of x) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hsx
    have hx' : ¬ ((Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of x = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := hx
    apply hx'
    calc (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of x
        = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of s) * Matrix.of x := by rw [hs']
      _ = (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of s * Matrix.of x) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hsx'
  have hc : μS Sᶜ = μS Set.univ := by
    rw [measure_compl hSm (by rw [hS0]; exact ENNReal.zero_ne_top), hS0, tsub_zero]
  have hne : μS Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hSne
  have h := hq (S.indicator 1) (measurable_one.indicator hSm)
  rw [lintegral_indicator_one hSm, hG0] at h
  have hle : ∫⁻ x, S.indicator (fun _ => μS Set.univ) x ∂ν ≤
      ∫⁻ x, ∫⁻ s, S.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, ← hc, ← lintegral_indicator_one hSm.compl]
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ S
      · have hs2 : s ∉ Sᶜ := fun h2 => h2 hs
        first | rw [Set.indicator_of_not_mem hs2] | rw [Set.indicator_of_notMem hs2]
        first | exact zero_le | exact zero_le _ | positivity
      · rw [Set.indicator_of_mem (Set.mem_compl hs), Set.indicator_of_mem (key s x hs hx)]
        all_goals exact le_rfl
    · first | rw [Set.indicator_of_not_mem hx] | rw [Set.indicator_of_notMem hx]
      first | exact zero_le | exact zero_le _ | positivity
  rw [← h, lintegral_indicator_const hSm] at hle
  exact (mul_eq_zero.mp (le_zero_iff.mp hle)).resolve_left hne

theorem weil_J (C : Choice X θ) (τ : D.what₂.Tau) {μS ν : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hq : Formalism.MainNotions.S.IsQuotMeas (muGB X (Qcs C τ) (Qics C τ) τ) μS ν)
    (hS0 : μS {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (hν0 : ν {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
      ∫⁻ x, ∫⁻ s, f (s * x) ∂(μS.comap (Tm C τ)) ∂(ν.comap (Tm C τ)) := by
  have hE := Tm_emb C τ
  obtain ⟨F, hF, hFT⟩ : ∃ F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞, Measurable F ∧ ∀ x, F (Tm C τ x) = f x :=
    ⟨Function.extend (Tm C τ) f (fun _ => 0), hE.measurable_extend hf measurable_const,
      fun x => hE.injective.extend_apply f _ x⟩
  have hmu : muGB X (Qcs C τ) (Qics C τ) τ = (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (Tm C τ) := rfl
  have key := hq F hF
  rw [hmu, hE.lintegral_map] at key
  simp only [hFT] at key
  rw [key]
  symm
  have inner : ∀ x, ∫⁻ s, f (s * x) ∂(μS.comap (Tm C τ)) =
      ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of (Tm C τ x)) i j) ∂μS := by
    intro x
    rw [← comap_lint C τ hS0 (fun s => F (fun i j => (Matrix.of s * Matrix.of (Tm C τ x)) i j))]
    congr 1
    funext s
    rw [← hFT (s * x), Tm_mul]
    rfl
  exact (lintegral_congr fun x => inner x).trans
    (comap_lint C τ hν0 (fun y => ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of y) i j) ∂μS))

private theorem measurable_invM' (k r : ℕ) : Measurable (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) := by
  have hdet : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x).det := by
    exact (continuous_id (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)).matrix_det
  have hadj : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x).adjugate := by
    exact (continuous_id (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)).matrix_adjugate
  have hinv : Measurable fun x : Formalism.QuantumDeterminants.Mt k r => ((Matrix.of x).det)⁻¹ := hdet.measurable.inv
  have e : (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) =
      fun x i j => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by
    funext x i j
    show ((Matrix.of x)⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = _
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    first | rw [Ring.inverse_eq_inv'] | rw [Ring.inverse_eq_inv] | simp
  rw [e]
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  exact hinv.mul ((continuous_apply j).comp ((continuous_apply i).comp hadj)).measurable

theorem inv_comap (C : Choice X θ) (τ : D.what₂.Tau) {μS : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hS0 : μS {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (hinv : μS.map Formalism.FourierDecayAlt.B2.invM = μS) :
    (μS.comap (Tm C τ)).map (fun x => x⁻¹) = μS.comap (Tm C τ) := by
  haveI : BorelSpace (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) := ⟨rfl⟩
  have hE := Tm_emb C τ
  have hinvm : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => x⁻¹) := continuous_inv.measurable
  have hae : ∀ᵐ m ∂μS, m ∈ Set.range (Tm C τ) := by
    rw [ae_iff]
    refine measure_mono_null (fun m hm => ?_) hS0
    simp only [Set.mem_setOf_eq] at hm ⊢
    exact fun h => hm (mem_range_Tm C τ h)
  have hc : (Tm C τ ∘ fun x => x⁻¹) = Formalism.FourierDecayAlt.B2.invM ∘ Tm C τ := funext fun x => Tm_inv C τ x
  rw [← hE.comap_map ((μS.comap (Tm C τ)).map fun x => x⁻¹), Measure.map_map hE.measurable hinvm, hc,
    ← Measure.map_map (measurable_invM' D.R.k D.R.rS) hE.measurable, hE.map_comap,
    Measure.restrict_eq_self_of_ae_mem hae, hinv]

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

section Model

variable {k r : ℕ}

theorem uw_fix {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) {w : Fin (2 * r + k + 1) → ℂ} (hw : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → w i = 0) :
    h *ᵥ w = w := by
  obtain ⟨-, hfix, -⟩ := hh
  have key : ∀ i : Fin (2 * r + k + 1), w i • (h *ᵥ Pi.single i (1:ℂ)) = w i • Pi.single i (1:ℂ) := by
    intro i
    have hlt := i.isLt
    by_cases h1 : i.val < r
    · have he : eI k r ⟨i.val, h1⟩ = i := Fin.ext rfl
      have := (hfix ⟨i.val, h1⟩).1
      rw [he] at this
      exact congrArg (fun v => w i • v) this
    · by_cases h2 : r + k < i.val
      · have he : esI k r ⟨2 * r + k - i.val, by omega⟩ = i := Fin.ext (by
          show 2 * r + k - (2 * r + k - i.val) = i.val
          omega)
        have := (hfix ⟨2 * r + k - i.val, by omega⟩).2
        rw [he] at this
        exact congrArg (fun v => w i • v) this
      · rw [hw i (by omega) (by omega), zero_smul, zero_smul]
  have hw' : w = ∑ i, w i • Pi.single i (1:ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show h *ᵥ (∑ i, w i • Pi.single i (1:ℂ)) = ∑ i, w i • (h *ᵥ Pi.single i (1:ℂ)) by
      simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]]
  rw [Finset.sum_congr rfl (fun i _ => key i), ← hw']

private theorem mulVec_single_one_apply_gauge_lattice_shifts {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) :
    (m *ᵥ Pi.single j (1:ℂ)) i = m i j := by
  first
  | simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  | simp [Pi.single_apply]

theorem sset_col {z : Fin (2 * r + k + 1) → ℂ} {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hM : M ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    ((M - 1) *ᵥ bvec (eI k r a)) i = 0 := by
  have ha := a.isLt
  delta Sset at hM
  simp only [Set.mem_setOf_eq] at hM
  obtain ⟨h, hh, m, hm, rfl⟩ := hM
  delta Nset at hm
  simp only [Set.mem_setOf_eq] at hm
  obtain ⟨-, hm1, -⟩ := hm
  have hfix : h *ᵥ (m *ᵥ bvec (eI k r a)) = m *ᵥ bvec (eI k r a) := by
    apply uw_fix hh
    intro j hj1 hj2
    have hne : j ≠ eI k r a := fun e => by
      have := congrArg Fin.val e
      change j.val = a.val at this
      omega
    have := hm1 a j (by omega)
    rw [show bvec (eI k r a) = Pi.single (eI k r a) (1:ℂ) from rfl, mulVec_single_one_apply_gauge_lattice_shifts, this]
    simp [hne]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hfix]
  rw [show bvec (eI k r a) = Pi.single (eI k r a) (1:ℂ) from rfl, Pi.sub_apply, mulVec_single_one_apply_gauge_lattice_shifts, hm1 a i hi]
  simp [Pi.single_apply]

theorem sub_one_mulVec_apply_eq_zero_of_mem_Sset {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : M ∈ Sset k r z) (i : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) : ((M - 1) *ᵥ z) i = 0 := by
  delta inWb at hz
  delta Sset at hM
  simp only [Set.mem_setOf_eq] at hM
  obtain ⟨h, hh, m, hm, rfl⟩ := hM
  delta Nset at hm
  simp only [Set.mem_setOf_eq] at hm
  obtain ⟨-, -, hm2⟩ := hm
  obtain ⟨-, -, hz'⟩ := id hh
  have hmz : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (m *ᵥ z) i = z i := by
    intro i hi
    have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
      intro j
      by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
      · rw [hm2 i j hj.1 hj.2 hi]
        split_ifs <;> simp
      · rw [hz j (by omega)]
        simp
    simp [Matrix.mulVec, dotProduct, hterm]
  have hv : h *ᵥ (m *ᵥ z - z) = m *ᵥ z - z := by
    apply uw_fix hh
    intro j hj1 hj2
    rw [Pi.sub_apply, hmz j hj1, sub_self]
  have hfix : h *ᵥ (m *ᵥ z) = m *ᵥ z := by
    have hsplit : m *ᵥ z = z + (m *ᵥ z - z) := by abel
    rw [hsplit, Matrix.mulVec_add, hz', hv]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hfix, Pi.sub_apply, hmz i hi, sub_self]

theorem sum_low {n : ℕ} (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (a : ℕ) (ha : a ≤ r)
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → w i = 0) :
    Q *ᵥ w = ∑ b : Fin r, (if b.val < a then w (eI k r b) else 0) • (Q *ᵥ bvec (eI k r b)) := by
  have hv : ∀ b : Fin r, (eI k r b).val = b.val := fun b => rfl
  have hw' : w = ∑ b : Fin r, (if b.val < a then w (eI k r b) else 0) • bvec (eI k r b) := by
    ext j
    rw [Finset.sum_apply]
    by_cases hj : j.val < a
    · rw [Finset.sum_eq_single ⟨j.val, by omega⟩]
      · have he : eI k r ⟨j.val, by omega⟩ = j := Fin.ext rfl
        simp [he, hj, bvec]
      · intro b _ hb
        have hne : j ≠ eI k r b := fun h => hb (Fin.ext (by
          have := congrArg Fin.val h
          rw [hv] at this
          simp only [Fin.val_mk]
          omega))
        simp [bvec, Pi.single_apply, hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hw j (by omega)]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      split_ifs with hb
      · have hne : j ≠ eI k r b := fun h => hj (by
          have := congrArg Fin.val h
          rw [hv] at this
          omega)
        simp [bvec, Pi.single_apply, hne]
      · simp
  conv_lhs => rw [hw']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]

end Model

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem qcs_e (C : Choice X θ) (τ : D.what₂.Tau) (b : Fin D.R.rS) :
    Qcs C τ *ᵥ bvec (eI D.R.k D.R.rS b) = cfS D ^ (D.R.rS - (b : ℕ)) • rv X.B.I (vOf X τ) (X.eR b) :=
  ((transpC' C τ).2.2.2 b b rfl).1

theorem qics_e (C : Choice X θ) (τ : D.what₂.Tau) (b : Fin D.R.rS) :
    Qics C τ *ᵥ rv X.B.I (vOf X τ) (X.eR b) = (cfS D ^ (D.R.rS - (b : ℕ)))⁻¹ • bvec (eI D.R.k D.R.rS b) := by
  have h1 := (transpC' C τ).1
  have hc : cfS D ^ (D.R.rS - (b : ℕ)) ≠ 0 := pow_ne_zero _ (Formalism.L2.SG.Pf.cfS_ne D)
  have e := congrArg (fun v => Qics C τ *ᵥ v) (qcs_e C τ b)
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_smul] at e
  rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem qcs_span (C : Choice X θ) (τ : D.what₂.Tau) (a : ℕ) (ha : a ≤ D.R.rS)
    (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) :
    Qcs C τ *ᵥ w ∈ spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a := by
  rw [sum_low (Qcs C τ) a ha w hw]
  refine Submodule.sum_mem _ fun b _ => ?_
  split_ifs with hb
  · rw [qcs_e C τ b]
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    delta spanLt
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  · rw [zero_smul]
    exact Submodule.zero_mem _

theorem sloc_of_sset (C : Choice X θ) (τ : D.what₂.Tau) (u : D.what₂.Word) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (hx : Matrix.of (Tm C τ x) ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ) := by
  have h2 := (transpC' C τ).2.1
  set M := Matrix.of (Tm C τ x) with hMdef
  have hU : uMat x - 1 = Qcs C τ * (M - 1) * Qics C τ := by
    show uMat x - 1 = Qcs C τ * (Qics C τ * uMat x * Qcs C τ - 1) * Qics C τ
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2,
      show Qcs C τ * (Qics C τ * uMat x * Qcs C τ) * Qics C τ = (Qcs C τ * Qics C τ) * uMat x * (Qcs C τ * Qics C τ) by
        simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun a => ?_, ?_⟩
  · rw [hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, qics_e C τ a, Matrix.mulVec_smul, Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ (qcs_span C τ a.val a.isLt.le _ fun i hi => sset_col hx a i hi)
  · rw [hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zc_eq C u τ]
    exact qcs_span C τ D.R.rS le_rfl _ fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Sset (Formalism.L2.SG.Pf.zTr C u τ).1 hx i hi

theorem bvec_supSub (a : ℕ) (b : Fin D.R.rS) (hb : b.val < a) :
    bvec (eI D.R.k D.R.rS b) ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a := by
  show ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → bvec (eI D.R.k D.R.rS b) i = 0
  intro i hi
  have hne : i ≠ eI D.R.k D.R.rS b := fun e => by
    have := congrArg Fin.val e
    change i.val = b.val at this
    omega
  show (Pi.single (eI D.R.k D.R.rS b) (1:ℂ) : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) i = 0
  simp only [Pi.single_apply, hne, if_false]

theorem qics_span (C : Choice X θ) (τ : D.what₂.Tau) (a : ℕ) (w : Fin X.B.I.n → ℂ)
    (hw : w ∈ spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a) :
    Qics C τ *ᵥ w ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a := by
  have hle : spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a ≤
      (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a).comap (Matrix.mulVecLin (Qics C τ)) := by
    delta spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    show Matrix.mulVecLin (Qics C τ) (rv X.B.I (vOf X τ) (X.eR b)) ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a
    rw [Matrix.mulVecLin_apply, qics_e C τ b]
    exact Submodule.smul_mem _ _ (bvec_supSub a b hb)
  have := hle hw
  rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at this

theorem sset_of_sloc (C : Choice X θ) (τ : D.what₂.Tau) (u : D.what₂.Word) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (hx : x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ)) :
    Matrix.of (Tm C τ x) ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  have h1 := (transpC' C τ).1
  have h2 := (transpC' C τ).2.1
  refine Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.fwd _ _ (Tm_mem C τ x) (Formalism.L2.SG.Pf.zTr C u τ).1 ⟨fun a => ?_, ?_⟩
  · have hM : (Matrix.of (Tm C τ x) - 1) *ᵥ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.stdX D.R.k D.R.rS a =
        cfS D ^ (D.R.rS - (a : ℕ)) • (Qics C τ *ᵥ ((uMat x - 1) *ᵥ rv X.B.I (vOf X τ) (X.eR a))) := by
      show (Qics C τ * uMat x * Qcs C τ - 1) *ᵥ bvec (eI D.R.k D.R.rS a) = _
      rw [show Qics C τ * uMat x * Qcs C τ - 1 = Qics C τ * (uMat x - 1) * Qcs C τ by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1], ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        qcs_e C τ a, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rw [hM]
    exact Submodule.smul_mem _ _ (qics_span C τ a.val _ (hx.1 a))
  · have hz : Qcs C τ *ᵥ zB X (C.Qi τ) u τ = rv X.B.I (vOf X τ) (X.zR u) := by
      rw [← zc_eq C u τ, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have hM : (Matrix.of (Tm C τ x) - 1) *ᵥ zB X (C.Qi τ) u τ =
        Qics C τ *ᵥ ((uMat x - 1) *ᵥ rv X.B.I (vOf X τ) (X.zR u)) := by
      show (Qics C τ * uMat x * Qcs C τ - 1) *ᵥ zB X (C.Qi τ) u τ = _
      rw [show Qics C τ * uMat x * Qcs C τ - 1 = Qics C τ * (uMat x - 1) * Qcs C τ by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1], ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz]
    rw [hM]
    exact qics_span C τ D.R.rS _ hx.2

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal Classical

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem mem_om_loc {v : InfinitePlace X.B.I.F} {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : 0 < sc) (u u' : D.what₂.Word) (cv : Fin (D.R.rS + 1) → ℂ)
    (hcv : cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u') (g : Formalism.REAL.UJ (X.B.I.ε v))
    (hg : Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv) :
    trG Q Qi g ∈ Formalism.FourierDecayAlt.JF.Om D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) := by
  have hsc0 : sc ≠ 0 := hsc.ne'
  set γ : X.B.I.Ginf := Function.update (1 : X.B.I.Ginf) v g with hγdef
  have hγv : γ v = g := by rw [hγdef]; exact Function.update_self _ _ _
  obtain ⟨d, hd⟩ : ∃ d : Fin (D.R.rS + 1) → ℂ, d = fun a => star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a * cv a :=
    ⟨_, rfl⟩
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
      (trG Q Qi g) = Matrix.diagonal d := by
    ext a b
    have := zhat_tr X hQ hsc0 u u' γ a b
    rw [hγv] at this
    rw [this]
    have hZX : ZX X u u' sc γ v = Matrix.diagonal cv := by
      unfold ZX; rw [hγv]; exact hg
    rw [hZX]
    by_cases hab : a = b
    · subst hab; simp [hd]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hd0 : ∀ a, d a ≠ 0 := fun a => by
    rw [hd]; exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (dsc_ne hl hsc0 a)) (dsc_ne hl hsc0 a)) (hcv.1 a)
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem Q Qi _ hQ.2.1 hQ.2.2.1 g, fun l _ => ?_, ?_⟩
  · rw [dmin_diag _ _ _ d hZ l]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
  · unfold Formalism.QuantumDeterminants.Gf
    rw [dmin_diag _ _ _ d hZ, dmin_diag _ _ _ d hZ,
      (show Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) = Tw u from (Formalism.L2.SG.Pf.Choice.zTr_of X hQ u).2),
      (show Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) = Tw u' from (Formalism.L2.SG.Pf.Choice.zTr_of X hQ u').2)]
    have hlast := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.normSq_last_gt (Tw u) (Tw u') cv hcv.2
    have hcl : ∀ (h : D.R.rS + 1 ≤ D.R.rS + 1) (i : Fin (D.R.rS + 1)), Fin.castLE h i = i := fun _ _ => Fin.ext rfl
    have hdl : d (Fin.last D.R.rS) = cv (Fin.last D.R.rS) := by simp only [hd, dsc_last, star_one, one_mul]
    obtain ⟨P, hPd⟩ : ∃ P : ℂ, P = ∏ i : Fin D.R.rS, d (Fin.castSucc i) := ⟨_, rfl⟩
    have e1 : ∏ i : Fin (Fin.last (D.R.rS + 1)).val, d (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt) i) =
        P * cv (Fin.last D.R.rS) := by
      show ∏ i : Fin (D.R.rS + 1), d (Fin.castLE _ i) = _
      rw [Fin.prod_univ_castSucc]
      simp only [hcl, hdl, hPd]
    have e2 : ∏ i : Fin (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).val,
        d (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt) i) = P := by
      rw [hPd]; rfl
    rw [e1, e2]
    have hP0 : P ≠ 0 := by rw [hPd]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
    rw [Complex.normSq_mul]
    have hn : Tw u * Tw u' < Complex.normSq (cv (Fin.last D.R.rS)) := by
      rw [Complex.normSq_eq_norm_sq]; exact hlast
    have hp : 0 < Complex.normSq P := Complex.normSq_pos.mpr hP0
    nlinarith

theorem sideC_SF (C : Choice X θ) (hθ : 0 < θ) (u : D.what₂.Word) (τ : D.what₂.Tau) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h)
    {w0 : X.B.H (vOf X τ)} (hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) w0) :
    ∃ νq, SFinite νq ∧ Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (Qcs C τ) (Qics C τ) τ) w0
      (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ)
      (C.muW u τ) ((muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) (muGB X (Qcs C τ) (Qics C τ) τ) νq := by
  obtain ⟨hz, hT⟩ := zT C u τ
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  have hDS : IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) := by
    obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    refine ⟨P, hP, ?_⟩
    exact dsHpk_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
      (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
      (X.B.lam (vOf X τ)) (lamD D τ)
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ (vOf X τ)) (X.ds (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg P hP
  have hμG := haar_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg
  have hμN := muNc_haar (D := D) hθ
  obtain ⟨νq, hsf, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExistsSF _ _ _ hz hT _ _ hμG
    (isHaarOn_muS_gen hz hT (C.muW_haar u τ) (C.muW_one u τ) (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  exact ⟨νq, hsf, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, hDS, hgap, hok, hlow, hz, hT, cStd_ne, hty_c C u τ,
    C.muW_haar u τ, hμN, hμG, hq⟩

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem sigC_Tm (C : Choice X θ) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    sigB X (Qcs C τ) (Qics C τ) τ (Matrix.of (Tm C τ y)) = X.B.σ (vOf X τ) (uMat y) := by
  have h2 := (transpC' C τ).2.1
  show X.B.σ (vOf X τ) (Qcs C τ * (Qics C τ * uMat y * Qcs C τ) * Qics C τ) = _
  rw [show Qcs C τ * (Qics C τ * uMat y * Qcs C τ) * Qics C τ = (Qcs C τ * Qics C τ) * uMat y * (Qcs C τ * Qics C τ) by
    simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]

theorem lintegral_four_comap (C : Choice X θ) (τ : D.what₂.Tau) {ν0 ν0' μ1 μ1' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (h0 : ν0 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h0' : ν0' {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1 : μ1 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1' : μ1' {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (G : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS →
      Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ x', ∫⁻ s, ∫⁻ s', G (Tm C τ x) (Tm C τ x') (Tm C τ s) (Tm C τ s')
      ∂(μ1'.comap (Tm C τ)) ∂(μ1.comap (Tm C τ)) ∂(ν0'.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) =
    ∫⁻ m, ∫⁻ m', ∫⁻ p, ∫⁻ p', G m m' p p' ∂μ1' ∂μ1 ∂ν0' ∂ν0 := by
  rw [← comap_lint C τ h0 (fun m => ∫⁻ m', ∫⁻ p, ∫⁻ p', G m m' p p' ∂μ1' ∂μ1 ∂ν0')]
  refine lintegral_congr fun x => ?_
  rw [← comap_lint C τ h0' (fun m' => ∫⁻ p, ∫⁻ p', G (Tm C τ x) m' p p' ∂μ1' ∂μ1)]
  refine lintegral_congr fun x' => ?_
  rw [← comap_lint C τ h1 (fun p => ∫⁻ p', G (Tm C τ x) (Tm C τ x') p p' ∂μ1')]
  refine lintegral_congr fun s => ?_
  rw [← comap_lint C τ h1' (fun p' => G (Tm C τ x) (Tm C τ x') (Tm C τ s) p')]

theorem lintegral_three_comap (C : Choice X θ) (τ : D.what₂.Tau) {ν0 μ1 : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (h0 : ν0 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1 : μ1 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (G : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ x', ∫⁻ s, G (Tm C τ x) (Tm C τ x') (Tm C τ s)
      ∂(μ1.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) =
    ∫⁻ m, ∫⁻ m', ∫⁻ p, G m m' p ∂μ1 ∂ν0 ∂ν0 := by
  rw [← comap_lint C τ h0 (fun m => ∫⁻ m', ∫⁻ p, G m m' p ∂μ1 ∂ν0)]
  refine lintegral_congr fun x => ?_
  rw [← comap_lint C τ h0 (fun m' => ∫⁻ p, G (Tm C τ x) m' p ∂μ1)]
  refine lintegral_congr fun x' => ?_
  rw [← comap_lint C τ h1 (fun p => G (Tm C τ x) (Tm C τ x') p)]

end Formalism.L2.SG.RealObj.EnergyConvJ
