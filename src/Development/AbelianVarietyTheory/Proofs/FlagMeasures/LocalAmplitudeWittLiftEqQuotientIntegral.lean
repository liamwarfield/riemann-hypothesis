module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootMeasureIndependentOfChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuous
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem uh_mul {k r : ℕ} {a b : MatKR k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem b_eq_wT (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := uh_mul hm (C.y_mem τ)
  have hJ := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hmy
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    ⟨Formalism.L2.SG.Pf.LocJEq.ujOf' _ hJ, rfl⟩
  unfold wT
  rw [dite_eq_left hex, Formalism.L2.SG.Pf.LocJEq.wloc_eq C hB u τ]
  have hc : Formalism.MainNotions.S.umat hex.choose = C.Q τ * (m * C.y τ) * C.Qi τ := hex.choose_spec
  rw [hc]
  unfold v0Of sigB
  rw [← Formalism.L2.SG.Pf.LocJEq.sig_mul τ (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hm)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (C.y_mem τ))]
  congr 2
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * m * (C.Qi τ * C.Q τ) * C.y τ * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, (C.isT τ).1, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem isSPsiEquiv_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {W F : MatKR k r → Wp}
    {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hW : IsSPsiEquiv z ψ π W)
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) : IsSPsiEquiv z ψ π F := by
  intro h hh n hn g hg
  have hhng : h * n * g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := uh_mul (uh_mul hh.1 hn.1) hg
  rw [hF _ hhng, hF g hg, Matrix.mul_assoc (h * n) g y, hW h hh n hn (g * y) (uh_mul hg hy), map_smul,
    smul_comm s (ψ n)]

theorem continuousOn_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {W F : MatKR k r → Wp} {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hW : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) :
    ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have h1 : ContinuousOn (fun m : MatKR k r => s • W (m * y)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hW.comp (continuous_id.matrix_mul continuous_const).continuousOn fun m hm => uh_mul hm hy).const_smul s
  exact h1.congr hF

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), (locS hB u u' τ).Φ m = (1 : ℂ) • wT C u τ (m * C.y τ) :=
  fun m hm => by rw [one_smul]; exact b_eq_wT C hB u τ hm

theorem phi'_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      (locS hB u u' τ).Φ' m = sclOf hB u u' τ • wT C u' τ (m * C.y τ) :=
  fun m hm => by
    show sclOf hB u u' τ • bOf hB u' τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = _
    rw [b_eq_wT C hB u' τ hm]

theorem tie_of (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hc : ∀ u, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)))
    (he : ∀ u, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)) :
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  ⟨isSPsiEquiv_transl 1 (C.y_mem τ) (he u) (phi_eq C hB u u' τ),
    isSPsiEquiv_transl _ (C.y_mem τ) (he u') (phi'_eq C hB u u' τ),
    continuousOn_transl 1 (C.y_mem τ) (hc u) (phi_eq C hB u u' τ),
    continuousOn_transl _ (C.y_mem τ) (hc u') (phi'_eq C hB u u' τ)⟩

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

theorem locS_phi_equiv_cont : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  fun D X θ C hB u u' τ _ =>
    tie_of C hB u u' τ (fun u => Formalism.L2.SG.Pf.LocF.local_continuity_all D X θ C u τ)
      (fun u => Formalism.L2.SG.Pf.EquivPf.local_equivalence_all D X θ C u τ)

end GlobalTheory.SlocTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuousStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localRealData_functions_equivariant_continuous :
    ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
      (u u' : D.what₂.Word) (τ : D.what₂.Tau),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  GlobalTheory.SlocTie.locS_phi_equiv_cont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotient
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotTransport

lemma jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

lemma exists_unit {n m : ℕ} (ε : Fin n → Bool) (H : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (h3 : Qᴴ * Formalism.REAL.Jm ε * Q = H)
    (y : Matrix (Fin m) (Fin m) ℂ) (hy : yᴴ * H * y = H) :
    ∃ g : Formalism.REAL.UJ ε, ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Q * y⁻¹ * Qi := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := jm_mul_self ε
  have hHi : (Qi * Formalism.REAL.Jm ε * Qiᴴ) * H = 1 := by
    have : H * (Qi * Formalism.REAL.Jm ε * Qiᴴ) = 1 := by
      rw [← h3]
      calc Qᴴ * Formalism.REAL.Jm ε * Q * (Qi * Formalism.REAL.Jm ε * Qiᴴ)
          = Qᴴ * Formalism.REAL.Jm ε * (Q * Qi) * Formalism.REAL.Jm ε * Qiᴴ := by simp only [Matrix.mul_assoc]
        _ = Qᴴ * Qiᴴ := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc Qᴴ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ, Matrix.mul_one]
        _ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    exact mul_eq_one_comm.mp this
  have hl : (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = 1 := by
    calc (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = (Qi * Formalism.REAL.Jm ε * Qiᴴ) * (yᴴ * H * y) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, hHi]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  have hyr : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y hdet
  have hyl : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hdet
  have hy' : (y⁻¹)ᴴ * H * y⁻¹ = H := by
    calc (y⁻¹)ᴴ * H * y⁻¹ = (y⁻¹)ᴴ * (yᴴ * H * y) * y⁻¹ := by rw [hy]
      _ = (y * y⁻¹)ᴴ * H * (y * y⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hyr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    ⟨Q * y⁻¹ * Qi, Q * y * Qi, by
      calc Q * y⁻¹ * Qi * (Q * y * Qi) = Q * (y⁻¹ * (Qi * Q) * y) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyl, Matrix.mul_one, h2],
     by
      calc Q * y * Qi * (Q * y⁻¹ * Qi) = Q * (y * (Qi * Q) * y⁻¹) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyr, Matrix.mul_one, h2]⟩
  have hu : u ∈ Formalism.REAL.UJ ε := by
    show Formalism.REAL.inUJ ε (Q * y⁻¹ * Qi)
    unfold Formalism.REAL.inUJ
    calc (Q * y⁻¹ * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * y⁻¹ * Qi)
        = Qiᴴ * ((y⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * y⁻¹) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [h3, hy']
      _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  exact ⟨⟨u, hu⟩, rfl⟩

end GlobalTheory.QuotTransport

namespace GlobalTheory


open GlobalTheory.QuotTransport in
theorem quotMeas_besselModel_of_quotLoc : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  intro D X θ C τ γ μ ν hμ hq f hf
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  obtain ⟨g, hg⟩ := exists_unit _ _ (C.Q τ) (C.Qi τ) h1 h2 h3 (C.y τ) (C.y_mem τ)
  have h2' : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M := by
    intro M; rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hγ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      ((γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        ((((γ⁻¹ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.one_mul]
  have hc : Continuous (fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => uMat w) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcM : ∀ {h : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}, Continuous h →
      ∀ (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ)
        (B : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ),
      Continuous (fun w => (Matrix.of.symm (A * uMat (h w) * B) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    fun hh A B => (continuous_const.matrix_mul (hc.comp hh)).matrix_mul continuous_const
  have hcβ : Continuous (fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (hcM (continuous_const_mul γ⁻¹) (C.Qi τ) (C.Q τ)).matrix_mul (continuous_const (y := (C.y τ)⁻¹))
  set φ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun w => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) w) with hφ
  set α : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)) with hα
  set β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) with hβ
  have hφm : Measurable φ := (hcM continuous_id _ _).measurable
  have hαm : Measurable α := (hcM ((continuous_const.mul continuous_id).mul continuous_const) _ _).measurable
  have hβm : Measurable β := hcβ.measurable
  have hpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))) :=
    Continuous.matrix_mul continuous_snd continuous_fst
  have hj : Measurable (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j)) :=
    hf.comp hpc.measurable
  have hA : ∀ w, φ (w * g) = β (γ * w) := by
    intro w
    show Matrix.of.symm (C.Qi τ * uMat (w * g) * C.Q τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * (γ * w)) * C.Q τ * (C.y τ)⁻¹)
    rw [inv_mul_cancel_left]
    congr 1
    simp only [uMat, Subgroup.coe_mul, Units.val_mul, hg, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hB : ∀ y z, β (y * z) = fun i j => (Matrix.of (α y) * Matrix.of (β z)) i j := by
    intro y z
    simp only [hα, hβ, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply, uMat, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc, h2', hγ]
    rfl
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ) = ∫⁻ x, ∫⁻ s,
    f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(μ.map α) ∂(ν.map β)
  rw [lintegral_map (hj.lintegral_prod_right' (ν := μ.map α)) hβm]
  calc ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ)
      = ∫⁻ w, f (φ w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_map hf hφm
    _ = ∫⁻ w, f (φ (w * g)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        (lintegral_mul_right_eq_self (fun w => f (φ w)) g).symm
    _ = ∫⁻ w, f (β (γ * w)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by simp only [hA]
    _ = ∫⁻ w, f (β w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_mul_left_eq_self (fun w => f (β w)) γ
    _ = ∫⁻ z, ∫⁻ y, f (β (y * z)) ∂μ ∂ν := hq _ (hf.comp hβm)
    _ = ∫⁻ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (β z)) i j) ∂(μ.map α) ∂ν := by
        refine lintegral_congr fun z => ?_
        have hmz : Measurable (fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
            f (fun i j => (Matrix.of s * Matrix.of (β z)) i j)) := hj.comp measurable_prodMk_left
        rw [lintegral_map hmz hαm]
        simp only [hB]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotientStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_besselModel_of_local_quotient : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  first | exact @GlobalTheory.quotMeas_besselModel_of_quotLoc | exact GlobalTheory.quotMeas_besselModel_of_quotLoc | (intros; apply GlobalTheory.quotMeas_besselModel_of_quotLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.AmpUniq

theorem isQuotMeas_smul {k r : ℕ} {μG μR ν : Measure (Mt k r)} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : IsQuotMeas μG (c • μR) ν) : IsQuotMeas μG μR (c • ν) := by
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  exact lintegral_const_mul' _ _ hc

theorem equiv_N {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {Φ : Mat k r → Wp}
    (hπ : IsURepOn (UWset k r z) π) (hΦ : IsSPsiEquiv z ψ π Φ) {n : Mat k r} (hn : n ∈ Nset k r)
    {x : Mat k r} (hx : x ∈ GG k r) : Φ (n * x) = ψ n • Φ x := by
  have h1 : (1 : Mat k r) ∈ UWset k r z := (isClosedSub_UWset (k := k) (r := r) z).2.2.1
  have e := hΦ 1 h1 n hn x hx
  rw [hπ.1.1, one_mul, ContinuousLinearMap.one_apply] at e
  exact e

theorem amp_uniq : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ z z' ψ ψ' π π' Φ Φ' cN _ _ _ _ hπ hπ' hψ hΦ hΦ' hc hc' γ μG μR ν ν' t hγ
    hψγ hG hR ht hν hν'
  obtain ⟨hRc, hRu⟩ := GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular k r γ hγ
  have hν₂ : IsQuotMeas μG μR (ENNReal.ofReal t • ν') := isQuotMeas_smul ENNReal.ofReal_ne_top hν'
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  let F : Mat k r → (Wq →L[ℂ] Wp) := fun g => (innerSL ℂ (Φ' g)).smulRight (Φ (γ * g))
  have hFc : ContinuousOn F (GG k r) := by
    have h1 : ContinuousOn (fun g => innerSL ℂ (Φ' g)) (GG k r) :=
      (innerSL ℂ).continuous.comp_continuousOn hc'
    have h2 : ContinuousOn (fun g => Φ (γ * g)) (GG k r) :=
      hc.comp (continuous_const.mul continuous_id).continuousOn fun g hg => hGm γ hγ g hg
    exact (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂.comp_continuousOn (h1.prodMk h2)
  have hFi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, F (ρ * x) = F x := by
    intro ρ hρ x hx
    have hρN : ρ ∈ Nset k r := hρ.1
    have hρc : γ * ρ * γ⁻¹ ∈ Nset k r := hρ.2
    have e1 : Φ' (ρ * x) = ψ' ρ • Φ' x := equiv_N hπ' hΦ' hρN hx
    have e2 : γ * (ρ * x) = γ * ρ * γ⁻¹ * (γ * x) := by
      rw [show γ * ρ * γ⁻¹ * (γ * x) = γ * ρ * (γ⁻¹ * γ) * x by simp only [Matrix.mul_assoc],
        Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hγ), Matrix.mul_one, Matrix.mul_assoc]
    have e3 : Φ (γ * (ρ * x)) = ψ' ρ • Φ (γ * x) := by
      rw [e2, equiv_N hπ hΦ hρc (hGm γ hγ x hx), hψγ ρ hρ]
    have hn : ‖ψ' ρ‖ = 1 := (hψ ρ hρN).2
    ext w
    simp only [F, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, e1, e3, inner_smul_left,
      smul_smul]
    congr 1
    calc (starRingEnd ℂ) (ψ' ρ) * inner ℂ (Φ' x) w * ψ' ρ
        = ((starRingEnd ℂ) (ψ' ρ) * ψ' ρ) * inner ℂ (Φ' x) w := by ring
      _ = inner ℂ (Φ' x) w := by rw [Complex.conj_mul', hn]; simp
  have key := (GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary k r (Rset k r γ) μG μR ν (ENNReal.ofReal t • ν') hRc hG hR (hRu μR hR) hν hν₂
    (Wq →L[ℂ] Wp) F hFc hFi).2
  rw [integral_smul_measure, ENNReal.toReal_ofReal ht.le] at key
  change (cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν = (t : ℂ) • ((cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν')
  rw [key, Complex.coe_smul, smul_comm]

end GlobalTheory.SnMass.AmpUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasureStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselAmplitude_eq_smul_of_rescaled_stabilizerHaar : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  first | exact @GlobalTheory.SnMass.AmpUniq.amp_uniq | exact GlobalTheory.SnMass.AmpUniq.amp_uniq | (intros; apply GlobalTheory.SnMass.AmpUniq.amp_uniq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariant
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.AmpCoset

variable {k r : ℕ}

theorem exists_blocks (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) :
    ∃ cs : List (ℂˣ × ℕ+), (cs.map (fun b => (b.2 : ℕ))).sum = (bs.map Prod.snd).sum ∧
      ∀ i j, Loc.ptEntryL cs i j = ptEntry bs i j := by
  induction bs with
  | nil => exact ⟨[], rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    obtain ⟨cs, h1, h2⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨h3, h4⟩ := h (t, s) List.mem_cons_self
    refine ⟨(Units.mk0 t h3, ⟨s, h4⟩) :: cs, by simp [h1], fun i j => ?_⟩
    simp only [Loc.ptEntryL, ptEntry, h2]
    rfl

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (m : Mat k r) :
    ell k r z m = ∑ j : Fin r, Uof k r z m j.castSucc j.succ := by
  unfold ell
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Uof
  rw [dite_eq_left (show (j.castSucc).val < r from j.2)]
  split_ifs with h
  · exact (mF_col z m _ j.succ h).symm
  · have h' : ¬ (j.succ).val < r := h
    simp [Matrix.mul_apply, Fm, fvec, h, Matrix.mulVec, dotProduct]

theorem psi_exact {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (c : ℝ) {g : Mat k r}
    (hg : g ∈ GG k r) {p : Point ℂ (r + 1)} (hp : ZhatO k r z z' g = ptMat p) {ρ : Mat k r} (hρ : ρ ∈ Rset k r g) :
    psi k r z c (g * ρ * g⁻¹) = psi k r z' c ρ := by
  obtain ⟨cs, h1, h2⟩ := exists_blocks p.1 p.2.1
  obtain ⟨hm', hs⟩ := (GlobalTheory.BesselPsi.psi_character k r z c hz).2.2.1 _ hρ.2
  have hgu := isUnit_det_of_mem_GG hg
  have hmu := isUnit_det_of_mem_GG hρ.2.1
  set m := g * ρ * g⁻¹ with hm
  have hU : (m⁻¹)ᴴ * Hpk k r * m⁻¹ = Hpk k r := hm'.1
  have e1 : m * g = g * ρ := by rw [hm, Matrix.nonsing_inv_mul_cancel_right _ _ hgu]
  have key : (Uof k r z m⁻¹)ᴴ * Zhat k r z z' g = Zhat k r z z' g * Uof k r z' ρ := by
    rw [Zhat_eq]
    calc (Uof k r z m⁻¹)ᴴ * ((Fm k r z)ᴴ * Hpk k r * g * Fm k r z')
        = (Fm k r z * Uof k r z m⁻¹)ᴴ * Hpk k r * (m⁻¹ * (m * g)) * Fm k r z' := by
          rw [conjTranspose_mul, Matrix.nonsing_inv_mul_cancel_left _ _ hmu]; simp only [Matrix.mul_assoc]
      _ = (Fm k r z)ᴴ * ((m⁻¹)ᴴ * Hpk k r * m⁻¹) * g * (ρ * Fm k r z') := by
          rw [← N_F hz hm', e1, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, N_F hz' hρ.1]; simp only [Matrix.mul_assoc]
  have main := GlobalTheory.HL.CharAgree.simple_sum (⟨cs, h1.trans p.2.2⟩ : Loc.Pt ℂ (r + 1)) (Zhat k r z z' g)
    (Uof k r z m⁻¹)ᴴ (Uof k r z' ρ) (fun a b => by
      have := congrFun (congrFun hp a) b
      simp only [ZhatO, ptMat] at this
      simp only [Loc.Pt.mat, h2, ← this]
      rw [mul_comm, ← mul_assoc, ← mul_pow]; simp)
    (fun i j h => by rw [conjTranspose_apply, Uof_lower_zero hm' j i h, star_zero])
    (fun i j h => Uof_lower_zero hρ.1 i j h) (fun a b => congrFun (congrFun key a) b)
  simp only [conjTranspose_apply] at main
  rw [← star_sum, ← ell_eq, ← ell_eq] at main
  rw [← star_star (psi k r z c m), ← hs]
  have e2 : ell k r z' ρ = - star (ell k r z m⁻¹) := by rw [main, neg_neg]
  unfold psi
  rw [e2, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp

theorem psi_cell {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (c : ℝ) {n n' g : Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (hγ : n * g * n' ∈ GG k r) {p : Point ℂ (r + 1)}
    (hp : ZhatO k r z z' g = ptMat p) {ρ : Mat k r} (hρ : ρ ∈ Rset k r (n * g * n')) :
    psi k r z c (n * g * n' * ρ * (n * g * n')⁻¹) = psi k r z' c ρ := by
  obtain ⟨-, -, -, gm, gi⟩ := isClosedSub_GG (k := k) (r := r)
  obtain ⟨-, -, -, nm, ni⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG hn.1
  have hu' := isUnit_det_of_mem_GG hn'.1
  have hg : g ∈ GG k r := by
    have := gm _ (gm _ (gi _ hn.1) _ hγ) _ (gi _ hn'.1)
    rwa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu', Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  have conj : ∀ w, inWb k r w → ∀ a ∈ Nset k r, ∀ x ∈ Nset k r, psi k r w c (a * x * a⁻¹) = psi k r w c x := by
    intro w hw a ha x hx
    obtain ⟨q1, q2, q3, -⟩ := GlobalTheory.BesselPsi.psi_character k r w c hw
    rw [(q2 _ (nm _ ha _ hx) _ (ni _ ha)).2, (q2 _ ha _ hx).2, (q3 _ ha).2, mul_right_comm, Complex.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, q1]
    simp
  have e : n * g * n' * ρ * (n * g * n')⁻¹ = n * (g * (n' * ρ * n'⁻¹) * g⁻¹) * n⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
  have h2 : g * (n' * ρ * n'⁻¹) * g⁻¹ ∈ Nset k r := by
    have := nm _ (nm _ (ni _ hn) _ hρ.2) _ hn
    rw [e] at this
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul n hu, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left n _ hu] using this
  rw [e, conj z hz n hn _ h2, psi_exact hz hz' c hg hp ⟨nm _ (nm _ hn' _ hρ.1) _ (ni _ hn'), h2⟩,
    conj z' hz' n' hn' _ hρ.1]

theorem cont_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem cont_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

noncomputable def lmulE {a : Mat k r} (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left a (Matrix.of x) ha
  right_inv x := Matrix.mul_nonsing_inv_cancel_left a (Matrix.of x) ha
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable

theorem quot_translate {μG μR ν : Measure (Mt k r)} {a : Mat k r} (ha : IsUnit a.det)
    (hG : μG.map (lmulM a) = μG) (h : IsQuotMeas μG μR ν) :
    IsQuotMeas μG (μR.map (conjM a)) (ν.map (lmulM a)) := by
  intro f hf
  have mL := (cont_lmul a).measurable
  have mC := (cont_conj a).measurable
  have e1 : ∫⁻ x, f x ∂μG = ∫⁻ x, f (lmulM a x) ∂μG := by
    conv_lhs => rw [← hG]
    rw [lintegral_map hf mL]
  rw [e1, h (fun x => f (lmulM a x)) (hf.comp mL)]
  refine Eq.trans ?_ ((lmulE ha).measurableEmbedding.lintegral_map _).symm
  refine lintegral_congr fun x => ?_
  have c2 : Continuous fun s : Mt k r => (fun i j => (Matrix.of s * Matrix.of (lmulE ha x)) i j : Mt k r) :=
    (continuous_id (X := Mat k r)).matrix_mul continuous_const
  have m2 : Measurable fun s : Mt k r => f (fun i j => (Matrix.of s * Matrix.of (lmulE ha x)) i j) :=
    hf.comp c2.measurable
  rw [lintegral_map m2 mC]
  refine lintegral_congr fun s => congrArg f ?_
  show a * (Matrix.of s * Matrix.of x) = a * Matrix.of s * a⁻¹ * (a * Matrix.of x)
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha]

theorem ae_mem_of_quot {μG μR ν : Measure (Mt k r)} {R : Set (Mat k r)} (hR : R ⊆ GG k r)
    (hG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn R μR) (h : IsQuotMeas μG μR ν) :
    ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
  obtain ⟨-, gc, -, gm, gi⟩ := isClosedSub_GG (k := k) (r := r)
  set B : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hB
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
  have mB : MeasurableSet B := (gc.preimage hof).measurableSet.compl
  have h1 := h (B.indicator 1) (measurable_one.indicator mB)
  rw [lintegral_indicator_one mB, hG.2.2.1] at h1
  have h2 : ∫⁻ x, B.indicator (fun _ => μR Set.univ) x ∂ν ≤ 0 := by
    rw [h1]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine (lintegral_congr_ae ?_).le
      filter_upwards [(ae_iff.2 hμ.2.2.1 : ∀ᵐ s ∂μR, Matrix.of s ∈ R)] with s hs
      rw [Set.indicator_of_mem]
      · rfl
      · intro hsx
        have := gm _ (gi _ (hR hs)) _ hsx
        exact hx (Matrix.nonsing_inv_mul_cancel_left (Matrix.of s) (Matrix.of x) (isUnit_det_of_mem_GG (hR hs)) ▸ this)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  rw [lintegral_indicator_const mB, nonpos_iff_eq_zero, mul_eq_zero, Measure.measure_univ_eq_zero] at h2
  exact ae_iff.2 (h2.resolve_left hμ.2.1)

section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem exists_isometry {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    {Φ : Mat k r → Wp} (hπ : IsURepOn (UWset k r z) π) (hψ : ∀ n, ‖ψ n‖ = 1) (hΦ : IsSPsiEquiv z ψ π Φ)
    {a : Mat k r} (ha : a ∈ Sset k r z) : ∃ U : Wp ≃ₗᵢ[ℂ] Wp, ∀ g ∈ GG k r, Φ (a * g) = U (Φ g) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  refine ⟨LinearIsometry.toLinearIsometryEquiv ⟨(ψ m • π h).toLinearMap, fun v => ?_⟩ rfl, fun g hg => hΦ h hh m hm g hg⟩
  show ‖ψ m • π h v‖ = ‖v‖
  rw [norm_smul, hψ, one_mul, hπ.2.1 h hh]

theorem hsNormSq_arrow (U : Wp ≃ₗᵢ[ℂ] Wp) (V : Wq ≃ₗᵢ[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    hsNormSq (V.toContinuousLinearEquiv.arrowCongr U.toContinuousLinearEquiv A) = hsNormSq A := by
  have e : V.toContinuousLinearEquiv.arrowCongr U.toContinuousLinearEquiv A =
      (U.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp (A.comp (V.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)) := by
    ext v; simp
  have e2 : ∀ X Y : Wq →L[ℂ] Wp, hsInner X Y = Formalism.FourierDecayAlt.B.hsInner X Y := fun X Y =>
    (Formalism.FourierDecayAlt.P.Topx1.hsInner_eq X Y).symm
  unfold hsNormSq
  rw [e, e2, e2, Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (by simp), Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (by simp)]

theorem hsNormSq_ampJ_translate [CompleteSpace Wp] {ν : Measure (Mt k r)} (hν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r) (c : ℝ)
    {Φ : Mat k r → Wp} {Φ' : Mat k r → Wq} {γ a a' : Mat k r} (hγ : γ ∈ GG k r) (ha' : IsUnit a'.det)
    (U : Wp ≃ₗᵢ[ℂ] Wp) (V : Wq ≃ₗᵢ[ℂ] Wq) (hU : ∀ g ∈ GG k r, Φ (a * g) = U (Φ g))
    (hV : ∀ g ∈ GG k r, Φ' (a' * g) = V (Φ' g)) :
    hsNormSq (ampJ (ν.map (lmulM a')) c Φ Φ' (a * γ * a'⁻¹)) = hsNormSq (ampJ ν c Φ Φ' γ) := by
  rw [← hsNormSq_arrow U V (ampJ ν c Φ Φ' γ)]
  congr 1
  unfold ampJ
  rw [map_smul, ← ContinuousLinearEquiv.integral_comp_comm]
  congr 1
  refine ((lmulE ha').measurableEmbedding.integral_map _).trans (integral_congr_ae ?_)
  filter_upwards [hν] with x hx
  have e : a * γ * a'⁻¹ * (a' * Matrix.of x) = a * (γ * Matrix.of x) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha']
  show (innerSL ℂ (Φ' (a' * Matrix.of x))).smulRight (Φ (a * γ * a'⁻¹ * (a' * Matrix.of x))) = _
  rw [e, hV _ hx, hU _ (isClosedSub_GG.2.2.2.1 _ hγ _ hx)]
  ext v
  simp [← V.inner_map_map (Φ' (Matrix.of x)) (V.symm v)]

end

theorem ka_pos (D : D7) : 0 < D.host.ka := by
  refine div_pos Real.pi_pos ?_
  unfold Host.v Host.rdE
  have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))
  have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
  linarith

theorem hsNormSq_amp_doubleCoset : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (A : LocS W), GoodW D τ w w' θ W → 0 < Tr D w → 0 < Tr D w' → IsSPsiEquiv W.z (psiS D W.z) W.π A.Φ → IsSPsiEquiv W.z' (psiS D W.z') W.π' A.Φ' → ContinuousOn A.Φ (UH (Hpk D.R.k D.R.rS)) → ContinuousOn A.Φ' (UH (Hpk D.R.k D.R.rS)) → ∀ (γ a a' : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (ν ν' : Measure (Mt D.R.k D.R.rS)), RelPt D W.z W.z' γ p → a ∈ Sset D.R.k D.R.rS W.z → a' ∈ Sset D.R.k D.R.rS W.z' → RMeas D W γ 1 ν → RMeas D W (a * γ * a'⁻¹) 1 ν' → hsNormSq (A.J ν' (a * γ * a'⁻¹)) = hsNormSq (A.J ν γ) := by
  rintro D τ w w' θ W A ⟨t1, t2, hz, hz', hT, hT', hG, -⟩ hw hw' hΦ hΦ' cΦ cΦ' γ a a' p ν ν' ⟨hγ, -, hGf⟩ ha ha'
    ⟨q, μ, hμ, hν⟩ ⟨q', μ', hμ', hν'⟩
  rw [← hT] at hw
  rw [← hT'] at hw'
  rw [ENNReal.ofReal_one, one_smul] at hν
  obtain ⟨s1, -⟩ := isClosedSub_Sset hz hw
  obtain ⟨s1', -, -, -, si'⟩ := isClosedSub_Sset hz' hw'
  obtain ⟨-, -, -, gm, gi⟩ := isClosedSub_GG (k := D.R.k) (r := D.R.rS)
  have hγ' : a * γ * a'⁻¹ ∈ GG D.R.k D.R.rS := gm _ (gm _ (s1 ha) _ hγ) _ (gi _ (s1' ha'))
  have hGf' : Gf D.R.k D.R.rS W.z W.z' (a * γ * a'⁻¹) ≠ 0 := by
    rwa [group_inverse_holds _ _ _ _ hz hz' a ha _ (si' _ ha') γ]
  have hπ := (GlobalTheory.Amp.Schur.type_irred hw t1).2.1
  have hπ' := (GlobalTheory.Amp.Schur.type_irred hw' t2).2.1
  have hψ : ∀ n, ‖psiS D W.z n‖ = 1 := (GlobalTheory.BesselPsi.psi_character _ _ _ _ hz).1
  have hψ' : ∀ n, ‖psiS D W.z' n‖ = 1 := (GlobalTheory.BesselPsi.psi_character _ _ _ _ hz').1
  have hH := (GlobalTheory.T.besselRootMeasure_independent_of_choices D W.z W.z' γ q q μ μ hz hz' hw hw' hγ hGf (ka_pos D) hμ hμ).2.2
  have hmv := GlobalTheory.T.rootMeasure_transport_doubleCoset D W.z W.z' q γ a a' μ hz hz' hw hw' hγ ha ha' hμ
  obtain ⟨-, e, hH'⟩ := GlobalTheory.T.besselRootMeasure_independent_of_choices D W.z W.z' _ q' q μ' _ hz hz' hw hw' hγ' hGf' (ka_pos D) hμ' hmv
  have hu := isUnit_det_of_mem_GG (s1' ha')
  have hq : IsQuotMeas W.μG μ' (ν.map (lmulM a')) := by
    rw [e]
    exact quot_translate hu (hG.2.2.2 _ (s1' ha')) hν
  have hrel : ∀ ρ ∈ Rset D.R.k D.R.rS (a * γ * a'⁻¹),
      psiS D W.z (a * γ * a'⁻¹ * ρ * (a * γ * a'⁻¹)⁻¹) = psiS D W.z' ρ := by
    obtain ⟨n, hn, n', hn', g, e1, e2, -⟩ := hμ'
    rw [e1] at hγ' ⊢
    exact fun ρ hρ => psi_cell hz hz' _ hn hn' hγ' e2 hρ
  have key := GlobalTheory.T.besselAmplitude_eq_smul_of_rescaled_stabilizerHaar _ _ W.Wp W.Wq W.z W.z' _ _ W.π W.π' A.Φ A.Φ' A.cN hz hz' hw hw' hπ hπ'
    (fun n _ => ⟨hψ n, hψ' n⟩) hΦ hΦ' cΦ cΦ' _ W.μG μ' _ ν' 1 hγ' hrel hG hH' one_pos hq hν'
  rw [Complex.ofReal_one, one_smul] at key
  obtain ⟨U, hU⟩ := exists_isometry hπ hψ hΦ ha
  obtain ⟨V, hV⟩ := exists_isometry hπ' hψ' hΦ' ha'
  unfold LocS.J
  rw [← key]
  exact hsNormSq_ampJ_translate (ae_mem_of_quot (R := Rset D.R.k D.R.rS γ) (fun x hx => hx.1.1) hG hH hν) _ hγ hu U V hU hV

end GlobalTheory.AmpCoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariantStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (A : LocS W), GoodW D τ w w' θ W → 0 < Tr D w → 0 < Tr D w' → IsSPsiEquiv W.z (psiS D W.z) W.π A.Φ → IsSPsiEquiv W.z' (psiS D W.z') W.π' A.Φ' → ContinuousOn A.Φ (UH (Hpk D.R.k D.R.rS)) → ContinuousOn A.Φ' (UH (Hpk D.R.k D.R.rS)) → ∀ (γ a a' : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (ν ν' : Measure (Mt D.R.k D.R.rS)), RelPt D W.z W.z' γ p → a ∈ Sset D.R.k D.R.rS W.z → a' ∈ Sset D.R.k D.R.rS W.z' → RMeas D W γ 1 ν → RMeas D W (a * γ * a'⁻¹) 1 ν' → hsNormSq (A.J ν' (a * γ * a'⁻¹)) = hsNormSq (A.J ν γ) := by
  first | exact @GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | exact GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | (intros; apply GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegral
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpLoc

theorem hsNormSq_amp_loc : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  intro D X Y hF hI C hB u u' t s hs hG hr hGap τ μ ν hμ hq hroot
  have hW : ∀ τ', GoodW D τ' u u' 1 (locW C u u' τ') := fun τ' =>
    goodW_of C u u' τ' (Formalism.L2.SG.Pf.colsTypeTr C u τ') (Formalism.L2.SG.Pf.colsTypeTr C u' τ')
      (Formalism.L2.SG.Pf.zTr C u τ') (Formalism.L2.SG.Pf.zTr C u' τ') (Formalism.L2.SG.Pf.haarTr C τ')
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u' τ (s.pt.1 (vOf X τ)) ν
  have hR2 : RMeas D (locW C u u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) 1
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ)))) := by
    obtain ⟨p, hp⟩ := hroot
    refine ⟨p, _, hp, ?_⟩
    rw [ENNReal.ofReal_one, one_smul]
    exact GlobalTheory.T.quotientMeasure_besselModel_of_local_quotient D X 1 C τ (s.pt.1 (vOf X τ)) μ ν hμ hq
  obtain ⟨a, ha, a', ha', hga⟩ := GlobalTheory.T.real_point_term_and_lift_same_real_double_coset D X Y hF hI 1 C u u' t s hs τ
  have hR4 : RMeas D (locW C u u' τ) (gamR hI C t τ) 1 (nu1 hI C t τ) := by
    have h := GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u' hW t hG hr τ
    unfold nu1
    rw [dite_eq_left h]
    exact h.choose_spec
  obtain ⟨p0, hp0⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨hΦ, hΦ', hc, hc'⟩ := GlobalTheory.T.localRealData_functions_equivariant_continuous D X 1 C hB u u' τ hGap
  have h5 := GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant D τ u u' 1 (locW C u u' τ) (locS hB u u' τ) (hW τ)
    (Nat.cast_pos.2 (D.mem u).A.T_prime.pos) (Nat.cast_pos.2 (D.mem u').A.T_prime.pos) hΦ hΦ' hc hc'
    (gamR hI C t τ) a a' p0 (nu1 hI C t τ) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ))))
    hp0 ha ha' hR4 (by rw [← hga]; exact hR2)
  rw [← h5, ← hga, e1]
  exact Formalism.L2.SG.LoopTerm.hsNormSq_smul _ _

end GlobalTheory.AmpLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegralStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  first | exact @GlobalTheory.AmpLoc.hsNormSq_amp_loc | exact GlobalTheory.AmpLoc.hsNormSq_amp_loc | (intros; apply GlobalTheory.AmpLoc.hsNormSq_amp_loc <;> assumption)
end
