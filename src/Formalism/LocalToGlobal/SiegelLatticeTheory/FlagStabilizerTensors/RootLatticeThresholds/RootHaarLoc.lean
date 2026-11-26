module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.BigCellDensity
open scoped ComplexConjugate

namespace Formalism.L2.SG.Pf.RootHaarLoc

section rootG

variable {k0 r : ℕ} (zz : Fin (2 * r + (k0 + 1) + 1) → ℂ) {Wp' Wq' : Type} [NormedAddCommGroup Wp']
  [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
  (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r Wp' Wq') (hz : Ds.z = zz) (γ : Point ℂ (r + 1))
  {g : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r} (hg : g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) d)
include hz hg hd hZ

theorem rootCoords_psiG (y : (rootPat γ) → ℂ) :
    rootCoords (k0 + 1) r zz γ (Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) = y := by
  have hG := good_of Ds hg hd hZ
  have hs := (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg hd hG (Tinv γ y)).2
  funext p
  have hp := p.2
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have ha : p.1.1.val < r := by
    have h1 := p.1.2.isLt
    have h2 := Fin.lt_def.1 hp.1
    omega
  simp only [rootCoords, Equiv.apply_symm_apply]
  rw [flag_eq_uMap _ _ _ _ _ _ ha, ← hz, hs, Matrix.conjTranspose_apply]
  have hc := Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord (wPt γ) (Tinv γ y) (eRoot γ p)
  simp only [eRoot, Equiv.coe_fn_mk] at hc
  rw [hc]
  simp [Tinv, eRoot]

theorem psi_rootCoordsG (x : Mt (k0 + 1) r) (hx : Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g) :
    Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r zz γ x))) = x := by
  have hG := good_of Ds hg hd hZ
  have hu := Formalism.FourierDecayAlt.P.Dx2.Rad.u_eq_low Ds hg hd hG (ρ := Matrix.of x) hx
  have hphi : Formalism.FourierDecayAlt.P.Dx2.Rad.phi0 Ds (wPt γ) (Matrix.of.symm (Matrix.of x)) =
      Tinv γ (rootCoords (k0 + 1) r zz γ x) := by
    funext q
    have hb : q.1.2.val < r := by
      have h1 := q.1.1.isLt
      have h2 := Fin.lt_def.1 q.2.1
      omega
    simp only [Formalism.FourierDecayAlt.P.Dx2.Rad.phi0, Tinv, rootCoords, Equiv.apply_symm_apply, eRoot, Equiv.coe_fn_symm_mk]
    rw [flag_eq_uMap _ _ _ _ _ _ hb, hz]
  have hρ := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_unique Ds hg hd hG (Tinv γ (rootCoords (k0 + 1) r zz γ x)) hx
    (by rw [← hphi, ← hu, Matrix.conjTranspose_conjTranspose])
  rw [← hρ]
  rfl

theorem muR_map_rootG :
    (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)).map (rootCoords (k0 + 1) r zz γ) = volume := by
  have hG := good_of Ds hg hd hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg hd hG
  show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)).map _ = _
  rw [Measure.map_map (meas_rootCoords _ γ) hm]
  have e : (rootCoords (k0 + 1) r zz γ ∘ fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) = Tmap γ := by
    funext x
    have := rootCoords_psiG zz Ds hz γ hg hd hZ (Tmap γ x)
    rw [Tinv_Tmap] at this
    exact this
  rw [e]
  exact (Tmap_mp γ).map_eq

end rootG

theorem zhat_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hu : IsUnit g.det) (i a : Fin (r + 1)) :
    Formalism.QuantumDeterminants.Zhat k r z' z g⁻¹ i a = star (Zhat k r z z' g a i) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.conjTranspose_apply, Hpk, Fin.mk.injEq]
    split_ifs <;> first | (simp; done) | omega
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hu
  have hkey : (Hpk k r * g)ᴴ = Hpk k r * g⁻¹ := by
    rw [Matrix.conjTranspose_mul, hH]
    have h2 := congrArg (· * g⁻¹) hg'
    simp only [Matrix.mul_assoc, hgi, Matrix.mul_one] at h2
    exact h2
  unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hkey]
  generalize Hpk k r * g = M
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.star_dotProduct_star, star_star]

theorem locRootHaar (k r : ℕ) (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : g₀ ∈ UH (Hpk k r)) (hZ : Formalism.MainNotions.S.ZhatO k r z z' g₀ = ptMat p) :
    ∃ (μ₀ : Measure (Mt k r)) (c : ENNReal), Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.Rset k r g₀) μ₀ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
      μ₀.map (rootCoords k r z' p) = c • volume := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Ds, hDz, hDz'⟩ := Formalism.MainNotions.S.Pv.AmpDDPf.bsetting_of (k0 + 1) r hk z' z ⟨hz', hT'⟩ ⟨hz, hT⟩
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed (k0 + 1) r
  have hgG : g₀ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hg
  have hu : IsUnit g₀.det := hG.unit g₀ hgG
  have hgi : g₀⁻¹ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hG.inv_mem g₀ hgG
  set w := wPt p with hw
  let d : Fin (r + 1) → ℂ := fun a => (-1 : ℂ) ^ (r - (w a).val) * star (dPt p (w a))
  have hd : ∀ a, d a ≠ 0 := fun a => mul_ne_zero (pow_ne_zero _ (by norm_num)) (star_ne_zero.2 (dPt_ne p (w a)))
  have hmono : ptMat p = Formalism.FourierDecayAlt.C2.monoP w (dPt p) := by rw [← ptMatN_swap, ptMatN_mono]
  have hZ' : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g₀⁻¹ = Formalism.FourierDecayAlt.C2.monoP w d := by
    ext i a
    rw [hDz, hDz', zhat_inv z z' hg hu i a]
    have h1 := congrFun (congrFun hZ a) i
    unfold Formalism.MainNotions.S.ZhatO at h1
    have hs : ((-1 : ℂ) ^ (r - i.val)) * (-1 : ℂ) ^ (r - i.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have h2 : Formalism.QuantumDeterminants.Zhat (k0 + 1) r z z' g₀ a i = (-1 : ℂ) ^ (r - i.val) * ptMat p a i := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2, hmono]
    simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]
    by_cases hai : a = w i
    · have hia : i = w a := by rw [hai, wPt_invol]
      rw [if_pos hai, if_pos hia]
      simp only [d, star_mul', star_pow, star_neg, star_one]
      rw [← hia]
    · have hia : ¬ i = w a := fun h => hai (by rw [h, wPt_invol])
      rw [if_neg hai, if_neg hia, mul_zero, star_zero]
  have hH := Formalism.FourierDecayAlt.P.radial_measure_is_haar (k0 + 1) r ℂ ℂ Ds g₀⁻¹ w d hgi hd hZ'
  have hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset (k0 + 1) r g₀ := by
    ext x
    simp only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  refine ⟨Formalism.FourierDecayAlt.D.muR Ds g₀⁻¹ w, 1, ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hH, hH.ne_zero, ?_, ?_⟩, one_ne_zero,
    ENNReal.one_ne_top, ?_⟩
  · rw [← hset]; exact hH.conc
  · intro s hs; rw [← hset] at hs; exact hH.left s hs
  · rw [one_smul]
    exact muR_map_rootG z' Ds hDz p hgi hd hZ'

end Formalism.L2.SG.Pf.RootHaarLoc
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
noncomputable section

open scoped Classical
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LTL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lemmas

open scoped ComplexConjugate

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  first
  | exact inner_self_nonneg (𝕜 := ℂ) (x := A (stdOrthonormalBasis ℂ Wq i))
  | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; positivity)

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (c • A) = Complex.normSq c * hsNormSq A := by
  unfold hsNormSq hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, ← mul_assoc]
  rw [← Finset.mul_sum]
  first
  | rw [Complex.mul_conj]
  | rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.re_ofReal_mul]

theorem isQuotMeas_smul {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : IsQuotMeas μG μS ν) {c : ENNReal}
    (h0 : c ≠ 0) (hT : c ≠ ⊤) : IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf]
  simp only [MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  rw [MeasureTheory.lintegral_const_mul' c _ hT, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

theorem locJ_smul {k r : ℕ} {W : LocW k r} (A : LocS W) (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (c : ENNReal)
    (γ : MatKR k r) : A.J (c • ν) γ = ((c.toReal : ℝ) : ℂ) • A.J ν γ := by
  simp only [Formalism.MainNotions.S.LocS.J, Formalism.MainNotions.S.ampJ, MeasureTheory.integral_smul_measure]
  rw [Complex.coe_smul]
  exact smul_comm _ _ _

end Lemmas

section Tr

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem star_dot_conjT {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem hJ_smul_real {n : ℕ} (ε : Fin n → Bool) (r s : ℝ) (x y : Fin n → ℂ) :
    hJ ε ((r : ℂ) • x) ((s : ℂ) • y) = ((r * s : ℝ) : ℂ) * hJ ε x y := by
  simp only [hJ]
  simp [Matrix.mulVec_smul, smul_eq_mul]
  try push_cast
  try ring

theorem frS_pow (D : D7) (a : Fin (D.R.rS + 1)) (h : a.val < D.R.rS) :
    frS D ^ (D.R.rS - a.val) = ((rhoF D a : ℝ) : ℂ) := by
  have hk : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    have hpi := Real.pi_pos.ne'
    rcases eq_or_ne D.host.rdE 0 with h0 | h0
    · rw [h0]
      simp
    · field_simp
      try ring
  have hnn : 0 ≤ D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hc : ((D.R.rS - a.val : ℕ) : ℝ) = (D.R.rS : ℝ) - (a.val : ℝ) := by
    rw [Nat.cast_sub h.le]
  unfold frS rhoF
  rw [hk, ← hc, Real.rpow_neg hnn, Real.rpow_natCast, ← inv_pow]
  push_cast
  try ring

theorem rhoF_last (D : D7) : rhoF D (Fin.last D.R.rS) = 1 := by
  simp [rhoF, Fin.val_last]

theorem Q_fvec (u : D.what₂.Word) (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • rv X.B.I (vOf X τ) (X.crd ((X.Fu u).fvec a)) := by
  obtain ⟨_, hQQi, _, hEv⟩ := C.isT τ
  by_cases h : a.val < D.R.rS
  · have h1 := (hEv ⟨a.val, h⟩ ⟨a.val, h⟩ rfl).1
    have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    have h2 : (X.Fu u).fvec (Fin.castSucc ⟨a.val, h⟩) = X.eX ⟨a.val, h⟩ := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact congrFun (X.Fu_e u) _
    rw [← ha] at h2
    rw [h2, ← frS_pow D a h, Formalism.QuantumDeterminants.fvec, dite_eq_left h, Formalism.QuantumDeterminants.bvec, h1]
    rfl
  · have ha : a = Fin.last D.R.rS := Fin.ext (by have := a.isLt; simp; omega)
    subst ha
    have h3 : (X.Fu u).fvec (Fin.last D.R.rS) = X.zu u := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact X.flagZVector u
    rw [h3, rhoF_last, Formalism.QuantumDeterminants.fvec, dite_eq_right h]
    simp only [zB, Complex.ofReal_one, one_smul]
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rfl

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  exact D.eTau.nonempty

theorem trG_mem {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (H : Matrix (Fin m) (Fin m) ℂ) (hQQi : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (g : Formalism.REAL.UJ ε) :
    Formalism.L2.SG.RealObj.trG Q Qi g ∈ Formalism.QuantumDeterminants.UH H := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := by
    first
    | exact g.2
    | (unfold uMat; exact g.2)
    | simpa [uMat] using g.2
  have h1 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Qiᴴ * (Qᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Q * (Qi * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
  have h3 : ∀ X : Matrix (Fin n) (Fin m) ℂ,
      (uMat g)ᴴ * (Formalism.REAL.Jm ε * (uMat g * X)) = Formalism.REAL.Jm ε * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  show (Qi * uMat g * Q)ᴴ * H * (Qi * uMat g * Q) = H
  rw [← hH]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, h1, h2, h3]

theorem tz_zB (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) = ((Tu D u : ℕ) : ℝ) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hT' : (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) =
      -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [show X.zR u = X.crd (X.zu u) from rfl, Formalism.L2.SG.Pf.Level.toV_crd, X.zu_norm]
  have hι := Formalism.L2.SG.Pf.Level.iota_hE (X := X) (X.zR u) (X.zR u)
  rw [hT'] at hι
  have hJv := Formalism.L2.SG.Pf.Level.hJ_rv (X := X) (vOf X τ) (X.zR u) (X.zR u)
  rw [X.φ_eq, hι] at hJv
  simp only [hJ, map_neg, map_natCast] at hJv
  unfold Formalism.QuantumDeterminants.Tz zB Formalism.QuantumDeterminants.herm
  rw [← hH, Matrix.mulVec_mulVec,
    Matrix.mul_assoc ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (C.Q τ) (C.Qi τ), hQQi,
    Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec, hJv]
  simp [Tu]

end Tr

end Formalism.L2.SG.Pf.LTL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJoint
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def DFrameAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∃ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h'

def Parts.JointTensor (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ x : ∀ v, X.Vloc u' v,
      (X.piU u h⁻¹) ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.piU u' h' (X.tensU u' x))) =
        X.tensU u (fun v => P.eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
            ((P.eQ v).symm (x v))))

end Formalism.L2.SG.Pf.Carrier
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergy
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.Gam0 (P : Parts X u u') : ℝ :=
  Formalism.FourierDecayAlt.D.GamLev P.S.G.k P.S.G.r (Formalism.FourierDecayAlt.D.kapG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E))
    (Formalism.FourierDecayAlt.D.deG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0

def Parts.EnergyModel (P : Parts X u u') : Prop :=
  P.Built → (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace P.S P.T P.f P.χ v (P.L v) (P.j v) (P.lam v) P.c (P.Cm v) (P.σ v)) →
    ∀ v, Formalism.FourierDecayAlt.JCT.jvModel P.S P.j P.Cm v = (Formalism.FourierDecayAlt.B.normSq (P.T v).base (P.f v)).toReal / P.Gam0

def Parts.EnergyNorm (P : Parts X u u') (jn : ℝ) : Prop :=
  (∏ v, (Formalism.FourierDecayAlt.B.normSq (P.T v).base (P.f v)).toReal / P.Gam0) = jn

end Formalism.L2.SG.Pf.Carrier
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVtPtSome
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

variable {D : D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
  [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wq x)]

theorem ptSome_of (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (hr : S.G.r = D.R.rS) : PtSome S := by
  intro p hp
  have hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS p) (D.R.rS + 1) := by
    refine ⟨?_, ?_⟩
    · rw [show Formalism.L2.SG.DataInst.signPt D.R.rS p = Formalism.L2.SG.DataInst.signAux D.R.rS 1 p from rfl,
        Formalism.L2.SG.DataInst.sign_list_fst]
      have := hp.1
      unfold Formalism.FourierDecayAlt.TB.level at this
      rw [this, hr]
    · refine (Formalism.L2.SG.DataInst.sign_list_mem_nonzero D.R.rS 1 p).2 fun c hc => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
      exact hp.2 k hk
  refine ⟨(Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨Formalism.L2.SG.DataInst.signPt D.R.rS p, hL⟩, ?_⟩
  unfold Formalism.L2.SG.RealObj.ptOfL Formalism.L2.SG.DataInst.ptOfList
  rw [dite_eq_left hL]

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OneBesselTor
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.OBT

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.FrameBoundFromBesselTorus

section Defs

variable {k r : ℕ}

def coefH (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) :
    Mx k r → (L.Wq →L[ℂ] L.Wp) :=
  fun x => P.comp ((L.σ x).comp Q)

def IsKFinPair (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) : Prop :=
  (∀ w, IsKFinHpk (k := k) (r := r) L.σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) L.σ (ContinuousLinearMap.adjoint P x))

def HasBData (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Λ : ℂ)
    (Φ : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Ψ : Mx k r → Measure (PairSp k r) → (L.Wq →L[ℂ] L.Wp)) : Prop :=
  (∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb k * μ = Hb k → L.J F (bigCell k r c μ) = Λ • Φ (bigCell k r c μ)) ∧
    (∀ (γ : Point ℂ (r + 1)) (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
      Gpt (Tz k r L.z) (Tz k r L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR →
      IsOrbQuot L g μR ν → OrbInt L F g ν = Λ • Ψ g ν)

end Defs

def RankOneTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (κ₀ : ℝ),
    0 < κ₀ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
        ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    ∃ (Φ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
      (Ψ : Mx D.R.k D.R.rS → Measure (PairSp D.R.k D.R.rS) → (L.Wq →L[ℂ] L.Wp))
      (Λ₀ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℂ)
      (Λ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℝ → ℝ → ℂ),
      (∀ P Q, IsKFinPair L P Q → HasBData L (coefH L P Q) (Λ₀ P Q) Φ Ψ) ∧
      (∀ P Q (κ τ : ℝ), 0 < κ → 0 < τ → IsKFinPair L P Q →
        HasBData L (fun x => coefH L P Q (cj D.R.k D.R.rS κ τ x)) (Λ P Q κ τ) Φ Ψ) ∧
      (∀ (κ τ : ℝ), 0 < κ → 0 < τ → ∀ P Q, IsKFinPair L P Q → Λ₀ P Q ≠ 0 →
        ∃ P₁ Q₁, IsKFinPair L P₁ Q₁ ∧ Λ P₁ Q₁ κ τ ≠ 0)

section Zero

variable {k r : ℕ}

theorem isKFinHpk_zero (L : LocBessel k r) : IsKFinHpk (k := k) (r := r) L.σ (0 : L.Hs) := by
  exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx
    simp [hx]⟩

theorem J_zero (L : LocBessel k r) (g : Mx k r) : L.J (fun _ => 0) g = 0 := by
  simp [LocBessel.J, Formalism.QuantumDeterminants.besselJ]

theorem orbInt_zero (L : LocBessel k r) (g : Mx k r) (ν : Measure (PairSp k r)) :
    OrbInt L (fun _ => 0) g ν = 0 := by
  simp [OrbInt, besselIntg]

end Zero

theorem oneBesselTor_of_rankOne (D : D7) (Cgf : ℝ) (h : RankOneTor D Cgf) : OneBesselTor D Cgf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hN hN' hε hgap hf
  obtain ⟨Φ, Ψ, Λ₀, Λ, h1, h2, h3⟩ := h L κ₀ hκ₀ hc hN hN' hε hgap
  obtain ⟨P, Q, hQ, hP, hfPQ⟩ := hf
  have hfeq : f = coefH L P Q := funext fun g => hfPQ g
  subst hfeq
  have hPQ : IsKFinPair L P Q := ⟨hQ, hP⟩
  by_cases h0 : Λ₀ P Q = 0
  · refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun w => by simpa using isKFinHpk_zero L,
      fun x => by simpa using isKFinHpk_zero L, fun g => by simp⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      show L.J (fun _ => 0) _ = _
      rw [(h1 P Q hPQ).1 c μ hc0 hμ, h0, J_zero]
      simp
    · intro γ g μR ν hG hrep hst hroot hq
      show OrbInt L (fun _ => 0) g ν = _
      rw [(h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, h0, orbInt_zero]
      simp
  · obtain ⟨P₁, Q₁, hPQ₁, hΛ⟩ := h3 κ τ hκ hτ P Q hPQ h0
    refine ⟨coefH L P₁ Q₁, Λ P₁ Q₁ κ τ / Λ₀ P Q, div_ne_zero hΛ h0,
      ⟨P₁, Q₁, hPQ₁.1, hPQ₁.2, fun g => rfl⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).1 c μ hc0 hμ, (h1 P Q hPQ).1 c μ hc0 hμ, smul_smul,
        div_mul_cancel₀ _ h0]
    · intro γ g μR ν hG hrep hst hroot hq
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).2 γ g μR ν hG hrep hst hroot hq,
        (h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, smul_smul, div_mul_cancel₀ _ h0]

end Formalism.L2.SG.Pf.OBT
end
end
