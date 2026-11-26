module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntQ

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PRhoRw
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC

section twist

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

end twist

variable {k r : ℕ}

theorem uwset_inv {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  obtain ⟨h1, h2, h3⟩ := hh
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh h1
  have key : ∀ v, Matrix.mulVec h v = v → Matrix.mulVec h⁻¹ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1, fun a => ⟨key _ (h2 a).1, key _ (h2 a).2⟩, key _ h3⟩

section rho

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

end rho

end PI.UnitaryGroupMassFormula.JCC
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MuNcHaar
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntLoc
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntOm
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.EnergyIntOm

variable {D : D7} (X : HidaSetting D)

def dsc (lam : ℂ) (sc : ℝ) (a : Fin (D.R.rS + 1)) : ℂ := (lam * (sc : ℂ)) ^ (D.R.rS - a.val)

theorem dsc_ne {lam : ℂ} (hl : lam ≠ 0) {sc : ℝ} (hsc : sc ≠ 0) (a : Fin (D.R.rS + 1)) : dsc (D := D) lam sc a ≠ 0 := by
  unfold dsc
  exact pow_ne_zero _ (mul_ne_zero hl (by exact_mod_cast hsc))

theorem dsc_last (lam : ℂ) (sc : ℝ) : dsc (D := D) lam sc (Fin.last D.R.rS) = 1 := by
  unfold dsc
  simp

theorem q_fvec {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u : D.what₂.Word) (a : Fin (D.R.rS + 1)) :
    Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) a = dsc (D := D) lam sc a • frm X u sc v a := by
  obtain ⟨-, h2, -, h4⟩ := hQ
  have hsc' : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc
  induction a using Fin.lastCases with
  | last =>
    have hl : ¬ (Fin.last D.R.rS).val < D.R.rS := by simp
    unfold Formalism.QuantumDeterminants.fvec
    rw [dite_eq_right hl, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, dsc_last, one_smul]
    unfold frm famSc fam
    simp [Fin.snoc_last]
  | cast b =>
    have hb : (Fin.castSucc b).val < D.R.rS := b.isLt
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    rw [dite_eq_left hb]
    have hbb : (⟨(Fin.castSucc b).val, hb⟩ : Fin D.R.rS) = b := Fin.ext rfl
    rw [hbb, (h4 b b rfl).1]
    unfold dsc frm famSc fam
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc]
    rw [smul_smul, mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hsc'), mul_one]

theorem zhat_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) (trG Q Qi (γ v)) a b =
      star (dsc (D := D) lam sc a) * dsc (D := D) lam sc b * ZX X u u' sc γ v a b := by
  obtain ⟨-, h2, h3, -⟩ := id hQ
  have ea := q_fvec X hQ hsc u a
  have eb := q_fvec X hQ hsc u' b
  unfold ZX Formalism.QuantumDeterminants.Zhat trG
  unfold Formalism.L2.SG.RealObj.Zhat
  beta_reduce
  unfold Formalism.QuantumDeterminants.herm Formalism.L2.SG.HidaSetting.hJ
  rw [← h3]
  have hm : Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q * (Qi * uMat (γ v) * Q) =
      Qᴴ * (Formalism.REAL.Jm (X.B.I.ε v) * (uMat (γ v) * Q)) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ea,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_smul, smul_eq_mul]
  ring

theorem dmin_diag (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (d : Fin (D.R.rS + 1) → ℂ)
    (h : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' g = Matrix.diagonal d) (l : Fin (D.R.rS + 2)) :
    Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' g l = ∏ i : Fin l.val, d (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Formalism.QuantumDeterminants.Dmin
  rw [h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  rfl

theorem mem_om {v : InfinitePlace X.B.I.F} {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : 0 < sc) (u u' : D.what₂.Word) (c : Cinf X) (hc : c ∈ Good X u u') (γ : X.B.I.Ginf)
    (hγ : HasDiag X u u' sc c γ) :
    trG Q Qi (γ v) ∈ Formalism.FourierDecayAlt.JF.Om D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) := by
  have hsc0 : sc ≠ 0 := hsc.ne'
  have hc' : ∀ w, (∀ l, c w l ≠ 0) ∧ 0 < Gv (Tw u) (Tw u') (Matrix.diagonal (c w)) := hc
  have hγ' : ∀ w, ZX X u u' sc γ w = Matrix.diagonal (c w) := hγ
  obtain ⟨dd, hdd⟩ : ∃ dd : Fin (D.R.rS + 1) → ℂ,
      dd = fun a => star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a * c v a := ⟨_, rfl⟩
  have hdiag : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
      (trG Q Qi (γ v)) = Matrix.diagonal dd := by
    ext a b
    rw [zhat_tr X hQ hsc0 u u' γ a b, hγ' v, hdd]
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hdsc : ∀ a, star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a ≠ 0 := fun a =>
    mul_ne_zero (star_ne_zero.mpr (dsc_ne (D := D) hl hsc0 a)) (dsc_ne (D := D) hl hsc0 a)
  have hd0 : ∀ a, dd a ≠ 0 := by
    intro a
    rw [hdd]
    exact mul_ne_zero (hdsc a) ((hc' v).1 a)
  have hDmin := fun l => dmin_diag (D := D) _ _ _ _ hdiag l
  have hTz : ∀ w : D.what₂.Word, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR w)) = Tw w := by
    intro w
    have hQz : Q *ᵥ (Qi *ᵥ rv X.B.I v (X.zR w)) = rv X.B.I v (X.zR w) := by
      rw [Matrix.mulVec_mulVec, hQ.2.1, Matrix.one_mulVec]
    have hJ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v w
    unfold Formalism.L2.SG.HidaSetting.hJ at hJ
    unfold Formalism.QuantumDeterminants.Tz Formalism.QuantumDeterminants.herm
    rw [← hQ.2.2.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Formalism.L2.SG.Pf.LTL.star_dot_conjT, hQz, hJ]
    simp
  unfold Formalism.FourierDecayAlt.JF.Om
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem Q Qi _ hQ.2.1 hQ.2.2.1 (γ v), ?_⟩
  rw [Formalism.FourierDecayAlt.Q.OmPlus, Set.mem_ofPred_eq]
  refine ⟨fun l _ => ?_, ?_⟩
  · rw [hDmin l]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
  · have hlast : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) (Fin.last (D.R.rS + 1)) =
        (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := by
      rw [hDmin]
      have h : ∏ i : Fin (D.R.rS + 1), dd i =
          (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := Fin.prod_univ_castSucc _
      exact h
    have hr : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) ⟨D.R.rS, by omega⟩ = ∏ i : Fin D.R.rS, dd (Fin.castSucc i) := by
      rw [hDmin]
      rfl
    have hsplit : ∏ i : Fin D.R.rS, dd (Fin.castSucc i) =
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) *
          ∏ i : Fin D.R.rS, c v (Fin.castSucc i) := by
      rw [hdd, ← Finset.prod_mul_distrib]
    have hlastd : dd (Fin.last D.R.rS) = c v (Fin.last D.R.rS) := by
      rw [hdd]
      simp [dsc_last]
    have hG := (hc' v).2
    unfold Gv at hG
    rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_last, Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_r,
      Complex.sq_norm, Complex.sq_norm] at hG
    have hE : 0 < Complex.normSq
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) :=
      Complex.normSq_pos.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hdsc _)
    unfold Formalism.QuantumDeterminants.Gf
    rw [hlast, hr, hTz u, hTz u', hsplit, hlastd]
    simp only [Complex.normSq_mul] at hG ⊢
    nlinarith [mul_pos hE hG]

end Formalism.L2.SG.RealObj.EnergyIntOm
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ConjEApply
noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

theorem cont_conj (A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous fun x : Mt k r => (fun i j => (A * Matrix.of x * B) i j : Mt k r) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply_apply i j).comp ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

def conjE {μ : ℂ} (hμ : μ ≠ 0) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (torS μ⁻¹ k r * Matrix.of x * torS μ k r) i j
  invFun x := fun i j => (torS μ k r * Matrix.of x * torS μ⁻¹ k r) i j
  left_inv x := by
    funext i j
    show (torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r) i j = x i j
    rw [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  right_inv x := by
    funext i j
    show (torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r) i j = x i j
    rw [show torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r =
      (torS μ⁻¹ k r * torS μ k r) * Matrix.of x * (torS μ⁻¹ k r * torS μ k r) by simp only [Matrix.mul_assoc],
      torS_inv_mul μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  measurable_toFun := (cont_conj _ _).measurable
  measurable_invFun := (cont_conj _ _).measurable

theorem conjE_apply {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) = torS μ⁻¹ k r * Matrix.of x * torS μ k r := rfl

theorem conjE_mem_N {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) ∈ Nset k r ↔ Matrix.of x ∈ Nset k r := by
  rw [conjE_apply]
  constructor
  · intro h
    have := tor_conj_N hμ h
    rwa [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one] at this
  · intro h
    have := tor_conj_N (inv_ne_zero hμ) h
    rwa [inv_inv] at this

theorem haarN_tor {μ : ℂ} (hμ : μ ≠ 0) {μN : Measure (Mt k r)} (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) :
    Formalism.MainNotions.S.IsHaarOn (Nset k r) (μN.map (conjE hμ)) := by
  obtain ⟨hsf, hne, hconc, hleft⟩ := hN
  refine ⟨(conjE hμ).sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h0
    apply hne
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h1
    rw [MeasurableEquiv.map_apply, Set.preimage_univ] at h1
    exact Measure.measure_univ_eq_zero.mp h1
  · rw [MeasurableEquiv.map_apply]
    have e : (conjE (k := k) (r := r) hμ) ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} =
        {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq, conjE_mem_N]
    rw [e]; exact hconc
  · have hs' : torS μ k r * s * torS μ⁻¹ k r ∈ Nset k r := tor_conj_N hμ hs
    have hmeas : Measurable (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    have hmeas' : Measurable (lmulM (k := k) (r := r) (torS μ k r * s * torS μ⁻¹ k r)) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    rw [Measure.map_map hmeas (conjE hμ).measurable]
    have e : lmulM (k := k) (r := r) s ∘ (conjE hμ) = (conjE hμ) ∘ lmulM (torS μ k r * s * torS μ⁻¹ k r) := by
      funext x
      simp only [Function.comp_apply]
      change (s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        (torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      calc s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r)
          = (torS μ⁻¹ k r * torS μ k r) * s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) := by
            rw [torS_inv_mul μ hμ, Matrix.one_mul]
        _ = torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r := by
            simp only [Matrix.mul_assoc]
    rw [e, ← Measure.map_map (conjE hμ).measurable hmeas', hleft _ hs']

theorem be_tor {μ : ℂ} (hμ : μ ≠ 0) {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (π π' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (σ σ' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H))
    (hσ : ∀ m, σ' m = σ (torS μ k r * m * torS μ⁻¹ k r)) (hπ : ∀ h ∈ UWset k r z, π' h = π h)
    (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hW : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0) (x y : H) :
    Formalism.FourierDecayAlt.ThreeDimData.be z (c * μ) π' σ' μW (μN.map (conjE hμ)) x y = Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN x y := by
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  have : SigmaFinite (μN.map (conjE hμ)) := (conjE hμ).sigmaFinite_map
  have e : (μW.prod μN).map (Prod.map id (conjE hμ)) = μW.prod (μN.map (conjE hμ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (conjE hμ).measurable, Measure.map_id]
  have hme : MeasurableEmbedding (Prod.map id (conjE (k := k) (r := r) hμ)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Mt k r)) (conjE hμ)).measurableEmbedding
  rw [← e, hme.integral_map]
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p; simp
    rw [es, Measure.prod_prod, hW, zero_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with p hp
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [Prod.map, id]
  have h1 : σ' (Matrix.of p.1 * Matrix.of (conjE hμ p.2)) = σ (Matrix.of p.1 * Matrix.of p.2) := by
    rw [hσ, conjE_apply]
    congr 1
    calc torS μ k r * (Matrix.of p.1 * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r)) * torS μ⁻¹ k r
        = (torS μ k r * Matrix.of p.1 * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.1 * Matrix.of p.2 := by rw [tor_conj_uw hμ hp, torS_mul_inv μ hμ, Matrix.mul_one]
  have h2 : psi k r z (c * μ) (Matrix.of (conjE hμ p.2)) = psi k r z c (Matrix.of p.2) := by
    rw [← psi_tor hμ hz c, conjE_apply]
    congr 1
    calc torS μ k r * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r) * torS μ⁻¹ k r
        = (torS μ k r * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.2 := by rw [torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
  have h3 : π' (Matrix.of p.1)⁻¹ = π (Matrix.of p.1)⁻¹ := hπ _ (PI.UnitaryGroupMassFormula.JCC.uwset_inv hp)
  rw [h1, h2, h3]

end Formalism.L2.SG.RealObj.EnergyIntTor
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem scale_eq (D : D7) : Formalism.L2.SG.Pf.WuBL.cS D * muT D = Formalism.QuantumDeterminants.cStd := by
  have h1 := Formalism.L2.SG.Pf.WuBL.cS_ne D
  unfold Formalism.L2.SG.Pf.WuBL.cS at h1
  have hka : D.host.ka ≠ 0 := by rintro h; apply h1; simp [h]
  have hg : ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≠ 0 := by intro h; apply h1; simp [h]
  have hg0 : (D.host.g 0 : ℂ) ≠ 0 := by
    have := (mul_ne_zero_iff.1 hg).1; exact_mod_cast this
  have hg1 : (D.host.g 1 : ℂ) ≠ 0 := by
    have := (mul_ne_zero_iff.1 hg).2; exact_mod_cast this
  have hka' : (D.host.ka : ℂ) ≠ 0 := by exact_mod_cast hka
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold Formalism.L2.SG.Pf.WuBL.cS muT cfS frS Formalism.QuantumDeterminants.cStd
  push_cast
  field_simp

theorem transpC' (C : Choice X θ) (τ : D.what₂.Tau) :
    IsTranspC X (vOf X τ) (cfS D) D.R.k D.R.rS (Qcs C τ) (Qics C τ) :=
  Formalism.L2.SG.Pf.torTie X _ _ _ (C.isT τ)

theorem zc_eq (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Qics C τ *ᵥ rv X.B.I (vOf X τ) (X.zR u) = zB X (C.Qi τ) u τ := by
  have hw := (Formalism.L2.SG.Pf.zTr C u τ).1
  unfold Qics
  rw [← Matrix.mulVec_mulVec]
  change torS (muT D)⁻¹ D.R.k D.R.rS *ᵥ zB X (C.Qi τ) u τ = zB X (C.Qi τ) u τ
  funext i
  simp only [torS, Matrix.mulVec_diagonal]
  split_ifs with h1 h2
  · rw [hw i (Or.inl h1), mul_zero]
  · rw [hw i (Or.inr h2), mul_zero]
  · rw [one_mul]

theorem sigC_eq (C : Choice X θ) (τ : D.what₂.Tau) (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    sigB X (Qcs C τ) (Qics C τ) τ m =
      sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * m * torS (muT D)⁻¹ D.R.k D.R.rS) := by
  unfold sigB Qcs Qics
  simp only [Matrix.mul_assoc]

theorem piC_eq (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau)
    {h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hh : h ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    piB X (Qcs C τ) (Qics C τ) u τ h = piB X (C.Q τ) (C.Qi τ) u τ h := by
  unfold piB Qcs Qics
  have e : C.Q τ * torS (muT D) D.R.k D.R.rS * h * (torS (muT D)⁻¹ D.R.k D.R.rS * C.Qi τ)
      = C.Q τ * (torS (muT D) D.R.k D.R.rS * h * torS (muT D)⁻¹ D.R.k D.R.rS) * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, tor_conj_uw (Formalism.L2.SG.Pf.muT_ne D) hh]

theorem inUJ_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : Formalism.REAL.inUJ (X.B.I.ε v) (Q * m * Qi) := by
  obtain ⟨h1, h2, h3, -⟩ := hQ
  unfold Formalism.REAL.inUJ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  have hJ : Formalism.REAL.Jm (X.B.I.ε v) = Qiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Qi := by
    rw [← h3]
    calc Formalism.REAL.Jm (X.B.I.ε v) = (Q * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * Qi) := by
          rw [h2]; simp
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi)
      = Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * m) * Qi := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [h3, hm', hJ]

private theorem conj_mem_lemma (D : D7)
    {a : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hμ := Formalism.L2.SG.Pf.muT_ne D
  have g1 := Formalism.L2.SG.Pf.Choice.torS_gram (k := D.R.k) (r := D.R.rS) (muT D)⁻¹ (inv_ne_zero hμ)
  have g2 := Formalism.L2.SG.Pf.Choice.torS_gram (k := D.R.k) (r := D.R.rS) (muT D) hμ
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := ha
  show (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  calc (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)
      = (torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * (aᴴ * ((torS (muT D) D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS) * a) * torS (muT D)⁻¹ D.R.k D.R.rS := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [g2, ha', g1]

theorem sigC_mul (C : Choice X θ) (τ : D.what₂.Tau)
    {a b : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS))
    (x : X.B.H (vOf X τ)) :
    sigB X (Qcs C τ) (Qics C τ) τ a (sigB X (Qcs C τ) (Qics C τ) τ b x) = sigB X (Qcs C τ) (Qics C τ) τ (a * b) x := by
  rw [sigC_eq, sigC_eq, sigC_eq]
  have hrep := (Formalism.L2.SG.Pf.WuBL.sigB_rep C τ).1.2 _ (conj_mem_lemma D ha) _ (conj_mem_lemma D hb)
  have hi := Formalism.L2.SG.Pf.Choice.torS_inv_mul (k := D.R.k) (r := D.R.rS) (muT D) (Formalism.L2.SG.Pf.muT_ne D)
  have e : torS (muT D) D.R.k D.R.rS * (a * b) * torS (muT D)⁻¹ D.R.k D.R.rS = (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) * (torS (muT D) D.R.k D.R.rS * b * torS (muT D)⁻¹ D.R.k D.R.rS) := by
    calc torS (muT D) D.R.k D.R.rS * (a * b) * torS (muT D)⁻¹ D.R.k D.R.rS
        = torS (muT D) D.R.k D.R.rS * a * (torS (muT D)⁻¹ D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS) * b * torS (muT D)⁻¹ D.R.k D.R.rS := by
          rw [hi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) * (torS (muT D) D.R.k D.R.rS * b * torS (muT D)⁻¹ D.R.k D.R.rS) := by simp only [Matrix.mul_assoc]
  rw [e, hrep]
  rfl

theorem sigC_norm (C : Choice X θ) (τ : D.what₂.Tau)
    {a : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (x : X.B.H (vOf X τ)) :
    ‖sigB X (Qcs C τ) (Qics C τ) τ a x‖ = ‖x‖ := by
  rw [sigC_eq]
  exact (Formalism.L2.SG.Pf.WuBL.sigB_rep C τ).2 _ (conj_mem_lemma D ha) x

private theorem mul_mem_UH_Hpk' (D : D7) {a b : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * b = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (a * b) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [ha', hb']

theorem dd_sub (C : Choice X θ) (τ : D.what₂.Tau)
    {yc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hyc : yc ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (Qcs C τ) (Qics C τ) τ) (sigB X (Qcs C τ) (Qics C τ) τ yc (X.B.w (vOf X τ))) ≤
      Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) := by
  have hy := C.y_mem τ
  obtain ⟨hyi, -, hyy⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hrep := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  unfold Formalism.FourierDecayAlt.ThreeDimData.DDsp
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  beta_reduce
  rw [sigC_mul C τ hg hyc, sigC_eq]
  have hg'm : torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := conj_mem_lemma D (mul_mem_UH_Hpk' D hg hyc)
  have e : sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS * (C.y τ)⁻¹) (v0Of C τ)
      = sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS) (X.B.w (vOf X τ)) := by
    unfold v0Of
    rw [← ContinuousLinearMap.comp_apply, ← hrep.1.2 _ (mul_mem_UH_Hpk' D hg'm hyi) _ hy,
      Matrix.mul_assoc, hyy, Matrix.mul_one]
  rw [← e]
  exact Submodule.subset_span ⟨_, mul_mem_UH_Hpk' D hg'm hyi, rfl⟩

end Formalism.L2.SG.RealObj.EnergyIntLoc
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem cStd_ne : Formalism.QuantumDeterminants.cStd ≠ 0 := by
  simp [Formalism.QuantumDeterminants.cStd]

theorem muNc_haar (hθ : 0 < θ) :
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) ((muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) :=
  haarN_tor (Formalism.L2.SG.Pf.muT_ne D)
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (Formalism.L2.SG.Pf.Choice.kapN_ne_zero D hθ) ENNReal.ofReal_ne_top)

theorem hty_c (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ) := by
  have h := Formalism.L2.SG.Pf.Choice.colsTypeTr_of X (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) u
  rw [zc_eq] at h
  rw [show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h
  exact h

theorem zT (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧ 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  refine ⟨(Formalism.L2.SG.Pf.zTr C u τ).1, ?_⟩
  rw [(Formalism.L2.SG.Pf.zTr C u τ).2]
  exact Formalism.L2.SG.Pf.Choice.Tr_pos D u

def Dc (C : Choice X θ) (hθ : 0 < θ) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.FourierDecayAlt.B.RealPlaceData D.R.k D.R.rS (X.Vloc u (vOf X τ)) (X.Vloc u' (vOf X τ)) where
  z := zB X (C.Qi τ) u τ
  z' := zB X (C.Qi τ) u' τ
  π := piB X (Qcs C τ) (Qics C τ) u τ
  π' := piB X (Qcs C τ) (Qics C τ) u' τ
  μG := muGB X (Qcs C τ) (Qics C τ) τ
  μW := C.muW u τ
  μN := (muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))
  μW' := C.muW u' τ
  μsec := (Formalism.L2.SG.Pf.BaseOf.sec_exists (Formalism.L2.SG.Pf.BaseOf.k_pos D) _ _ (zT C u τ).2 (zT C u' τ).2
    (let ⟨g, hg, _⟩ := hty_c C u τ; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := hty_c C u' τ; ⟨g, hg⟩)).choose
  χ := Formalism.FourierDecayAlt.P.character_exists_alt.choose
  k_pos := Formalism.L2.SG.Pf.BaseOf.k_pos D
  z_mem := (zT C u τ).1
  z'_mem := (zT C u' τ).1
  T_pos := (zT C u τ).2
  T'_pos := (zT C u' τ).2
  π_rep := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).1
  π'_rep := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).1
  π_unitary := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).2.1
  π'_unitary := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).2.1
  π_cont := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u τ).1 (zT C u τ).2 (hty_c C u τ)).2.2
  π'_cont := (Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved _ _ _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (hty_c C u' τ)).2.2
  haarG := Formalism.L2.SG.Pf.BaseOf.haarG_B (n_eq' X) (X.B.I.ε (vOf X τ)) (transpC' C τ).2.1 (transpC' C τ).2.2.1
  haarW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ)
  haarN := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (muNc_haar hθ)
  haarW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u' τ).1 (zT C u' τ).2 (C.muW_haar u' τ)
  sec := (Formalism.L2.SG.Pf.BaseOf.sec_exists (Formalism.L2.SG.Pf.BaseOf.k_pos D) _ _ (zT C u τ).2 (zT C u' τ).2
    (let ⟨g, hg, _⟩ := hty_c C u τ; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := hty_c C u' τ; ⟨g, hg⟩)).choose_spec
  χ_smooth := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.1
  χ_supp := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.1
  χ_int := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.2

theorem sideC (C : Choice X θ) (hθ : 0 < θ) (u : D.what₂.Word) (τ : D.what₂.Tau) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h)
    {w0 : X.B.H (vOf X τ)} (hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) w0) :
    ∃ νq, Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (Qcs C τ) (Qics C τ) τ) w0
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
  obtain ⟨νq, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists _ _ _ hz hT _ _ hμG
    (isHaarOn_muS_gen hz hT (C.muW_haar u τ) (C.muW_one u τ) (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  exact ⟨νq, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, hDS, hgap, hok, hlow, hz, hT, cStd_ne, hty_c C u τ,
    C.muW_haar u τ, hμN, hμG, hq⟩

end Formalism.L2.SG.RealObj.EnergyIntLoc
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

variable {k r : ℕ}

def rmulE (b bi : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hb : b * bi = 1) (hbi : bi * b = 1) :
    Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun := Formalism.FourierDecayAlt.B.rmulF b
  invFun := Formalism.FourierDecayAlt.B.rmulF bi
  left_inv x := by
    show Matrix.of x * b * bi = x
    rw [Matrix.mul_assoc, hb, Matrix.mul_one]; rfl
  right_inv x := by
    show Matrix.of x * bi * b = x
    rw [Matrix.mul_assoc, hbi, Matrix.mul_one]; rfl
  measurable_toFun := by
    have h := (cont_conj (k := k) (r := r) 1 b).measurable
    convert h using 1
    funext x i j
    simp [Formalism.FourierDecayAlt.B.rmulF]
  measurable_invFun := by
    have h := (cont_conj (k := k) (r := r) 1 bi).measurable
    convert h using 1
    funext x i j
    simp [Formalism.FourierDecayAlt.B.rmulF]

theorem rmulE_coe (b bi : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hb : b * bi = 1)
    (hbi : bi * b = 1) : ⇑(rmulE (k := k) (r := r) b bi hb hbi) = Formalism.FourierDecayAlt.B.rmulF b := rfl

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem uMat_inv_mul' {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  rw [← uMat_mul', inv_mul_cancel]; rfl


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem locOrbG_of (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C) :
    Formalism.L2.SG.RealObj.EnergyInt.LocOrbG := by
  intro D hG X u u' sc hsc c hc γ hγ v
  obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, (X.pl.symm_apply_apply v).symm⟩
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨l, a, hbe, hW⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u τ
  obtain ⟨l', a', hbe', hW'⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u' τ
  have h1 := (transpC' C τ).1
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  obtain ⟨yc, hyc, hycl⟩ := y_exists (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
    (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
    (X.B.lam (vOf X τ)) (lamD D τ)
    (fun i => by
      rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
      exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
    (X.B.σ (vOf X τ)) (X.ds (vOf X τ)).2.2.1 (X.low (vOf X τ)).2 (Qcs C τ) (Qics C τ) h2 hg P hP
  set σc := sigB X (Qcs C τ) (Qics C τ) τ with hσc
  set w0 := σc yc (X.B.w (vOf X τ)) with hw0
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) σc w0 := by
    refine ⟨P, hP, ?_, hycl⟩
    rw [hw0, sigC_norm C τ hyc]
    exact (X.low (vOf X τ)).1
  obtain ⟨h, hgap, hok⟩ := hGp D hG τ
  obtain ⟨νq, hS⟩ := sideC C one_pos u τ hgap hok hlow
  obtain ⟨νq', hS'⟩ := sideC C one_pos u' τ hgap hok hlow
  have hμW := C.muW_haar u τ
  have hμW' := C.muW_haar u' τ
  have : SigmaFinite (C.muW u τ) := hμW.1
  have : SigmaFinite (C.muW u' τ) := hμW'.1
  have : SigmaFinite (muNB D 1) :=
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D one_pos) (kapN_ne_top D 1)).1

  have hl : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
      Formalism.FourierDecayAlt.ThreeDimData.be (Dc C one_pos u u' τ).z Formalism.QuantumDeterminants.cStd (Dc C one_pos u u' τ).π σc (Dc C one_pos u u' τ).μW
        (Dc C one_pos u u' τ).μN x y = (innerSL ℂ (l y)).smulRight (l x) := by
    intro x hx y hy
    show Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u τ) σc (C.muW u τ)
      ((muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) x y = _
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u τ)
      (piB X (Qcs C τ) (Qics C τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u τ hh) (C.muW u τ) (muNB D 1) hμW.2.2.1 x y]
    exact hbe x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)
  have hl' : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
      Formalism.FourierDecayAlt.ThreeDimData.be (Dc C one_pos u u' τ).z' Formalism.QuantumDeterminants.cStd (Dc C one_pos u u' τ).π' σc (Dc C one_pos u u' τ).μW'
        (Dc C one_pos u u' τ).μN x y = (innerSL ℂ (l' y)).smulRight (l' x) := by
    intro x hx y hy
    show Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u' τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u' τ) σc (C.muW u' τ)
      ((muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) x y = _
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u' τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u' τ)
      (piB X (Qcs C τ) (Qics C τ) u' τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u' τ hh) (C.muW u' τ) (muNB D 1) hμW'.2.2.1 x y]
    exact hbe' x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)

  set γc := Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) (γ (vOf X τ)) with hγc
  have hom := Formalism.L2.SG.RealObj.EnergyIntOm.mem_om X (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) hsc u u' c hc γ hγ
  rw [zc_eq, zc_eq] at hom
  have hint := Formalism.FourierDecayAlt.P.orbit_integral_convergence hI D.R.k D.R.rS _ _ (Dc C one_pos u u' τ) (epsSH D.R) (lamD D τ) h _ σc w0
    _ _ νq νq' hS hS' l l' hl hl' γc hom

  set μGc := muGB X (Qcs C τ) (Qics C τ) τ with hμGc
  set F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞ :=
    fun m => ‖l (σc (Matrix.of m) w0)‖ₑ * ‖l' (σc (γc⁻¹ * Matrix.of m) w0)‖ₑ with hF
  have hFfin : ∫⁻ m, F m ∂μGc < ⊤ := by
    have hfi := hint.2
    unfold HasFiniteIntegral at hfi
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun m => ?_)) hfi
    simp only [hF]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]
  clear_value F μGc

  obtain ⟨hyiU, hyi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem yc hyc
  set yi := Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * ycᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS with hyidef
  have hyi' : yc * yi = 1 := mul_eq_one_comm.mp hyi
  have hR : ∫⁻ m, F (Formalism.FourierDecayAlt.B.rmulF yi m) ∂μGc = ∫⁻ m, F m ∂μGc := by
    have hrm : μGc.map (Formalism.FourierDecayAlt.B.rmulF yi) = μGc := by
      rw [hμGc]
      exact (Formalism.L2.SG.Pf.BaseOf.haarG_B (n_eq' X) (X.B.I.ε (vOf X τ)) h2 hg).right yi hyiU
    rw [← rmulE_coe yi yc hyi hyi', ← lintegral_map_equiv F (rmulE yi yc hyi hyi'), rmulE_coe, hrm]

  have hTe : MeasurableEmbedding (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (vOf X τ)) h2).measurableEmbedding
  have hCV : ∫⁻ x, F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
      ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ m, F (Formalism.FourierDecayAlt.B.rmulF yi m) ∂μGc := by
    rw [hμGc]
    unfold muGB
    exact (hTe.lintegral_map (fun m => F (Formalism.FourierDecayAlt.B.rmulF yi m))).symm

  have key : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0 = X.B.σ (vOf X τ) (uMat x) (X.B.w (vOf X τ)) := by
    intro x
    have hTx := Formalism.L2.SG.Pf.LTL.trG_mem (Qcs C τ) (Qics C τ) _ h2 hg x
    rw [hw0, sigC_mul C τ (Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hTx hyiU) hyc, Matrix.mul_assoc, hyi, Matrix.mul_one]
    show X.B.σ (vOf X τ) (Qcs C τ * (Qics C τ * uMat x * Qcs C τ) * Qics C τ) (X.B.w (vOf X τ)) = _
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hγinv : γc⁻¹ = Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hγc]
    unfold Formalism.L2.SG.RealObj.trG
    calc Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ * (Qics C τ * uMat (γ (vOf X τ)) * Qcs C τ)
        = Qics C τ * (uMat (γ (vOf X τ))⁻¹ * (Qcs C τ * Qics C τ) * uMat (γ (vOf X τ))) * Qcs C τ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, uMat_inv_mul', Matrix.mul_one, h1]
  have hpt : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      ‖X.Wloc u (vOf X τ) x‖ₑ * ‖X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * x)‖ₑ =
        (‖a‖ₑ * ‖a'‖ₑ) * F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x))) := by
    intro x
    have e2 : γc⁻¹ * Matrix.of (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x))) =
        Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi := by
      show γc⁻¹ * (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) = _
      rw [hγinv]
      unfold Formalism.L2.SG.RealObj.trG
      rw [uMat_mul']
      calc Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ * (Qics C τ * uMat x * Qcs C τ * yi)
          = Qics C τ * uMat (γ (vOf X τ))⁻¹ * (Qcs C τ * Qics C τ) * uMat x * Qcs C τ * yi := by
            simp only [Matrix.mul_assoc]
        _ = Qics C τ * (uMat (γ (vOf X τ))⁻¹ * uMat x) * Qcs C τ * yi := by
            rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hW x, hW' ((γ (vOf X τ))⁻¹ * x), enorm_smul, enorm_smul, ← key x, ← key ((γ (vOf X τ))⁻¹ * x)]
    simp only [hF]
    rw [e2]
    show ‖a‖ₑ * ‖l (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0)‖ₑ *
        (‖a'‖ₑ * ‖l' (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi) w0)‖ₑ) =
      ‖a‖ₑ * ‖a'‖ₑ * (‖l (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0)‖ₑ *
        ‖l' (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi) w0)‖ₑ)
    ring
  calc ∫⁻ x, ‖X.Wloc u (vOf X τ) x‖ₑ * ‖X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * x)‖ₑ
        ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
      = ∫⁻ x, (‖a‖ₑ * ‖a'‖ₑ) *
          F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
          ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_congr hpt
    _ = (‖a‖ₑ * ‖a'‖ₑ) * ∫⁻ x,
          F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
          ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
    _ < ⊤ := by
        rw [hCV, hR]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hFfin


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem stepIntG_of (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C) :
    Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyInt.stepIntG_of_loc (locOrbG_of hI hRT hL2 hGp hLF)

end Formalism.L2.SG.RealObj.EnergyIntLoc
