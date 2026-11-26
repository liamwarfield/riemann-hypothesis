module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpNZTie
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomTie
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpTrans
open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpTrans

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem quot_meas_not_mem_UH_eq_zero {μG μS ν : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG) (hS0 : μS ≠ 0)
    (hSc : μS {x | Matrix.of x ∉ UH (Hpk k r)} = 0) (hq : IsQuotMeas μG μS ν) :
    ν {x | Matrix.of x ∉ UH (Hpk k r)} = 0 := by
  have hA : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
    have hc : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} := by
      apply isClosed_eq
      · exact ((Continuous.matrix_conjTranspose continuous_id).matrix_mul continuous_const).matrix_mul continuous_id
      · exact continuous_const
    exact hc.measurableSet
  have hN : MeasurableSet {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} := hA.compl
  have hint := hq ({x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}.indicator 1) (measurable_one.indicator hN)
  rw [lintegral_indicator_one hN, hG.2.2.1] at hint
  have hmass : μS Set.univ ≠ 0 := fun h => hS0 (Measure.measure_univ_eq_zero.mp h)
  have hSc' : μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}ᶜ = 0 := hSc
  have hlow : ∀ x ∈ {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}, μS Set.univ ≤
      ∫⁻ s, {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x hx
    have hsub : ∀ s ∈ {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)},
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} := by
      intro s hs hsx
      apply hx
      have e1 : (Matrix.of s * Matrix.of x)ᴴ * Hpk k r * (Matrix.of s * Matrix.of x) = Hpk k r := hsx
      have e2 : (Matrix.of s)ᴴ * Hpk k r * Matrix.of s = Hpk k r := hs
      show (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r
      calc (Matrix.of x)ᴴ * Hpk k r * Matrix.of x
          = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Hpk k r * Matrix.of s) * Matrix.of x := by rw [e2]
        _ = (Matrix.of s * Matrix.of x)ᴴ * Hpk k r * (Matrix.of s * Matrix.of x) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Hpk k r := e1
    calc μS Set.univ = μS ({s : Mt k r | Matrix.of s ∈ UH (Hpk k r)} ∪ {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)} + μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}ᶜ :=
          measure_union_le _ _
      _ = μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)} := by rw [hSc', add_zero]
      _ = ∫⁻ s, {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}.indicator 1 s ∂μS := (lintegral_indicator_one hA).symm
      _ ≤ _ := lintegral_mono (fun s => by
            by_cases hs : s ∈ {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}
            · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hsub s hs)]; exact le_rfl
            · rw [Set.indicator_of_notMem hs]; exact zero_le)
  have hge : μS Set.univ * ν {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} ≤
      ∫⁻ x, ∫⁻ s, {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}.indicator 1
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν := by
    rw [← lintegral_indicator_const hN]
    exact lintegral_mono (fun x => by
      by_cases hx : x ∈ {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}
      · rw [Set.indicator_of_mem hx]; exact hlow x hx
      · rw [Set.indicator_of_notMem hx]; exact zero_le)
  rw [← hint] at hge
  rcases mul_eq_zero.mp (le_zero_iff.mp hge) with h | h
  · exact absurd h hmass
  · exact h

def lmulE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (a * Matrix.of x) i j
  invFun x := fun i j => (a⁻¹ * Matrix.of x) i j
  left_inv x := by
    funext i j
    show (a⁻¹ * (a * Matrix.of x)) i j = x i j
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]; rfl
  right_inv x := by
    funext i j
    show (a * (a⁻¹ * Matrix.of x)) i j = x i j
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]; rfl
  measurable_toFun := by
    apply Continuous.measurable
    exact continuous_pi fun i => continuous_pi fun j => (continuous_const.matrix_mul continuous_id).matrix_elem i j
  measurable_invFun := by
    apply Continuous.measurable
    exact continuous_pi fun i => continuous_pi fun j => (continuous_const.matrix_mul continuous_id).matrix_elem i j

def conjE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (a⁻¹ * Matrix.of x * a) i j
  invFun x := fun i j => (a * Matrix.of x * a⁻¹) i j
  left_inv x := by
    funext i j
    show (a * (a⁻¹ * Matrix.of x * a) * a⁻¹) i j = x i j
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]; rfl
  right_inv x := by
    funext i j
    show (a⁻¹ * (a * Matrix.of x * a⁻¹) * a) i j = x i j
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]; rfl
  measurable_toFun := Formalism.MainNotions.S.Pv.LemmaJ.measurable_conjL _ _
  measurable_invFun := Formalism.MainNotions.S.Pv.LemmaJ.measurable_conjL _ _

theorem quot_transport {μG μ₀ νR : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG)
    {n' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn' : n' ∈ UH (Hpk k r)) (θ' : ℝ)
    (hq : IsQuotMeas μG (ENNReal.ofReal θ' • μ₀.map (fun x => fun i j => (n'⁻¹ * Matrix.of x * n') i j)) νR) :
    IsQuotMeas μG μ₀ (ENNReal.ofReal θ' • νR.map (fun x => fun i j => (n' * Matrix.of x) i j)) := by
  intro f hf
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hn'' : n'ᴴ * Hpk k r * n' = Hpk k r := hn'
  have hleft : (Hpk k r * n'ᴴ * Hpk k r) * n' = 1 := by
    simp only [Matrix.mul_assoc] at hn'' ⊢
    rw [hn'', hH]
  have ha : IsUnit n'.det := Matrix.isUnit_det_of_left_inverse hleft
  have hc : ENNReal.ofReal θ' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinv : μG.map (lmulE n' ha) = μG := hG.2.2.2 n' hn'
  have hL : νR.map (fun x => fun i j => (n' * Matrix.of x) i j) = νR.map (lmulE n' ha) := rfl
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, f (lmulE n' ha x) ∂μG := by
        conv_lhs => rw [← hinv]
        exact lintegral_map_equiv _ _
    _ = ∫⁻ x, ∫⁻ s, f (lmulE n' ha (fun i j => (Matrix.of s * Matrix.of x) i j))
          ∂(ENNReal.ofReal θ' • μ₀.map (conjE n' ha)) ∂νR :=
        hq _ (hf.comp (lmulE n' ha).measurable)
    _ = ∫⁻ x, ENNReal.ofReal θ' * ∫⁻ s, f (lmulE n' ha
          (fun i j => (Matrix.of (conjE n' ha s) * Matrix.of x) i j)) ∂μ₀ ∂νR := by
        simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_map_equiv]
    _ = ENNReal.ofReal θ' * ∫⁻ x, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (lmulE n' ha x)) i j) ∂μ₀ ∂νR := by
        rw [lintegral_const_mul' _ _ hc]
        congr 1
        refine lintegral_congr (fun x => lintegral_congr (fun s => ?_))
        congr 1
        funext i j
        show (n' * (n'⁻¹ * Matrix.of s * n' * Matrix.of x)) i j = (Matrix.of s * (n' * Matrix.of x)) i j
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
    _ = _ := by
        rw [lintegral_smul_measure, smul_eq_mul, hL, lintegral_map_equiv]

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

theorem smulRight_smul_smul {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (a b : ℂ) (u : E) (v : F) :
    (innerSL ℂ (a • u)).smulRight (b • v) = (star a * b) • (innerSL ℂ u).smulRight v := by
  ext x
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_smul, smul_smul]
  congr 1
  have h1 : (innerSL ℂ (a • u)) x = star a * (innerSL ℂ u) x := by
    simp [inner_smul_left, Complex.star_def]
  rw [h1]
  ring

theorem amplitude_transport : Formalism.MainNotions.S.Pv.LemmaJ.AmpTransport := by
  intro D τ w w' θ W hW lam' A hA hT hT' n n' g₀ hn hn' hg₀ θ' hθ' μ₀ νR hμ₀ hq
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  refine ⟨quot_transport hG hn'.1 θ' hq, ?_⟩
  have hH : Hpk D.R.k D.R.rS * Hpk D.R.k D.R.rS = 1 := (hpkFacts D.R.k D.R.rS).2.1
  have hHdet : IsUnit (Hpk D.R.k D.R.rS).det := Matrix.isUnit_det_of_left_inverse hH
  have hUH := uHGroup _ (Hpk D.R.k D.R.rS) hHdet
  have hn'U : n' ∈ UH (Hpk D.R.k D.R.rS) := hn'.1
  have hnU : n ∈ UH (Hpk D.R.k D.R.rS) := hn.1
  have ha : IsUnit n'.det := (hUH.2.2 n' hn'U).1
  have hn'inv : n'⁻¹ ∈ UH (Hpk D.R.k D.R.rS) := (hUH.2.2 n' hn'U).2
  set μS := ENNReal.ofReal θ' • μ₀.map (fun x => fun i j => (n'⁻¹ * Matrix.of x * n') i j) with hμS
  have hS0 : μS ≠ 0 := by
    intro h0
    have h1 := hq (fun _ => 1) measurable_const
    rw [h0] at h1
    simp at h1
    exact hG.2.1 h1
  have hSc : μS {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 := by
    rw [hμS, Measure.smul_apply, smul_eq_mul,
      show (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = ⇑(conjE n' ha) from rfl,
      MeasurableEquiv.map_apply]
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ hμ₀)
    intro x hx hR
    apply hx
    have hxU : Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := hR.1.1
    show n'⁻¹ * Matrix.of x * n' ∈ UH (Hpk D.R.k D.R.rS)
    exact hUH.2.1 _ (hUH.2.1 _ hn'inv _ hxU) _ hn'U
  have hνUH : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) :=
    ae_iff.2 (quot_meas_not_mem_UH_eq_zero hG hS0 hSc hq)
  have hσ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hA.2.1
  have hv0 := hA.2.2.2.2.1
  have hπ1 : W.π 1 = 1 := (Formalism.MainNotions.LowestKTypeMultiplicity.rp_repOfHC _ _ _ _ _ _ hW.2.2.1
    (by rw [hW.2.2.2.2.1]; exact hT) hW.1).1.1
  have hπ'1 : W.π' 1 = 1 := (Formalism.MainNotions.LowestKTypeMultiplicity.rp_repOfHC _ _ _ _ _ _ hW.2.2.2.1
    (by rw [hW.2.2.2.2.2.1]; exact hT') hW.2.1).1.1
  have h1W : ∀ z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ,
      (1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) ∈
        UWset D.R.k D.R.rS z := by
    intro z
    exact ⟨hUH.1, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ (n * g) = psiS D W.z n • A.Φ g := by
    intro g hg
    have h2 := hA.2.2.1.2.2.1 1 (h1W W.z) n hn (A.σ g A.v0)
      (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv0 hg)
    rw [one_mul, hπ1, ContinuousLinearMap.one_apply] at h2
    simp only [LocS.Φ]
    rw [hσ.1.2 n hnU g hg, ContinuousLinearMap.comp_apply]
    exact h2
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' (n' * g) = psiS D W.z' n' • A.Φ' g := by
    intro g hg
    have h2 := hA.2.2.2.1.2.2.1 1 (h1W W.z') n' hn' (A.σ g A.v0)
      (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv0 hg)
    rw [one_mul, hπ'1, ContinuousLinearMap.one_apply] at h2
    simp only [LocS.Φ']
    rw [hσ.1.2 n' hn'U g hg, ContinuousLinearMap.comp_apply]
    exact h2
  set K : W.Wq →L[ℂ] W.Wp := ((A.cN : ℂ))⁻¹ • ∫ x, (innerSL ℂ (A.Φ' (Matrix.of x))).smulRight
    (A.Φ (g₀ * (n' * Matrix.of x))) ∂νR with hKdef
  have hL : A.J νR (n * g₀ * n') = psiS D W.z n • K := by
    simp only [LocS.J, ampJ, hKdef]
    rw [smul_comm (psiS D W.z n), ← integral_smul (psiS D W.z n)]
    congr 1
    refine integral_congr_ae (hνUH.mono fun x hx => ?_)
    simp only
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hΦ _ (hUH.2.1 _ hg₀ _ (hUH.2.1 _ hn'U _ hx))]
    have h := smulRight_smul_smul (1 : ℂ) (psiS D W.z n) (A.Φ' (Matrix.of x))
      (A.Φ (g₀ * (n' * Matrix.of x)))
    rw [one_smul, star_one, one_mul] at h
    exact h
  have hR : A.J (ENNReal.ofReal θ' • νR.map (fun x => fun i j => (n' * Matrix.of x) i j)) g₀ =
      ((θ' : ℂ) * star (psiS D W.z' n')) • K := by
    simp only [LocS.J, ampJ, hKdef]
    rw [integral_smul_measure,
      show (fun x : Mt D.R.k D.R.rS => fun i j => (n' * Matrix.of x) i j) = ⇑(lmulE n' ha) from rfl,
      integral_map_equiv, ENNReal.toReal_ofReal hθ'.le]
    have hI : ∫ x, (innerSL ℂ (A.Φ' (Matrix.of (lmulE n' ha x)))).smulRight
        (A.Φ (g₀ * Matrix.of (lmulE n' ha x))) ∂νR =
        star (psiS D W.z' n') • ∫ x, (innerSL ℂ (A.Φ' (Matrix.of x))).smulRight
          (A.Φ (g₀ * (n' * Matrix.of x))) ∂νR := by
      rw [← integral_smul (star (psiS D W.z' n'))]
      refine integral_congr_ae (hνUH.mono fun x hx => ?_)
      show (innerSL ℂ (A.Φ' (n' * Matrix.of x))).smulRight (A.Φ (g₀ * (n' * Matrix.of x))) = _
      rw [hΦ' _ hx]
      have h := smulRight_smul_smul (psiS D W.z' n') (1 : ℂ) (A.Φ' (Matrix.of x))
        (A.Φ (g₀ * (n' * Matrix.of x)))
      rw [one_smul, mul_one] at h
      exact h
    rw [hI, ← Complex.coe_smul]
    simp only [smul_smul]
    congr 1
    ring
  rw [hL, hR, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul (psiS D W.z n) K,
    Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul ((θ' : ℂ) * star (psiS D W.z' n')) K]
  have hψ : ‖psiS D W.z n‖ = 1 := by
    unfold psiS
    exact norm_psi _ _ _
  have hψ' : ‖(θ' : ℂ) * star (psiS D W.z' n')‖ = θ' := by
    have h1 : ‖psiS D W.z' n'‖ = 1 := by
      unfold psiS
      exact norm_psi _ _ _
    rw [norm_mul, norm_star, h1, mul_one, Complex.norm_real, Real.norm_of_nonneg hθ'.le]
  rw [hψ, hψ', ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_pow, one_mul, _root_.zpow_neg, zpow_ofNat, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

end Formalism.MainNotions.S.Pv.AmpTrans
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpNZFinal
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpFinal
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpCell
open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.AmpCell

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem one_mem_UW' (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem mem_S_of_N (z : Fin (2 * r + k + 1) → ℂ) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : n ∈ Sset k r z := ⟨1, one_mem_UW' z, n, hn, (one_mul n).symm⟩

def Ds (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem Ds_mul_Ds : Ds r * Ds r = 1 := by
  unfold Ds
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  norm_num

theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ZhatO k r z z' g = Zhat k r z z' g * Ds r := by
  ext a b
  simp only [Ds]
  rw [Matrix.mul_diagonal]
  simp only [ZhatO]
  ring

theorem inCell_of_rep {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') {n n' g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r)
    (hn' : n' ∈ Nset k r) {p : Point ℂ (r + 1)} (hZ : ZhatO k r z z' g₀ = ptMat p) :
    IsInCell (ZhatO k r z z' (n * g₀ * n')) p := by
  have hni : n⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hn
  have hE := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ n⁻¹ (mem_S_of_N z hni) n'
    (mem_S_of_N z' hn') g₀
  have hnn : (n⁻¹)⁻¹ = n := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hn.1)
  rw [hnn] at hE
  have hu := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z ⟨hz, hT⟩).1 n⁻¹ (mem_S_of_N z hni)).2.1
  have hu' := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' ⟨hz', hT'⟩).1 n' (mem_S_of_N z' hn')).2.1
  refine ⟨(Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ, Ds r * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r, fun i j => ⟨fun hij => ?_, fun hij => ?_⟩,
    fun i j => ⟨fun hij => ?_, fun hij => ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_apply, hu.1 j i hij, star_zero]
  · subst hij; rw [Matrix.conjTranspose_apply, hu.2 i, star_one]
  · unfold Ds; rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hu'.1 i j hij]; ring
  · subst hij; unfold Ds; rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hu'.2 i, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [zhatO_eq, hE, ← hZ, zhatO_eq]
    calc (Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ * Zhat k r z z' g₀ * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r
        = (Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ * (Zhat k r z z' g₀ * (Ds r * Ds r)) * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r := by
          rw [Ds_mul_Ds, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem zhat_monomial {z z' : Fin (2 * r + k + 1) → ℂ} {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hZ : ZhatO k r z z' g₀ = ptMat p) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Zhat k r z z' g₀) := by
  have hinv : Function.Involutive (Formalism.L2.SG.PtCell.pinv p) := Formalism.L2.SG.PtCell.pinv_pinv p
  refine ⟨hinv.toPerm _, fun a => (-1 : ℂ) ^ (r - a.val) * Formalism.L2.SG.PtCell.pval p.1 (Formalism.L2.SG.PtCell.pinv p a).val,
    fun a => mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Formalism.L2.SG.PtCell.pval_ne p.1 (fun b hb => (p.2.1 b hb).1) _ (by rw [p.2.2]; exact (Formalism.L2.SG.PtCell.pinv p a).isLt)),
    ?_⟩
  have hZ' : Zhat k r z z' g₀ = ptMat p * Ds r := by
    rw [← hZ, zhatO_eq, Matrix.mul_assoc, Ds_mul_Ds, Matrix.mul_one]
  rw [hZ', Formalism.L2.SG.PtCell.ptMat_eq_mono]
  ext i a
  rw [show Ds r = Matrix.diagonal (fun b : Fin (r + 1) => (-1 : ℂ) ^ (r - b.val)) from rfl, Matrix.mul_diagonal]
  simp only [Formalism.L2.SG.PtCell.mono, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, Function.Involutive.coe_toPerm]
  by_cases h : a = Formalism.L2.SG.PtCell.pinv p i
  · have h2 : i = Formalism.L2.SG.PtCell.pinv p a := by rw [h, hinv]
    rw [if_pos h]
    simp only [h2, if_true]
    ring
  · have h2 : ¬ i = Formalism.L2.SG.PtCell.pinv p a := fun e => h (by rw [e, hinv])
    rw [if_neg h]
    simp only [h2, if_false]
    ring

theorem cell_representation : Formalism.MainNotions.S.Pv.LemmaJ.CellRep := by
  intro D W γ p θ' νR hz hz' hT hT' hRel hνR
  obtain ⟨p', μR, ⟨n, hn, n', hn', g₀, hγ, hZ', μ₀, h0, h1, hμR⟩, hq⟩ := hνR
  have hcell := inCell_of_rep hz hz' hT hT' hn hn' hZ'
  rw [← hγ] at hcell
  have hpp : p = p' := Formalism.L2.SG.PtCell.isInCell_uniq hRel.2.1 hcell
  subst hpp
  have hnU : n ∈ UH (Hpk D.R.k D.R.rS) := hn.1
  have hn'U : n' ∈ UH (Hpk D.R.k D.R.rS) := hn'.1
  have hu := WeylGroupFacts.isUnit_of_uh hnU
  have hu' := WeylGroupFacts.isUnit_of_uh hn'U
  have hg₀ : g₀ = n⁻¹ * γ * n'⁻¹ := by
    rw [hγ]
    calc g₀ = (n⁻¹ * n) * g₀ * (n' * n'⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul, Matrix.mul_one]
      _ = n⁻¹ * (n * g₀ * n') * n'⁻¹ := by simp only [Matrix.mul_assoc]
  have hg₀U : g₀ ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [hg₀]
    exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hnU) hRel.1) (WeylGroupFacts.uh_inv hn'U)
  have hGeq : Gf D.R.k D.R.rS W.z W.z' γ = Gf D.R.k D.R.rS W.z W.z' g₀ := by
    rw [hγ]
    exact Formalism.QuantumDeterminants.gInv _ _ _ _ hz hz' n (mem_S_of_N _ hn) n' (mem_S_of_N _ hn') g₀
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' g₀ := by
    refine lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg _ _ _ _ hz hz' hT hT' g₀ hg₀U) (fun e => hRel.2.2 ?_)
    rw [hGeq, ← e]
  refine ⟨n, hn, n', hn', g₀, hγ, hg₀U, hZ', hG, zhat_monomial hZ', μ₀, h0, h1, ?_⟩
  rw [← hμR]
  exact hq

end Formalism.L2.S.Pv.AmpCell
end
end

namespace Formalism.L2.S.Pv.AmpFinal

open Formalism.MainNotions.S.Pv.LemmaJ

theorem rootCmp_of_parts (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt) : RootCmp :=
  rootCmp_of Formalism.L2.S.Pv.AmpCell.cell_representation Formalism.MainNotions.S.Pv.AmpTrans.amplitude_transport hRJ hRH hOQ hRA

theorem ampUnif_of_parts (hAO : AmpOrbU) (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt)
    (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of' hAO (rootCmp_of_parts hRJ hRH hOQ hRA) hNZ

end Formalism.L2.S.Pv.AmpFinal
end

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

def AmpOrbCoefDD : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl → ∀ (D : D7) (large₂ : SizeData₂ D),
    Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
      (A : LocS W) (hA : GoodS D (lamD D τ) A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (v v' : A.H) (l : W.Wp) (l' : W.Wq) (ξ : W.Wp) (ξ' : W.Wq) (κ : ℂ), κ ≠ 0 ∧
      v ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ ∧
      v' ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ ∧
      Formalism.FourierDecayAlt.ThreeDimData.be W.z (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').c W.π A.σ W.μW
                (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').μN v v = (innerSL ℂ l).smulRight l ∧
      Formalism.FourierDecayAlt.ThreeDimData.be W.z' (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').c W.π' A.σ W.μW'
                (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').μN v' v' = (innerSL ℂ l').smulRight l' ∧
      ⟪l, ξ⟫_ℂ ≠ 0 ∧ ⟪ξ', l'⟫_ℂ ≠ 0 ∧
      OrbEq D hW hA hT hT' (fun g => κ • Formalism.MainNotions.S.Pv.AmpDD.coefF (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT')
        v v' ξ ξ' g)

theorem ampNZCoef_of (hE : AmpOrbCoefDD) (hCI : Formalism.MainNotions.S.Pv.BetaCut.CoefInCC)
    (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) : AmpNZCoef := by
  intro Cg cb Cu cT CT C0
  obtain ⟨A1, B1, hE'⟩ := hE Cg cb Cu cT CT C0
  refine ⟨A1, max B1 1000, fun C' Cl hC' hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec => ?_⟩
  have hCl1 : B1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl2 : (1000 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨v, v', l, l', ξ, ξ', κ, hκ, hv, hv', hbe, hbe', hl, hl', hOrb⟩ :=
    hE' C' Cl hC' hCl1 D large₂ hH τ w w' hTT θ W hW A hA hT hT'
  refine ⟨_, hOrb, ?_⟩
  set L := toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT' with hLdef
  have hk2 : 2 ≤ D.R.k := by have := Formalism.MainNotions.BridgeLemma.five_le_k D; omega

  have hv0 : 0 < D.host.v := by
    unfold Host.v Host.rdE
    refine div_pos (Real.rpow_pos_of_pos (abs_pos.2 ?_) _) two_pos
    exact_mod_cast NumberField.discr_ne_zero D.host.E
  have hka0 : 0 < D.host.ka := by unfold Host.ka; exact div_pos Real.pi_pos hv0
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  set ka : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) with hka
  have hkapos : 0 < ka := by positivity
  have hc : L.c = ((2 * ka : ℝ) : ℂ) := by
    show (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) = _
    congr 1; rw [hka]; ring

  have hW' := hW
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hNq, hq, -⟩ := hW'
  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := by
    intro h0
    have hμN : W.μN = 0 := by rw [hNq, h0]; unfold haarLie; rw [zero_smul]
    have hS0 : muS W.μW W.μN = 0 := by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]
    have h1 := hq (fun _ => 1) measurable_const
    rw [hS0] at h1
    simp at h1
    exact hG.2.1 h1

  have hL1 : (1 : ℝ) ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) (le_of_lt large₂.sc.eps_pos)
  obtain ⟨-, hTie⟩ := Formalism.L2.S.Pv.Mom.paramTieG_of hH.1 0 (by rw [abs_zero, add_zero]; nlinarith)
  have hl0 : l1dist (lamD D τ) (lamD D τ) ≤ 0 * D.R.k * (D.R.m : ℝ) ^ 3 := by
    unfold l1dist; simp
  obtain ⟨h, hgap, hok⟩ := hTie τ (lamD D τ) hl0 (Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc τ))
  have hsm : jNorm2 L (fun g => κ • Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ' g) μsec =
      ENNReal.ofReal (‖κ‖ ^ 2) * jNorm2 L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') μsec :=
    Formalism.MainNotions.BesselShellMomentBounds.jNorm2_smul L κ _ μsec
  rw [hsm]
  refine mul_ne_zero (ENNReal.ofReal_pos.2 (pow_pos (norm_pos_iff.2 hκ) 2)).ne' ?_
  exact Formalism.L2.S.Pv.AmpNZTie.jNorm2_coef_ne' hk2 L ka hkapos hc hκ0 hκtop μsec hsec h hgap hok v v' hv hv'
    l l' ξ ξ' hbe hbe' hl hl' hCI hBI

theorem coefficients_in_compact_closure : Formalism.MainNotions.S.Pv.BetaCut.CoefInCC := by
  intro k r ε lam H _ _ _ σ h m A hlam hσ hgap hm hA v hv v' hv' Wp Wq _ _ _ _ ξ ξ'
  exact Formalism.L2.SG.Pf.CoefDecay.coefM_inCC hlam hgap m hm hA hσ hv hv' ξ ξ' 5

theorem ampNZ_of_parts (hE : AmpOrbCoefDD) (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) : AmpNZ :=
  ampNZ_of (ampNZCoef_of hE coefficients_in_compact_closure hBI)


end Formalism.MainNotions.S.Pv.LemmaJ
end
end

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.AmpOrbCoef

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf

theorem fdegH_pos {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    (hG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) {w : H} (hw : ‖w‖ = 1) :
    0 < PI.BesselPeriodGGP.fdegH μG σ w := by
  obtain ⟨d, hd, hS⟩ := Formalism.FourierDecayAlt.P.schur_hermitian k r ε lam H σ μG hlam hσ hG
  obtain ⟨hint, heq⟩ := hS w w w w
  have hf : (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ * star ⟪w, σ (Matrix.of x) w⟫_ℂ) =
      fun x => (((‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hf, integral_complex_ofReal] at heq
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
  rw [hww, one_mul] at heq
  have hI : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by
    have := congrArg Complex.re heq
    simp only [Complex.ofReal_re] at this
    rw [this]
    rw [show (1 : ℂ) / (d : ℂ) = ((1 / d : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  delta PI.BesselPeriodGGP.fdegH
  rw [hI, hw]
  simp only [one_pow, one_div, inv_inv]
  exact hd

theorem muS_conc {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (hN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    muS μW μN {x | Matrix.of x ∉ UH (Hpk k r)} = 0 := by
  have hm : Measurable (fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := by
    apply Continuous.measurable
    exact continuous_pi fun i => continuous_pi fun j => (Continuous.matrix_mul continuous_fst continuous_snd).matrix_elem i j
  set m : Mt k r × Mt k r → Mt k r := fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j with hmdef
  have hmuS : muS μW μN = (μW.prod μN).map m := rfl
  have hset : {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} = {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ := rfl
  rw [hmuS, hset, Measure.map_apply hm (Formalism.MainNotions.BesselShellMomentBounds.measurableSet_UH k r).compl]
  have g1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae hW
  have g2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae hN
  have g : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := by
    filter_upwards [g1, g2] with p h1 h2
    exact WeylGroupFacts.uh_mul h1.1 h2.1
  rw [ae_iff] at g
  exact g

theorem B_ne {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN νS : Measure (Mt k r)}
    (hG : IsHaarOn (UH (Hpk k r)) μG) (hW : IsHaarOn (UWset k r z) μW) (hN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    [SigmaFinite μN] (hq : IsQuotMeas μG (muS μW μN) νS) {B : H → Wp} {v0 : H}
    (hv0 : v0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {c : ℝ} (hc : 0 < c)
    (hl2 : l2SG νS (fun g => B (σ g v0)) = ENNReal.ofReal (c * Module.finrank ℂ Wp)) :
    ∃ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x ≠ 0 := by
  have : SigmaFinite μW := hW.1
  have hWa : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have hS0 : muS μW μN ≠ 0 := by
    intro h0
    have e := hq 1 measurable_one
    rw [h0] at e
    simp at e
    exact hG.2.1 (by simpa using e)
  have hae0 : ∀ᵐ y ∂νS, Matrix.of y ∈ UH (Hpk k r) := by
    rw [ae_iff]; simpa using Formalism.MainNotions.S.Pv.AmpTrans.quot_meas_not_mem_UH_eq_zero hG hS0 (muS_conc hWa hN) hq
  by_contra hcon
  push Not at hcon
  have hσU := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ
  have hz0 : l2SG νS (fun g => B (σ g v0)) = 0 := by
    delta l2SG
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae0] with y hy
    show (‖B (σ (Matrix.of y) v0)‖₊ : ℝ≥0∞) ^ 2 = 0
    rw [hcon _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσU hv0 hy)]
    simp
  rw [hl2] at hz0
  have hm0 : 0 < c * (Module.finrank ℂ Wp : ℝ) := mul_pos hc (by exact_mod_cast Module.finrank_pos)
  exact (ENNReal.ofReal_pos.2 hm0).ne' hz0


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ampOrbCoefDD_of (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.MainNotions.S.Pv.LemmaJ.AmpOrbCoefDD := by
  intro Cg cb Cu cT CT C0
  refine ⟨0, 1000, fun C' Cl _ hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' => ?_⟩
  have hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs := Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ
  have hAt := Formalism.FourierDecayAlt.P.admissible_atomic_form_one
  have hl0 : l1dist (lamD D τ) (lamD D τ) ≤ 0 * D.R.k * (D.R.m : ℝ) ^ 3 := by
    delta l1dist
    simp
  obtain ⟨h, hg, hok, hcell⟩ :=
    Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 hCl (by linarith) hH τ (lamD D τ) hl0
  set L := toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0

  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith) hH τ w w' hTT θ W hW (lamD D τ) hl0 A hA hT hT'
      w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp

  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩

  have hW' := hW
  obtain ⟨hc1, hc2, -, -, -, -, -, hUW, -, hUW', -, hNq, hq, hq'⟩ := hW'
  have hA' := hA
  obtain ⟨-, -, -, -, hv0s, hv0ne, -, hcN, hl2, hl2', -⟩ := hA'
  have hNa : ∀ᵐ x ∂W.μN, Matrix.of x ∈ Nset D.R.k D.R.rS := by
    rw [hNq]; exact Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_haarLieN _
  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have : SigmaFinite W.μN := by
    have := (Formalism.MainNotions.BridgeCSB.haarLieN D.R.k D.R.rS _ hκ0 hκtop).1
    rw [hNq]; exact this
  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hNt' : Nontrivial W.Wq := by obtain ⟨g, -, hU⟩ := hc2; exact hU.1
  obtain ⟨xb, hxb, hBx⟩ := B_ne hA.2.1 hG hUW hNa hq hv0s hcN hl2
  obtain ⟨xb', hxb', hBx'⟩ := B_ne hA.2.1 hG hUW' hNa hq' hv0s hcN hl2'
  have hc0ne : c0 ≠ 0 := by
    intro e; apply hBx; have h1 := hc0 xb hxb; rw [e] at h1; rw [h1]; exact zero_smul ℂ _
  have hc0ne' : c0' ≠ 0 := by
    intro e; apply hBx'; have h1 := hc0' xb' hxb'; rw [e] at h1; rw [h1]; exact zero_smul ℂ _

  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have htne : t ≠ 0 := by rw [ht]; exact_mod_cast norm_ne_zero_iff.mpr hv0ne
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hv0s
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'

  set s : ℂ := ⟪l x, l x⟫_ℂ * ⟪l' x', l' x'⟫_ℂ with hs
  have hs0 : s ≠ 0 := mul_ne_zero (inner_self_ne_zero.mpr hlx) (inner_self_ne_zero.mpr hlx')
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  have hdg0 : dg ≠ 0 := by
    rw [hdg]
    obtain ⟨-, -, hn1, -⟩ := hw0
    exact_mod_cast (fdegH_pos hA.1 hA.2.1 hG hn1).ne'
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  have hK1ne : K1 ≠ 0 := by
    rw [hK1]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero (by exact_mod_cast hcN.ne')) (mul_ne_zero hc0ne htne)) ?_
    exact (map_ne_zero _).2 (mul_ne_zero hc0ne' htne)
  refine ⟨x, x', l x, l' x', l x, l' x', K1 * s⁻¹ * dg⁻¹,
    mul_ne_zero (mul_ne_zero hK1ne (inv_ne_zero hs0)) (inv_ne_zero hdg0), hDDs x hx, hDDs x' hx',
    hOP.1.2.2.2.2.2.1 x hx x hx, hOP.1.2.2.2.2.2.2 x' hx' x' hx', inner_self_ne_zero.mpr hlx,
    inner_self_ne_zero.mpr hlx', ?_⟩
  intro γ hγ hGf hMono hRel μR νR ν hRH hOQ hqR
  have hCD : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨b, hb0, hbm, hbi⟩ :=
    Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD hMono
  have hAmp := Formalism.L2.SG.AmpOrbClosed.ampDD_thm hI _ _ L h W.μG w0 l l' hOP.1 γ μR νR ν hCD b hb0 (by linarith) hbi
    x hx x' hx' (l x) (l' x')
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae
  have hJ2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      (s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := by
    have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := hAmp
    have e1 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
        s⁻¹ • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e1, hAmp']
    exact smul_smul s⁻¹ dg⁻¹ _
  rw [hJ1, hJ2]
  have hO := orbInt_smul L (K1 * s⁻¹ * dg⁻¹) (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν
  have e2 : K1 • ((s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν) =
      (K1 * s⁻¹ * dg⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L x x' (l x) (l' x')) γ ν := by
    rw [smul_smul]
    congr 1
    ring
  exact e2.trans hO.symm


end Formalism.L2.S.Pv.AmpOrbCoef
