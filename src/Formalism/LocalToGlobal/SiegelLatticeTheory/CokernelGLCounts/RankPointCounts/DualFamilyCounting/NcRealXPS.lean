module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealX
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdExactHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPlace
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXN
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem inN_indep {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
    (hz' : ∀ a, hJ ε (e a) z' = 0) {g : Matrix (Fin n) (Fin n) ℂ} (h : InN ε e z g) : InN ε e z' g :=
  ⟨⟨h.1.1, h.2 z' hz'⟩, h.2⟩

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem Qm_mulVec_eq_sum (w : Fin (2 * r + k + 1) → ℂ) : Qm e f wf z0 *ᵥ w = ∑ j, w j • colQ e f wf z0 j := by
  funext i
  simp only [mulVec, dotProduct, Qm, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem Qm_mem_spanLt {a : ℕ} (ha : a ≤ r) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → w i = 0) : Qm e f wf z0 *ᵥ w ∈ spanLt e a := by
  rw [Qm_mulVec_eq_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j.val < a
  · have hjr : j.val < r := lt_of_lt_of_le hj ha
    have hc : colQ e f wf z0 j = e ⟨j.val, hjr⟩ := by simp [colQ, hjr]
    rw [hc]
    unfold spanLt
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, hjr⟩, hj, rfl⟩)
  · rw [hw j (not_lt.mp hj), zero_smul]
    exact Submodule.zero_mem _

theorem sub_one_eI {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) (a : Fin r)
    (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : ((m - 1) *ᵥ bvec (eI k r a)) i = 0 := by
  rw [bvec, mulVec_single_one, col_apply, Matrix.sub_apply, hm.2.1 a i hi, Matrix.one_apply, sub_self]

theorem sub_one_mulVec_apply_eq_zero_of_mem_Nset {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ j : Fin (2 * r + k + 1), r + k < j.val → w j = 0)
    (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : ((m - 1) *ᵥ w) i = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases lt_or_ge (r + k) j.val with hj | hj
  · rw [hw j hj, mul_zero]
  · rcases lt_or_ge j.val r with hj' | hj'
    · have h1 := hm.2.1 ⟨j.val, hj'⟩ i (by show j.val ≤ i.val; omega)
      have he : eI k r ⟨j.val, hj'⟩ = j := Fin.ext rfl
      rw [he] at h1
      rw [Matrix.sub_apply, h1, Matrix.one_apply, sub_self, zero_mul]
    · rw [Matrix.sub_apply, hm.2.2 i j hj' hj hi, Matrix.one_apply, sub_self, zero_mul]

theorem Qi_perp (y : Fin (2 * r + k + 1) → ℂ) (hy : ∀ a, hJ ε (e a) y = 0) (j : Fin (2 * r + k + 1))
    (hj : r + k < j.val) : (Qi ε e f wf z0 *ᵥ y) j = 0 := by
  have hv : ∀ l : Fin (2 * r + k + 1), l.val < r → ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0 := by
    intro l hl
    have hc : colQ e f wf z0 l = e ⟨l.val, hl⟩ := by simp [colQ, hl]
    have h1 := hy ⟨l.val, hl⟩
    rw [← hc] at h1
    rw [← h1]
    simp only [hJ, mulVec, dotProduct, conjTranspose_apply, Qm, of_apply, Pi.star_apply]
  unfold Qi
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change ∑ l, Hpk k r j l * ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hv l hl, mul_zero]
  · have h0 : Hpk k r j l = 0 := by
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> first | rfl | omega
    rw [h0, zero_mul]

theorem inN_of_conj (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : Qi ε e f wf z0 * g * Qm e f wf z0 ∈ Nset k r) :
    InN ε e (Qm e f wf z0 *ᵥ zB) g := by
  have hg : Qm e f wf z0 * (Qi ε e f wf z0 * g * Qm e f wf z0) * Qi ε e f wf z0 = g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul, Matrix.mul_assoc,
      Qm_mul_Qi hF, Matrix.mul_one]
  have key : ∀ v, (g - 1) *ᵥ v
      = Qm e f wf z0 *ᵥ ((Qi ε e f wf z0 * g * Qm e f wf z0 - 1) *ᵥ (Qi ε e f wf z0 *ᵥ v)) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, hg, Matrix.mul_one, Qm_mul_Qi hF]
  have hz : Qi ε e f wf z0 *ᵥ (Qm e f wf z0 *ᵥ zB) = zB := by
    rw [mulVec_mulVec, Qi_mul_Qm hF, one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, Qi_e hF]
    exact Qm_mem_spanLt (le_of_lt a.isLt) _ (fun i hi => sub_one_eI hm a i hi)
  · rw [key, hz]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm zB (fun j hj => hzB j (Or.inr hj)) i hi)
  · rw [key]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm _ (fun j hj => Qi_perp y hy j hj) i hi)

theorem refN_map (hF : IsFrameJ ε e f wf z0) :
    (refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) = Jac.N1 k r := by
  have h := measN_of hF 1
  rwa [ENNReal.ofReal_one, one_smul] at h

theorem refN_isHaarLoc (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    (hz0 : ∃ t : ℂ, z0 = t • (Qm e f wf z0 *ᵥ zB)) :
    IsHaarLoc (NLoc ε e (Qm e f wf z0 *ᵥ zB)) (refN ε e f wf z0) := by
  set C := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hC
  have hE : MeasurableEmbedding C := embQ hF
  have hmap : Measure.map C (refN ε e f wf z0) = Jac.N1 k r := refN_map hF
  have hH := Jac.nilradical_measure_is_haar (k := k) (r := r)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : SigmaFinite (Measure.map C (refN ε e f wf z0)) := by
      rw [hmap]
      exact hH.1
    exact SigmaFinite.of_map _ hE.measurable.aemeasurable hs
  · intro h0
    apply hH.2.1
    rw [← hmap, h0, Measure.map_zero]
  · refine measure_mono_null (t := C ⁻¹' {x : Mt k r | of x ∉ Nset k r}) ?_ ?_
    · intro g hg
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro hm
      exact hg (inN_of_conj hF hzB hm)
    · rw [← hE.map_apply, hmap]
      exact hH.2.2.1
  · intro s hs
    have hsN := conj_mem_Nset hF hz0 (uMat_mem s) hs
    have hcomp : C ∘ (fun x => s * x) = lmulM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) ∘ C := by
      funext x
      simp only [Function.comp_apply, hC]
      rw [lmulM_cM]
      show Qi ε e f wf z0 * uMat (s * x) * Qm e f wf z0
        = Qi ε e f wf z0 * uMat s * Qm e f wf z0 * Qi ε e f wf z0 * uMat x * Qm e f wf z0
      rw [uMat_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.one_mul]
    have hms : Measurable (fun x : ↥(REAL.UJ ε) => s * x) := by
      rw [← hE.measurable_comp_iff, hcomp]
      exact (measurable_lmulM _).comp hE.measurable
    have hmm : Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))
        = Measure.map C (refN ε e f wf z0) := by
      rw [Measure.map_map hE.measurable hms, hcomp, ← Measure.map_map (measurable_lmulM _) hE.measurable,
        hmap, hH.2.2.2 _ hsN]
    calc Measure.map (fun x => s * x) (refN ε e f wf z0)
        = Measure.comap C (Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))) :=
          (hE.comap_map _).symm
      _ = Measure.comap C (Measure.map C (refN ε e f wf z0)) := by rw [hmm]
      _ = refN ε e f wf z0 := hE.comap_map _

end Formalism.L2.SG.Pf.NcReal.JX
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

def refNg : {n r k : ℕ} → n = 2 * r + k + 1 → (ε : Fin n → Bool) → (Fin r → Fin n → ℂ) → (Fin r → Fin n → ℂ) →
    (Fin k → Fin n → ℂ) → (Fin n → ℂ) → Measure (Formalism.REAL.UJ ε)
  | _, _, _, rfl, ε, e, f, wf, z0 => refN ε e f wf z0

theorem refNg_rfl {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) :
    refNg rfl ε e f wf z0 = refN ε e f wf z0 := rfl

theorem muSL_smul {n : ℕ} {ε : Fin n → Bool} (μH μN : Measure (Formalism.REAL.UJ ε)) [SFinite μH] (c : ℝ≥0∞) :
    muSL μH (c • μN) = c • muSL μH μN := by
  unfold muSL; rw [Measure.prod_smul_left, Measure.map_smul]
  exact measurable_mul.aemeasurable

theorem disint_smul_right {n r k : ℕ} {ε : Fin n → Bool} {T T' : ℝ} {μS μS' : Measure (Formalism.REAL.UJ ε)}
    {h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} {C c : ℝ} (hc : 0 < c) (hD : DisintLoc ε k T T' μS μS' h C) :
    DisintLoc ε k T T' μS (ENNReal.ofReal c • μS') h (C / c) := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun x _ => ?_)
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul' hc.le]
  congr 2
  field_simp

theorem placeStep (hJG : JacGauge) {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T T' : ℝ} (hk : 1 ≤ k) (hT : 0 < T)
    (hT' : 0 < T') (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (hez' : ∀ a, hJ ε (e a) z' = 0) (hfz' : ∀ a, hJ ε (f a) z' = 0) (hzz' : hJ ε z' z' = -(T' : ℂ))
    (hG : Formalism.MainNotions.S.Gauge.GaugeDens ε) (μH μH' : Measure (Formalism.REAL.UJ ε))
    (hH : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) μH) (hH' : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z') μH')
    (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a') (hma : μH Set.univ = ENNReal.ofReal a)
    (hma' : μH' Set.univ = ENNReal.ofReal a') (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (hh : IsSecLoc ε 1 e z z' T T' h) :
    DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refNg hn ε e f wf (z0v T z)))
      (muSL μH' (ENNReal.ofReal κ' • refNg hn ε e f wf (z0v T z))) h
      (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
        ((T * T') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * (κ * κ'))) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hzB : inWb k r (zBv k r T) := inWb_zB T
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hTzB : Tz k r (zBv k r T) = T := Tz_zB hT.le
  set zB' := Qi ε e f wf (z0v T z) *ᵥ z' with hzB'
  have hQzB' : Qm e f wf (z0v T z) *ᵥ zB' = z' := by
    rw [hzB', Matrix.mulVec_mulVec, Qm_mul_Qi hFJ, Matrix.one_mulVec]
  have hzB'W : inWb k r zB' := by
    intro i hi
    rcases hi with hi | hi
    · have hie : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hie, hzB', Qi_mulVec_eI, hfz']
    · exact Qi_perp z' hez' i hi
  have hTzB' : Tz k r zB' = T' := by
    have hw := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_P (gramQ hFJ) zB' zB'
    rw [hQzB', hzz'] at hw
    unfold Tz
    rw [← hw]
    simp
  have hHB : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zBv k r T)) μH := by
    rw [hQzB]; exact hH
  have hHB' : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zB')) μH' := by
    rw [hQzB']; exact hH'
  have hhB : IsSecLoc ε 1 e (Qm e f wf (z0v T z) *ᵥ zBv k r T) (Qm e f wf (z0v T z) *ᵥ zB')
      (Tz k r (zBv k r T)) (Tz k r zB') h := by
    rw [hQzB, hQzB', hTzB, hTzB']; exact hh
  have hD := jacLocX_of hJG k r ε e f wf (z0v T z) (zBv k r T) zB' hFJ hk hzB hzB'W (by rw [hTzB]; exact hT)
    (by rw [hTzB']; exact hT') hG μH μH' hHB hHB' a a' ha ha' hma hma' κ hκ h hhB
  rw [hTzB, hTzB'] at hD
  have hD2 := disint_smul_right (c := κ' / κ) (div_pos hκ' hκ) hD
  haveI : SigmaFinite μH' := hH'.1
  have hm : muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z)) =
      ENNReal.ofReal (κ' / κ) • muSL μH' (ENNReal.ofReal κ • refN ε e f wf (z0v T z)) := by
    rw [muSL_smul, muSL_smul, smul_smul, ← ENNReal.ofReal_mul (div_pos hκ' hκ).le, div_mul_cancel₀ _ hκ.ne']
  show DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refN ε e f wf (z0v T z)))
    (muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z))) h _
  rw [hm]
  convert hD2 using 1
  have hV1 := Jac.volU_pos (k - 1)
  field_simp

theorem refNg_isHaarLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) (hez' : ∀ a, hJ ε (e a) z' = 0) :
    IsHaarLoc (NLoc ε e z') (refNg hn ε e f wf (z0v T z)) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f wf (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQzB]; rfl⟩
  have h0 := refN_isHaarLoc hFJ (inWb_zB T) hz0
  rw [hQzB] at h0
  obtain ⟨h1, h2, h3, h4⟩ := h0
  have hNeq : NLoc ε e z' = NLoc ε e z := by
    ext g
    exact ⟨fun hg => inN_indep hez hg, fun hg => inN_indep hez' hg⟩
  show IsHaarLoc (NLoc ε e z') (refN ε e f wf (z0v T z))
  rw [hNeq]
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.Pf.NcReal.JX
end
end

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem isFrameJ_of {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z : Fin (2 * r + k + 1) → ℂ} {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) : IsFrameJ ε e f wf (z0v T z) := by
  have hl : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ), hJ ε (c • x) y = star c * hJ ε x y := by
    intro x y c
    simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul]
  have hr : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ), hJ ε x (c • y) = c * hJ ε x y := by
    intro x y c
    simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul]
  have hsc : star ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  have key : ((Real.sqrt T)⁻¹ * ((Real.sqrt T)⁻¹ * -T) : ℝ) = -1 := by
    rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hT.le, mul_neg, inv_mul_cancel₀ hT.ne']
  refine ⟨hee, hff, hef, ?_, ?_, ?_, hww, hew, hfw, ?_⟩
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hr, hez, mul_zero]
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hr, hfz, mul_zero]
  · rw [Formalism.L2.SG.Pf.WFL.z0v, hl, hr, hzz, hsc]
    exact_mod_cast key
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hl, hzw, mul_zero]

theorem hLoc_eq {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    Formalism.L2.SG.Pf.NcReal.HLoc ε e f z = Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc ε e f z := by
  ext s
  simp only [Formalism.L2.SG.Pf.NcReal.HLoc, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc, Set.mem_setOf_eq, forall_and,
    and_assoc]

theorem compact_HLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) : IsCompact (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have hemb := cM_closedEmb (ε := ε) (A := Qi ε e f wf (z0v T z)) (B := Qm e f wf (z0v T z))
    (A' := Qm e f wf (z0v T z)) (B' := Qi ε e f wf (z0v T z)) (Qm_mul_Qi hFJ) (Qm_mul_Qi hFJ)
  have hW : IsCompact (UWset k r (zBv k r T) : Set (Mt k r)) :=
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r (zBv k r T) (inWb_zB T) (by rw [Tz_zB hT.le]; exact hT)
  have hK := hemb.isCompact_preimage hW
  have hcl : IsClosed (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) := by
    rw [hLoc_eq]
    exact NilradicalHermitianFrames.NH.HG_closed ε e f z
  refine hK.of_isClosed_subset hcl fun g hg => ?_
  exact conj_mem_UWset hFJ (Qm_zB hT z) (uMat_mem g) (fun a => (hg.1 a).1) (fun a => (hg.1 a).2) hg.2

theorem pi_smul_factors {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI : ∀ i, SigmaFinite (c i • μ i) := fun i =>
    ⟨⟨⟨spanningSets (μ i), fun _ => Set.mem_univ _, fun n => by
        rw [Measure.smul_apply, smul_eq_mul]
        exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (hc i) (measure_spanningSets_lt_top (μ i) n).ne),
      iUnion_spanningSets (μ i)⟩⟩⟩
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

theorem isHaarLoc_smul {n : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (h : IsHaarLoc S μ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) : IsHaarLoc S (c • μ) := by
  unfold Formalism.L2.SG.RealObj.IsHaarLoc at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  haveI := h1
  refine ⟨⟨⟨⟨spanningSets μ, fun _ => Set.mem_univ _, fun n => ?_, iUnion_spanningSets μ⟩⟩⟩, ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hc (measure_spanningSets_lt_top μ n).ne)
  · intro h0
    apply h2
    ext s _
    simpa [hc0] using congrArg (fun m : Measure (Formalism.REAL.UJ ε) => m s) h0
  · simp [h3]
  · intro s hs
    rw [Measure.map_smul c (continuous_const_mul s).measurable.aemeasurable, h4 s hs]

end Gen

section HidaSetting

variable {D : D7} (X : HidaSetting D)

theorem nX : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  rw [X.n_eq]
  have hm := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

def refNX (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  refNg (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (z0v (Tw u) (ProductExactness.zV X u v))

section Facts

variable (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

theorem fX_ee : ∀ a b, hJ (X.B.I.ε v) (eV X v a) (eV X v b) = 0 := fun a b =>
  (ProductExactness.hJ_X X v (X.eX a) (X.eX b)).trans (by rw [X.ee]; simp)
theorem fX_ff : ∀ a b, hJ (X.B.I.ε v) (ProductExactness.pV X v a) (ProductExactness.pV X v b) = 0 := fun a b =>
  (ProductExactness.hJ_X X v (X.fY a) (X.fY b)).trans (by rw [X.ff]; simp)
theorem fX_ef : ∀ a b, hJ (X.B.I.ε v) (eV X v a) (ProductExactness.pV X v b) = if a = b then 1 else 0 := fun a b =>
  (ProductExactness.hJ_X X v (X.eX a) (X.fY b)).trans (by rw [X.ef]; split_ifs <;> simp)
theorem fX_ww : ∀ a b, hJ (X.B.I.ε v) (X.wfr u v a) (X.wfr u v b) = if a = b then 1 else 0 := X.wfr_on u v
theorem fX_ew : ∀ c a, hJ (X.B.I.ε v) (eV X v c) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
theorem fX_fw : ∀ c a, hJ (X.B.I.ε v) (ProductExactness.pV X v c) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
theorem fX_ez : ∀ a, hJ (X.B.I.ε v) (eV X v a) (ProductExactness.zV X u v) = 0 := (ProductExactness.frameLoc_X X u u v).ez
theorem fX_fz : ∀ a, hJ (X.B.I.ε v) (ProductExactness.pV X v a) (ProductExactness.zV X u v) = 0 := fun a =>
  (ProductExactness.hJ_X X v (X.fY a) (X.zu u)).trans (by rw [(X.zu_orth u a).2]; simp)
theorem frame_real_z_z_eq_neg : hJ (X.B.I.ε v) (ProductExactness.zV X u v) (ProductExactness.zV X u v) = -((Tw u : ℝ) : ℂ) :=
  (ProductExactness.frameLoc_X X u u v).zz
theorem fX_zw : ∀ a, hJ (X.B.I.ε v) (ProductExactness.zV X u v) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2

end Facts

theorem muNv_eq (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ d ≠ ⊤ ∧ ProductExactness.muNv X w v = d • refNX X u v := by
  have hR := refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
    (ProductExactness.zV X w v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X w v)
  obtain ⟨r1, r2, r3, r4⟩ := hR
  obtain ⟨⟨m1, m2, m3, m4⟩, -⟩ := ProductExactness.muNv_haar X w v
  haveI : SigmaFinite (refNX X u v) := r1
  exact ProductExactness.PiM.uniq_on_closed (ProductExactness.NGv X w v) (NilradicalHermitianFrames.NH.NG_closed _ _ _) _ _ m3 r3 m4 r4 m2 r2

theorem muHv_mass (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ProductExactness.muHv X u v Set.univ ≠ 0 ∧ ProductExactness.muHv X u v Set.univ ≠ ⊤ := by
  obtain ⟨⟨m1, m2, m3, m4⟩, m5⟩ := ProductExactness.muHv_haar X u v
  have hK := compact_HLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
    (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  rw [hLoc_eq] at hK
  refine ⟨fun h0 => m2 (Measure.measure_univ_eq_zero.1 h0), ?_⟩
  have hsplit : ProductExactness.muHv X u v Set.univ ≤
      ProductExactness.muHv X u v (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v)) +
        ProductExactness.muHv X u v (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v))ᶜ := by
    rw [← Set.union_compl_self (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v)
      (ProductExactness.zV X u v))]
    exact measure_union_le _ _
  have m3' : ProductExactness.muHv X u v
      (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v))ᶜ = 0 := m3
  rw [m3', add_zero] at hsplit
  exact (lt_of_le_of_lt hsplit (hK.measure_lt_top)).ne

end HidaSetting

def CovolRef : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' →
      ((Measure.pi (refNX X u)) FdN).toReal * ((Measure.pi (refNX X u)) FdN').toReal =
        |(NumberField.discr X.B.I.F : ℝ)| ^ eDF D.R.k D.R.rS

theorem placeSplit_of (hJG : JacGauge) (hC : CovolRef) : PlaceSplit := by
  classical
  intro D X hb FdN FdN' u u' ψ hHyp _ _ hGd
  obtain ⟨v0⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

  obtain ⟨κN, hκN0, hκNT, hN⟩ := ProductExactness.muN_eq X u
  obtain ⟨κN', hκN'0, hκN'T, hN'⟩ := ProductExactness.muN_eq X u'
  choose d hd0 hdT hd using fun v => muNv_eq X u u v
  choose d' hd'0 hd'T hd' using fun v => muNv_eq X u u' v
  set cN : InfinitePlace X.B.I.F → ℝ≥0∞ := fun v => (if v = v0 then κN else 1) * d v with hcN
  set cN' : InfinitePlace X.B.I.F → ℝ≥0∞ := fun v => (if v = v0 then κN' else 1) * d' v with hcN'
  have hcT : ∀ v, cN v ≠ ⊤ := fun v => ENNReal.mul_ne_top (by split_ifs <;> simp [hκNT]) (hdT v)
  have hcT' : ∀ v, cN' v ≠ ⊤ := fun v => ENNReal.mul_ne_top (by split_ifs <;> simp [hκN'T]) (hd'T v)
  have hc0 : ∀ v, cN v ≠ 0 := fun v => mul_ne_zero (by split_ifs <;> simp [hκN0]) (hd0 v)
  have hc0' : ∀ v, cN' v ≠ 0 := fun v => mul_ne_zero (by split_ifs <;> simp [hκN'0]) (hd'0 v)
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
      (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X u v)).1
  have hprod : ∀ (κ0 : ℝ≥0∞) (dd : InfinitePlace X.B.I.F → ℝ≥0∞), (∀ v, dd v ≠ ⊤) → κ0 ≠ ⊤ →
      κ0 • Measure.pi (fun v => dd v • refNX X u v) =
        Measure.pi (fun v => ((if v = v0 then κ0 else 1) * dd v) • refNX X u v) := by
    intro κ0 dd hddT hκ0
    rw [pi_smul_factors _ dd hddT, pi_smul_factors _ _ (fun v => ENNReal.mul_ne_top
      (by split_ifs <;> simp [hκ0]) (hddT v)), smul_smul, Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hmuN : X.muN u = Measure.pi (fun v => cN v • refNX X u v) := by
    have he : ProductExactness.muNv X u = fun v => d v • refNX X u v := funext hd
    rw [hN, he]
    exact hprod κN d hdT hκNT
  have hmuN' : X.muN u' = Measure.pi (fun v => cN' v • refNX X u v) := by
    have he : ProductExactness.muNv X u' = fun v => d' v • refNX X u v := funext hd'
    rw [hN', he]
    exact hprod κN' d' hd'T hκN'T

  obtain ⟨κH, hκH0, hκHT, hH⟩ := ProductExactness.muH_eq X u
  obtain ⟨κH', hκH'0, hκH'T, hH'⟩ := ProductExactness.muH_eq X u'
  set μH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (if v = v0 then κH else 1) • ProductExactness.muHv X u v with hμH
  set μH' : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (if v = v0 then κH' else 1) • ProductExactness.muHv X u' v
    with hμH'
  have hsH : ∀ v, (if v = v0 then κH else 1) ≠ 0 ∧ (if v = v0 then κH else 1) ≠ ⊤ := fun v => by
    split_ifs <;> simp [hκH0, hκHT]
  have hsH' : ∀ v, (if v = v0 then κH' else 1) ≠ 0 ∧ (if v = v0 then κH' else 1) ≠ ⊤ := fun v => by
    split_ifs <;> simp [hκH'0, hκH'T]
  have hmuH : X.muH u = Measure.pi μH := by
    have hp : (∏ v, (if v = v0 then κH else 1 : ℝ≥0∞)) = κH := by simp
    rw [hH, hμH, pi_smul_factors _ _ (fun v => (hsH v).2), hp]
  have hmuH' : X.muH u' = Measure.pi μH' := by
    have hp : (∏ v, (if v = v0 then κH' else 1 : ℝ≥0∞)) = κH' := by simp
    rw [hH', hμH', pi_smul_factors _ _ (fun v => (hsH' v).2), hp]
  have hHaarH : ∀ v, IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v)) (μH v) :=
    fun v => by
      rw [hLoc_eq]
      exact isHaarLoc_smul (ProductExactness.muHv_haar X u v).1 (hsH v).1 (hsH v).2
  have hHaarH' : ∀ v, IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u' v))
      (μH' v) := fun v => by
    rw [hLoc_eq]
    exact isHaarLoc_smul (ProductExactness.muHv_haar X u' v).1 (hsH' v).1 (hsH' v).2
  have hmH : ∀ v, μH v Set.univ ≠ 0 ∧ μH v Set.univ ≠ ⊤ := fun v => by
    obtain ⟨h1, h2⟩ := muHv_mass X u v
    simp only [hμH, Measure.smul_apply, smul_eq_mul]
    exact ⟨mul_ne_zero (hsH v).1 h1, ENNReal.mul_ne_top (hsH v).2 h2⟩
  have hmH' : ∀ v, μH' v Set.univ ≠ 0 ∧ μH' v Set.univ ≠ ⊤ := fun v => by
    obtain ⟨h1, h2⟩ := muHv_mass X u' v
    simp only [hμH', Measure.smul_apply, smul_eq_mul]
    exact ⟨mul_ne_zero (hsH' v).1 h1, ENNReal.mul_ne_top (hsH' v).2 h2⟩

  refine ⟨fun v => cN v • refNX X u v, fun v => cN' v • refNX X u v, μH, μH',
    fun v => (μH v Set.univ).toReal, fun v => (μH' v Set.univ).toReal, fun v => (cN v).toReal,
    fun v => (cN' v).toReal, ((Measure.pi (refNX X u)) FdN).toReal, ((Measure.pi (refNX X u)) FdN').toReal,
    fun v => ProductExactness.sf_smul _ _ (hcT v), fun v => ProductExactness.sf_smul _ _ (hcT' v), fun v => (hHaarH v).1,
    fun v => (hHaarH' v).1, fun v => ⟨ENNReal.toReal_pos (hmH v).1 (hmH v).2, ENNReal.toReal_pos (hmH' v).1 (hmH' v).2,
      ENNReal.toReal_pos (hc0 v) (hcT v), ENNReal.toReal_pos (hc0' v) (hcT' v)⟩,
    hmuN, hmuN', hmuH, hmuH', fun v => (ENNReal.ofReal_toReal (hmH v).2).symm,
    fun v => (ENNReal.ofReal_toReal (hmH' v).2).symm, ?_, ?_, ?_, hC X hb FdN FdN' u u' hHyp⟩
  · intro v h hh
    have hP := placeStep hJG (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u' v) hk (ProductExactness.Tw_pos u) (ProductExactness.Tw_pos u') (fX_ee X v) (fX_ff X v) (fX_ef X v)
      (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
      (fX_ez X u' v) (fX_fz X u' v) (frame_real_z_z_eq_neg X u' v) (hGd v) (μH v) (μH' v) (hHaarH v) (hHaarH' v)
      _ _ (ENNReal.toReal_pos (hmH v).1 (hmH v).2) (ENNReal.toReal_pos (hmH' v).1 (hmH' v).2)
      (ENNReal.ofReal_toReal (hmH v).2).symm (ENNReal.ofReal_toReal (hmH' v).2).symm
      (cN v).toReal (cN' v).toReal (ENNReal.toReal_pos (hc0 v) (hcT v)) (ENNReal.toReal_pos (hc0' v) (hcT' v)) h hh
    rw [ENNReal.ofReal_toReal (hcT v), ENNReal.ofReal_toReal (hcT' v)] at hP
    exact hP
  · rw [hmuN, pi_smul_factors _ _ hcT, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod]
  · rw [hmuN', pi_smul_factors _ _ hcT', Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod]

theorem realBracket_of_jac (hJG : JacGauge) (hC : CovolRef) (hA : AprimeInf)
    (hG : ∀ (n : ℕ) (ε : Fin n → Bool), Formalism.MainNotions.S.Gauge.GaugeDens ε) : RealBracket :=
  realBracket_of Formalism.L2.SG.RealObj.InfCut.ProductExactness.ProdExact_holds hA (placeSplit_of hJG hC) hG

end Formalism.L2.SG.Pf.NcReal.JX
