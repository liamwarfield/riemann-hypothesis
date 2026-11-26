module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartIntegralLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsCombineMk
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

section Meas

variable {k r : ℕ}

theorem uh_mul {a b : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

theorem uh_cancel {a x : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hax : a * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hax' : (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) = Formalism.QuantumDeterminants.Hpk k r := hax
  show xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r
  calc xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = xᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * x := by rw [ha']
    _ = (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := hax'

theorem uh_measurableSet :
    MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : IsClosed {x : Formalism.QuantumDeterminants.Mt k r | (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact hc.measurableSet.compl

theorem ae_UH_of_quot {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : μG {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS0 : μS ≠ 0) (hS : μS {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) :
    ∀ᵐ x ∂νq, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  classical
  set B : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hBdef
  have hBm : MeasurableSet B := uh_measurableSet
  have key := hq (B.indicator 1) (measurable_one.indicator hBm)
  rw [lintegral_indicator_one hBm, hG] at key
  have hc : μS Bᶜ ≠ 0 := by
    intro h0
    apply hS0
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc μS Set.univ = μS (B ∪ Bᶜ) := by rw [Set.union_compl_self]
      _ ≤ μS B + μS Bᶜ := measure_union_le _ _
      _ = 0 := by rw [hS, h0, add_zero]
  have hle : ∀ x, μS Bᶜ * B.indicator 1 x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, ← lintegral_indicator_one hBm.compl]
      refine lintegral_mono fun s => ?_
      by_cases hs : Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
      · have hsx : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ B := fun hmem =>
          hx (uh_cancel (x := Matrix.of x) hs hmem)
        have hsB : s ∈ Bᶜ := fun h => h hs
        rw [Set.indicator_of_mem hsB, Set.indicator_of_mem hsx]
        exact le_rfl
      · have hsB : s ∉ Bᶜ := fun h => h hs
        rw [Set.indicator_of_notMem hsB]
        exact zero_le
    · rw [Set.indicator_apply, if_neg hx, mul_zero]
      exact zero_le
  have h0 : μS Bᶜ * νq B = 0 := by
    rw [← lintegral_indicator_one hBm, ← lintegral_const_mul _ (measurable_one.indicator hBm)]
    refine le_antisymm ?_ zero_le
    calc ∫⁻ x, μS Bᶜ * B.indicator 1 x ∂νq
        ≤ ∫⁻ x, ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂νq := lintegral_mono hle
      _ = 0 := key.symm
  have hνB : νq B = 0 := (mul_eq_zero.mp h0).resolve_left hc
  rw [ae_iff]
  exact hνB

theorem muSof_facts {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    muSof μW μN ≠ 0 ∧ muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  obtain ⟨hWs, hW0, hWb, -⟩ := hW
  obtain ⟨hNs, hN0, hNb, -⟩ := hN
  haveI := hWs
  haveI := hNs
  have hcont : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hmeas := hcont.measurable
  refine ⟨?_, ?_⟩
  · intro h0
    unfold muSof at h0
    rw [Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    have h1 : (μW.prod μN) Set.univ = 0 := by rw [h0, Measure.coe_zero, Pi.zero_apply]
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact hW0 (Measure.measure_univ_eq_zero.mp h)
    · exact hN0 (Measure.measure_univ_eq_zero.mp h)
  · unfold muSof
    rw [Measure.map_apply hmeas uh_measurableSet]
    refine measure_mono_null (t := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ ∪
      Set.univ ×ˢ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_ ?_
    · rintro ⟨a, b⟩ hab
      by_contra hno
      simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, Set.mem_setOf_eq, not_or,
        not_not] at hno
      exact hab (uh_mul hno.1.1 hno.2.1)
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hWb, zero_mul]
      · rw [Measure.prod_prod, hNb, mul_zero]

end Meas

section Deg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fdeg_eq {σ : Mx k r → (H →L[ℂ] H)} {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} {d : ℝ} (hd : 0 < d)
    (hS : ∀ v w v' w' : H,
      Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {u : H} (hu : u ≠ 0) : PI.BesselPeriodGGP.fdegH μG σ u = d := by
  obtain ⟨-, hI⟩ := hS u u u u
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r, ⟪u, σ (Matrix.of x) u⟫_ℂ * star ⟪u, σ (Matrix.of x) u⟫_ℂ =
      ((‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hpt] at hI
  rw [integral_complex_ofReal] at hI
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hu4 : (0 : ℝ) < ‖u‖ ^ 4 := pow_pos hn 4
  have huu : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) u
    · rw [Complex.ofReal_im]
      exact inner_self_im (𝕜 := ℂ) u
  have hreal : ∫ x, ‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 ∂μG = ‖u‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hI, huu]
    push_cast
    ring
  unfold PI.BesselPeriodGGP.fdegH
  rw [hreal]
  field_simp

end Deg

section Bessel

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem bessel_smul {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B) (κ : ℂ) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => κ • B x) := by
  obtain ⟨hadd, hsm, heq, C, Ws, hWs, hbd⟩ := hB
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, ‖κ‖ * C, Ws, hWs, fun v hv => ?_⟩
  · simp only [hadd v hv w hw, smul_add]
  · simp only [hsm c v hv]
    exact smul_comm κ c (B v)
  · simp only [heq h hh m hm v hv, map_smul]
    exact smul_comm κ (ψ m) _
  · rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (norm_nonneg κ)

theorem bessel_zero {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ} {σ : Mx k r → (H →L[ℂ] H)}
    {π : Mx k r → (Wp →L[ℂ] Wp)} :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun _ => (0 : Wp)) := by
  refine ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => by simp, 0, [], by simp,
    fun _ _ => by simp⟩

theorem jsz_line (hU : PI.BesselMapUniq.BesselMapUniq) (hPsi : PsiConst)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {B0 B : H → Wp}
    (h0 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B0)
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B)
    {x0 : H} (hx0 : x0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hne : B0 x0 ≠ 0) :
    ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x = κ • B0 x := by
  have hfun : Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) :=
    funext fun g => hPsi k r z c g
  rw [hfun] at h0 h
  obtain ⟨a, b, hab, hlin⟩ := hU k r ε lam H σ z (fun _ => c) u Wp π hl hσ hz hT (fun _ => hc) hπ B0 B h0 h
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := hab.resolve_right (fun h => h rfl)
    have h2 := hlin x0 hx0
    rw [zero_smul, add_zero, smul_eq_zero] at h2
    exact h2.elim ha hne
  refine ⟨-(a / b), fun x hx => ?_⟩
  have h1 : b • B x = -(a • B0 x) := eq_neg_of_add_eq_zero_right (hlin x hx)
  calc B x = b⁻¹ • (b • B x) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = -(a / b) • B0 x := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Bessel

end Formalism.FourierDecayAlt.P.DDSmoothness
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma bigCell_mulVec_jV (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    bigCell k r c μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by
  rw [← emb_mulVec_jV (r := r) μ u]
  ext i
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    have e : bigCell k r c μ i j = Formalism.FourierDecayAlt.B2.embWb k r μ i j := by
      simp only [bigCell, Formalism.FourierDecayAlt.B2.embWb, dif_neg hj1, dif_pos hj.2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, dif_pos ⟨hi, hj⟩]
      · rw [dif_neg hi, dif_neg (fun h => hi h.1)]
        rw [if_neg]
        rintro ⟨rfl, h2⟩
        exact h2 hj
    rw [e]
  · have h0 : jV k r u j = 0 := by simp only [jV, dif_neg hj]
    rw [h0, mul_zero, mul_zero]

lemma herm_bigCell (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [bigCell_mulVec_jV, herm_jV]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gqDom (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    gq D q ∈ Om k r D.z D.z' := by
  obtain ⟨hc, hζ⟩ := hq
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  refine ⟨big_cell_mem_holds k r q.1 _ hc hsec.1, ?_, ?_⟩
  · intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    show Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) l ≠ 0
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  · have hz := hmin.2.2 hc
    rw [herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    show 0 < Gf k r D.z D.z' (gq D q)
    unfold Gf gq
    rw [hlast, ← hP, Complex.normSq_mul]
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

theorem _root_.Formalism.FourierDecayAlt.P.big_cell_domain : GqDom := fun _ _ _ _ _ _ _ _ D _ hq => gqDom D hq

end Formalism.FourierDecayAlt.P.BigCellHermitian
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ∞) :
    CkOn m (GV k r) (fun _ : Mat k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma dLR_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : List (Mat k r)) :
    dLR u v (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
  have hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show RdV X (Rw w _) = _
      rw [ih]
      funext g
      simp only [RdV, deriv_const']
  induction u with
  | nil => exact hR v
  | cons X u ih =>
    show LdV X (dLR u v _) = _
    rw [ih]
    funext g
    simp only [LdV, deriv_const']

lemma norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [Complex.norm_exp]
  simp

lemma isOpen_OmPlus (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Formalism.FourierDecayAlt.Q.OmPlus k r z z') := by
  have e : Formalism.FourierDecayAlt.Q.OmPlus k r z z' =
      (⋂ l : Fin (r + 2), {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0}) ∩ {g | 0 < Gf k r z z' g} := by
    ext g; simp [Formalism.FourierDecayAlt.Q.OmPlus]
  rw [e]
  refine (isOpen_iInter_of_finite fun l => ?_).inter
    (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z'))
  by_cases hl : l.val ≤ r
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' l) continuous_const
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_univ

lemma cv_continuous (b : Bool) (X g : Mat k r) : Continuous fun t : ℝ => cv b X t g := by
  cases b
  · exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  · have h := (Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous
    have h2 := (continuous_mul_const g).comp h
    refine h2.congr fun t => ?_
    simp [cv, smul_neg]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma norm_xiP (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiP D p‖ ≤ 1 := by
  unfold xiP
  simp [norm_psi]

lemma continuous_xiP (D : RealPlaceData k r Wp Wq) : Continuous (xiP D) := by
  have key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M) := by
    intro z
    unfold ell
    refine continuous_finsetSum _ fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, ↓reduceDIte, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]
      refine continuous_finsetSum _ fun j _ => ?_
      first
        | fun_prop
        | exact (((continuous_apply j).comp (continuous_apply (eI k r a))).mul continuous_const :)
        | continuity
  have hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M) := by
    intro z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (key z)))))
  unfold xiP
  exact ((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul
    (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))

lemma ckOn_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) := by
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have e : rho D p F = fun x => ((ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)))
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
    funext x
    simp only [rho, sgs, Matrix.mul_assoc]
    rfl
  rw [e]
  exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hF ha hb) _

lemma ckOn_dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X)
    (hv : ∀ X ∈ v, unitLie k r X) (j : ℕ) (hl : j + (u.length + v.length) ≤ m) :
    CkOn ((j : ℕ) : ℕ∞) (GV k r) (dLR u v (rho D p F)) := by
  rw [dLR_eq]
  exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) j (ckOn_mono (by rw [length_lr]; omega) (ckOn_rho D hp hF))

lemma good_set (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F)
    {K : Set (Mat k r)} (hK : IsCompact K) (hKG : K ⊆ GV k r)
    {WS : Set (List (Mat k r) × List (Mat k r))} (hWS : WS.Countable)
    (hWSl : ∀ uv ∈ WS, (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m)
    (b : SS k r → ℝ)
    (hb : ∀ uv ∈ WS, ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖rho D p (dLR (uv.1.map (AdL p)) (uv.2.map (AdR p)) F) g‖ ≤ b p) :
    ∀ᵐ p ∂D.μSS, D.inSS p ∧ ∀ uv ∈ WS, ∀ g ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g‖ ≤ b p := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat k r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨S, hSK, hSc, hKS⟩ := hK.isSeparable.exists_countable_dense_subset
  haveI := hWS.to_subtype
  haveI := hSc.to_subtype
  have hall : ∀ᵐ p ∂D.μSS, ∀ i : WS × S,
      ‖rho D p (dLR (i.1.1.1.map (AdL p)) (i.1.1.2.map (AdR p)) F) i.2.1‖ ≤ b p :=
    ae_all_iff.2 fun i => hb i.1.1 i.1.2 i.2.1 (hSK i.2.2)
  filter_upwards [hall, Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp hpS
  refine ⟨hpS, fun uv huv g hg => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hWSl uv huv
  have hcont : ContinuousOn (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) (GV k r) :=
    (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_dLR_rho D hpS hF h1 h2 0 (by omega))).norm
  have hcl : IsClosed (GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p)) :=
    hcont.preimage_isClosed_of_isClosed Formalism.FourierDecayAlt.P.B5.GV_closed isClosed_Iic
  have hS : S ⊆ GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p) := by
    intro x hx
    refine ⟨hKG (hSK hx), ?_⟩
    show ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ b p
    rw [dLR_rho D hpS]
    exact hp ⟨⟨uv, huv⟩, ⟨x, hx⟩⟩
  exact (hcl.closure_subset_iff.2 hS (hKS hg)).2

lemma curve_ball (D : RealPlaceData k r Wp Wq) {g : Mat k r} (hg : g ∈ Om k r D.z D.z') (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ Om k r D.z D.z' := by
  have hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') :=
    (isOpen_OmPlus _ _).preimage (cv_continuous b X g)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := by
    show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'
    rw [cv_zero]; exact hg.2
  obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := hg
  refine ⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩
  rw [Metric.mem_closedBall] at ht
  rw [Metric.mem_ball]
  linarith

end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.QuantumMinorCommutation

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem sgn_congr {a b : ℕ} (h : a % 2 = b % 2) : (-1 : ℤ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

section alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem commute_Tm (v : ℂ) (a b : Fin n) (x : A) (h : Commute x (E a b)) : Commute x (Tm E v a b) := by
  unfold Tm
  refine Commute.add_right ?_ h
  split_ifs
  · exact (Algebra.commutes v x).symm
  · exact Commute.zero_right x

theorem Tm_comm (v : ℂ) (a b : Fin n) (x : A) :
    Tm E v a b * x - x * Tm E v a b = E a b * x - x * E a b := by
  unfold Tm
  have h : (if a = b then algebraMap ℂ A v else 0) * x = x * (if a = b then algebraMap ℂ A v else 0) := by
    split_ifs
    · exact Algebra.commutes v x
    · simp
  rw [add_mul, mul_add, h]
  abel

theorem commute_qminor {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (x : A)
    (h : ∀ s s', Commute x (E (a s) (b s'))) : Commute x (qminor E a b u) := by
  unfold qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.commute_cast x _) ?_
  refine Commute.list_prod_right _ _ (fun y hy => ?_)
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  exact commute_Tm E _ _ _ x (h _ _)

theorem rowExp (hE : GlRel E) {m : ℕ} (a b : Fin (m + 1) → Fin n) (l₀ : Fin (m + 1)) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
      (Tm E (u - (m : ℂ)) (a l₀) (b l) * qminor E (a ∘ l₀.succAbove) (b ∘ l.succAbove) u) := by
  have h := quantumMinorRowSkew_holds A n (m + 1) E a b (Fin.cycleRange l₀).symm u
  have hs : ((Equiv.Perm.sign (Fin.cycleRange l₀).symm : ℤˣ) : ℤ) = (-1) ^ (l₀ : ℕ) := by
    rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp
  rw [hs] at h
  have h2 : qminor E a b u = (((-1 : ℤ) ^ (l₀ : ℕ) : ℤ) : A) * qminor E (a ∘ (Fin.cycleRange l₀).symm) b u := by
    rw [h, ← mul_assoc, ← Int.cast_mul, ← pow_add, sgn_congr (b := 0) (by omega)]
    simp
  rw [h2, expansion_first_line A n m E hE _ b u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h0 : (a ∘ (Fin.cycleRange l₀).symm) 0 = a l₀ := by
    simp [Fin.cycleRange_symm_zero]
  have h1 : (a ∘ (Fin.cycleRange l₀).symm) ∘ Fin.succ = a ∘ l₀.succAbove := by
    funext k
    simp [Fin.cycleRange_symm_succ]
  rw [h0, h1, ← mul_assoc, ← Int.cast_mul, ← pow_add]

theorem colExp (hE : GlRel E) {m : ℕ} (a b : Fin (m + 1) → Fin n) (l₀ : Fin (m + 1)) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * Tm E (u - (m : ℂ)) (a l) (b l₀)) := by
  have h := quantumMinorColSkew_holds A n (m + 1) E hE a b (cycleToLast m l₀) u
  have hs : ((Equiv.Perm.sign (cycleToLast m l₀) : ℤˣ) : ℤ) = (-1) ^ (m - (l₀ : ℕ)) := by
    rw [sign_cycleToLast]
    simp
  rw [hs] at h
  have h2 : qminor E a b u = (((-1 : ℤ) ^ (m - (l₀ : ℕ)) : ℤ) : A) * qminor E a (b ∘ cycleToLast m l₀) u := by
    rw [h, ← mul_assoc, ← Int.cast_mul, ← pow_add, sgn_congr (b := 0) (by omega)]
    simp
  rw [h2, expansion_last_column A n m E a _ u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h0 : (b ∘ cycleToLast m l₀) (Fin.last m) = b l₀ := by
    simp [cycleToLast_last]
  have h1 : (b ∘ cycleToLast m l₀) ∘ Fin.castSucc = b ∘ l₀.succAbove := by
    funext k
    simp [cycleToLast_castSucc]
  have hl := l₀.isLt
  rw [h0, h1, ← mul_assoc, ← Int.cast_mul, ← pow_add,
    sgn_congr (a := m - (l₀ : ℕ) + (m + (l : ℕ))) (b := (l₀ : ℕ) + (l : ℕ)) (by omega)]

theorem minorVec_gen (hE : GlRel E) (y : Fin n → A) (hy : IsVec E y) {m : ℕ} (a b : Fin (m + 1) → Fin n)
    (l₀ : Fin (m + 1)) (hne : ∀ k, a (l₀.succAbove k) ≠ a l₀) (u : ℂ) :
    qminor E a b u * y (a l₀) = y (a l₀) * qminor E a b u -
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
        (y (b l) * qminor E (a ∘ l₀.succAbove) (b ∘ l.succAbove) u) := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', rowExp E hE a b l₀ u, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hM : Commute (y (a l₀)) (qminor E (a ∘ l₀.succAbove) (b ∘ l.succAbove) u) := by
    refine commute_qminor E _ _ u _ (fun s s' => ?_)
    have := hy ((a ∘ l₀.succAbove) s) ((b ∘ l.succAbove) s') (a l₀)
    rw [if_neg (show (a ∘ l₀.succAbove) s ≠ a l₀ from hne s), sub_eq_zero] at this
    exact this.symm
  have hT : Tm E (u - (m : ℂ)) (a l₀) (b l) * y (a l₀) - y (a l₀) * Tm E (u - (m : ℂ)) (a l₀) (b l) = -y (b l) := by
    rw [Tm_comm, hy, if_pos rfl]
  have hc : y (a l₀) * (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) =
      (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) * y (a l₀) := (Int.commute_cast _ _).eq
  have hT' : y (b l) = y (a l₀) * Tm E (u - (m : ℂ)) (a l₀) (b l) - Tm E (u - (m : ℂ)) (a l₀) (b l) * y (a l₀) := by
    rw [← neg_sub, hT, neg_neg]
  rw [← mul_assoc (y (a l₀)), hc, mul_assoc _ (y (a l₀)), mul_assoc _ _ (y (a l₀)), mul_assoc _ _ (y (a l₀)),
    ← hM.eq, ← mul_sub]
  congr 1
  rw [hT', sub_mul, mul_assoc, mul_assoc]

theorem minorCov_gen (hE : GlRel E) (η : Fin n → A) (hη : IsCov E η) {m : ℕ} (a b : Fin (m + 1) → Fin n)
    (l₀ : Fin (m + 1)) (hne : ∀ k, b (l₀.succAbove k) ≠ b l₀) (u : ℂ) :
    qminor E a b u * η (b l₀) - η (b l₀) * qminor E a b u =
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * η (a l)) := by
  rw [colExp E hE a b l₀ u, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hM : Commute (η (b l₀)) (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u) := by
    refine commute_qminor E _ _ u _ (fun s s' => ?_)
    have := hη ((a ∘ l.succAbove) s) ((b ∘ l₀.succAbove) s') (b l₀)
    rw [if_neg (show (b ∘ l₀.succAbove) s' ≠ b l₀ from hne s'), sub_eq_zero] at this
    exact this.symm
  have hT : Tm E (u - (m : ℂ)) (a l) (b l₀) * η (b l₀) - η (b l₀) * Tm E (u - (m : ℂ)) (a l) (b l₀) = η (a l) := by
    rw [Tm_comm, hη, if_pos rfl]
  have hc : η (b l₀) * (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) =
      (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) * η (b l₀) := (Int.commute_cast _ _).eq
  rw [← mul_assoc (η (b l₀)), hc, mul_assoc _ (η (b l₀)), ← mul_assoc (η (b l₀)), hM.eq,
    mul_assoc _ _ (η (b l₀)), mul_assoc _ _ (η (b l₀)), mul_assoc _ (η (b l₀)), ← mul_sub, ← mul_sub, hT]

end alg

theorem sa_val {m : ℕ} (q : Fin (m + 1)) (l : Fin m) :
    ((q.succAbove l : Fin (m + 1)) : ℕ) = if (l : ℕ) < (q : ℕ) then (l : ℕ) else (l : ℕ) + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem skip_one_eq_succAbove {m : ℕ} (q : Fin (m + 1)) : (skip1 q : Fin m → Fin (m + 1)) = q.succAbove :=
  funext (skip_succ_identity m q)

theorem skip_comp {m : ℕ} (q : Fin (m + 2)) (l : Fin (m + 1)) :
    (q.succAbove ∘ l.succAbove : Fin m → Fin (m + 2)) = skip2 (min (q.succAbove l) q) (max (q.succAbove l) q) := by
  funext k
  apply Fin.ext
  simp only [Function.comp, skip2, Fin.coe_min, Fin.coe_max, sa_val]
  split_ifs <;> simp only [] <;> omega

theorem eps_sa {m : ℕ} (q : Fin (m + 1)) (l : Fin m) :
    eps (q.succAbove l) q * (-1) ^ ((q.succAbove l : Fin (m + 1)) : ℕ) = (-1) ^ (l : ℕ) := by
  unfold eps
  rw [sa_val]
  split_ifs
  · simp
  · omega
  · rw [pow_succ]; ring

theorem detVec_succ {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A)
    (y : Fin (m + 1) → A) (hE : GlRel E) (hy : IsVec E y) (w : ℂ) (j : Fin (m + 1)) :
    qdet E w * y j = y j * qdet E w -
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((j : ℕ) + (l : ℕ)) : ℤ) : A) *
        (y l * qminor (t := m) E (skip1 j) (skip1 l) w) := by
  have h := minorVec_gen E hE y hy id id j (fun k => Fin.succAbove_ne j k) w
  simp only [id, Function.id_comp] at h
  simp only [skip_one_eq_succAbove]
  exact h

theorem minorCov_succ {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
    (η : Fin (m + 2) → A) (hE : GlRel E) (hη : IsCov E η) (u : ℂ) (q p i : Fin (m + 2)) (hip : i ≠ p) :
    qminor (t := m + 1) E (skip1 q) (skip1 p) u * η i - η i * qminor (t := m + 1) E (skip1 q) (skip1 p) u =
      ∑ a : Fin (m + 2), if a = q then 0 else
        ((eps a q * eps i p * (-1) ^ ((a : ℕ) + (i : ℕ)) : ℤ) : A) *
          (qminor (t := m) E (skip2 (min a q) (max a q)) (skip2 (min i p) (max i p)) u * η a) := by
  obtain ⟨l₀, rfl⟩ := Fin.exists_succAbove_eq hip
  have h := minorCov_gen E hE η hη q.succAbove p.succAbove l₀
    (fun k => fun hk => Fin.succAbove_ne l₀ k (Fin.succAbove_right_injective hk)) u
  rw [skip_one_eq_succAbove, skip_one_eq_succAbove, h, Fin.sum_univ_succAbove _ q, if_pos rfl, zero_add]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [if_neg (Fin.succAbove_ne q l), skip_comp, skip_comp]
  congr 2
  rw [pow_add, pow_add, ← eps_sa q l, ← eps_sa p l₀]
  ring

end Formalism.FourierDecayAlt.P.QuantumMinorCommutation

theorem Formalism.FourierDecayAlt.P.quantum_determinant_vector : Formalism.FourierDecayAlt.Qr.DetVec := by
  intro A _ _ t E y hE hy w j
  cases t with
  | zero => exact j.elim0
  | succ m => exact Formalism.FourierDecayAlt.P.QuantumMinorCommutation.detVec_succ E y hE hy w j

theorem Formalism.FourierDecayAlt.P.quantum_minor_covariance : Formalism.FourierDecayAlt.Qr.MinorCov := by
  intro A _ _ t E η hE hη u q p i
  by_cases hip : i = p
  · rw [if_pos hip, sub_eq_zero]
    refine (Formalism.FourierDecayAlt.P.QuantumMinorCommutation.commute_qminor E _ _ u _ (fun s s' => ?_)).eq.symm
    have := hη (Formalism.FourierDecayAlt.Q.skip1 q s) (Formalism.FourierDecayAlt.Q.skip1 p s') i
    have hne : Formalism.FourierDecayAlt.Q.skip1 p s' ≠ i := by
      rw [hip]
      intro h
      have h' := congrArg Fin.val h
      unfold Formalism.FourierDecayAlt.Q.skip1 at h'
      split_ifs at h' <;> simp only [] at h' <;> omega
    rw [if_neg hne, sub_eq_zero] at this
    exact this.symm
  · rw [if_neg hip]
    match t, E, η, hE, hη, q, p, i, hip with
    | 0, _, _, _, _, q, _, _, _ => exact q.elim0
    | 1, _, _, _, _, _, p, i, hip => exact absurd (Subsingleton.elim i p) hip
    | m + 2, E, η, hE, hη, q, p, i, hip => exact Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_succ E η hE hη u q p i hip
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P

namespace C2x7

variable {k r : ℕ}

lemma one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun a => ⟨by simp, by simp⟩, by simp⟩

lemma N_sub_S {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, one_mem_UW z, n, hn, by simp⟩

lemma UW_sub_S {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩

end C2x7

open C2x5 C2x6 C2x7

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Actual

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem mulOp_comm_fn (X : ActualOps k r z z' π π') (W : Module.End ℂ (RadSp k r z z' π π'))
    (m : (Fin r → ℂ) → Mx k r → ℂ) (hW : multiplicationOperator W m) (j : Fin 6) : W * X.fn j = X.fn j * W := by
  have hW1 : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      m c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g := hW
  apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
  simp only [Module.End.mul_apply]
  rw [hW1]
  by_cases hp : (c, g) ∈ DomR k r z z'
  · have h1 := X.fn_apply j Φ (c, g) hp
    have h2 := X.fn_apply j (W Φ) (c, g) hp
    simp only at h1 h2
    rw [h1, h2, hW1, smul_comm]
  · have h1 := (X.fn j Φ).2.1 (c, g) hp
    have h2 := (X.fn j (W Φ)).2.1 (c, g) hp
    simp only at h1 h2
    rw [h1, h2, smul_zero]

end Actual

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliUnderIntegral
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CapelliUnderIntegral

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem glev0 {k r : ℕ} (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by
  simp only [Q.Glev, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, fun a ha => by simp at ha⟩

theorem integrable_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    Integrable (fun x => (L.map (fun i => φ i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem integral_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    ∫ x, (L.map (fun i => φ i x)).sum ∂μ = (L.map (fun i => ∫ x, φ i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := h i (by simp)
    have hL : ∀ j ∈ L, Integrable (φ j) μ := fun j hj => h j (by simp [hj])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add hi (integrable_map_sum L φ hL), ih hL]

end Formalism.FourierDecayAlt.P.CapelliUnderIntegral

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Truncated
theorem Formalism.FourierDecayAlt.P.derivative_cost_bound : Formalism.FourierDecayAlt.U.DerivativeCost := by
  have hS : Formalism.FourierDecayAlt.U.SliceMem := Formalism.FourierDecayAlt.P.slice_membership
  have h21 : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
    Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses hS Formalism.FourierDecayAlt.P.block3_apply_embedding Formalism.FourierDecayAlt.P.aux_statement_17
      Formalism.FourierDecayAlt.P.hat_z_on_slice
  exact operator_word_cost hS Formalism.FourierDecayAlt.P.radical_parametrisation Formalism.FourierDecayAlt.P.slice_right_coordinates
    Formalism.FourierDecayAlt.P.slice_left_coordinates Formalism.FourierDecayAlt.P.slice_z_coordinates Formalism.FourierDecayAlt.P.directions_in_parabolic h21
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvSelf
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section PairNeg

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_neg_fst (a : Pr V) : (-a).1 = -a.1 := rfl
theorem pr_neg_snd (a : Pr V) : (-a).2.unop = -a.2.unop := rfl

end PairNeg

end Formalism.FourierDecayAlt.P5
end
end
