module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslate
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypotheses

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOne
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem lintegral_prod_pow_le_of_moments : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  classical
  intro Ω _ ν r q ρ Ph Rr s hρm hρ0 hPm hP0 hP1 hR hbd
  have hR0 : (0:ℝ) ≤ Rr := le_trans zero_le_one hR
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
    subst hs
    simpa using hP1
  · set N : ℕ := 2 * (r * q) with hN
    let u : Fin r → Ω → ℝ := fun a x => if a ∈ s then ρ a x else Rr
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    have hr0 : r ≠ 0 := Nat.pos_iff_ne_zero.mp hr
    have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
        ≤ ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
      have hall : ∀ᵐ x ∂ν, ∀ a, 0 ≤ ρ a x := ae_all_iff.mpr hρ0
      filter_upwards [hall] with x hx
      have hu0 : ∀ a, 0 ≤ u a x := fun a => by
        by_cases ha : a ∈ s <;> simp [u, ha, hx a, hR0]
      have h1 : (∏ a ∈ s, ρ a x) ^ (2 * q) ≤ ∏ a : Fin r, u a x ^ (2 * q) := by
        have : (∏ a ∈ s, ρ a x) ^ (2 * q)
            = ∏ a : Fin r, (if a ∈ s then ρ a x ^ (2 * q) else 1) := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow]
        rw [this]
        apply Finset.prod_le_prod₀
        · intro a _
          by_cases ha : a ∈ s
          · simp [ha, pow_nonneg (hx a)]
          · simp [ha]
        · intro a _
          by_cases ha : a ∈ s
          · simp [u, ha]
          · simp [u, ha, one_le_pow₀ hR]
      have h2 : ∏ a : Fin r, u a x ^ (2 * q) ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N := by
        have hw : ∑ _a : Fin r, (r:ℝ)⁻¹ = 1 := by
          simp [Finset.card_univ, Fintype.card_fin, hrR.ne']
        have key := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin r))
          (fun _ => (r:ℝ)⁻¹) (fun a => (u a x ^ (2 * q)) ^ r)
          (fun _ _ => inv_nonneg.mpr hrR.le) hw (fun a _ => pow_nonneg (pow_nonneg (hu0 a) _) _)
        have e1 : ∀ a, ((u a x ^ (2 * q)) ^ r) ^ ((r:ℝ)⁻¹) = u a x ^ (2 * q) := fun a =>
          Real.pow_rpow_inv_natCast (pow_nonneg (hu0 a) _) hr0
        have e2 : ∀ a, (u a x ^ (2 * q)) ^ r = u a x ^ N := fun a => by
          rw [← pow_mul, hN]; congr 1; ring
        simp only [e1] at key
        simp only [e2] at key
        exact key
      have hP : 0 ≤ Ph x := hP0 x
      have h3 : (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
          ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
        calc (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
            ≤ (∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N) * Ph x :=
              mul_le_mul_of_nonneg_right (h1.trans h2) hP
          _ = ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
              rw [Finset.sum_mul]; congr 1; ext a; ring
      calc ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
          ≤ ENNReal.ofReal (∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x)) :=
            ENNReal.ofReal_le_ofReal h3
        _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · congr 1; ext a
              rw [ENNReal.ofReal_mul (inv_nonneg.mpr hrR.le)]
            · intro a _
              exact mul_nonneg (inv_nonneg.mpr hrR.le) (mul_nonneg (pow_nonneg (hu0 a) _) hP)
    have hum : ∀ a, AEMeasurable (u a) ν := fun a => by
      by_cases ha : a ∈ s
      · simpa [u, ha] using hρm a
      · simp only [u, ha, if_false]; exact aemeasurable_const
    have hint : ∀ a, ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ N) := by
      intro a
      by_cases ha : a ∈ s
      · simpa [u, ha] using hbd a
      · simp only [u, ha, if_false]
        have hRN : (0:ℝ) ≤ Rr ^ N := pow_nonneg hR0 _
        simp_rw [ENNReal.ofReal_mul hRN]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc ENNReal.ofReal (Rr ^ N) * ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν
            ≤ ENNReal.ofReal (Rr ^ N) * 1 := by gcongr
          _ = ENNReal.ofReal (Rr ^ N) := mul_one _
    calc ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν
        ≤ ∫⁻ x, ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) ∂ν :=
          lintegral_mono_ae hpt
      _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν := by
          rw [lintegral_finsetSum']
          · congr 1; ext a
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          · intro a _
            exact (((hum a).pow_const N).mul hPm).ennreal_ofReal.const_mul _
      _ ≤ ∑ _a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (Rr ^ N) := by
          gcongr with a
          exact hint a
      _ = ENNReal.ofReal (Rr ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
          have : (r : ℝ≥0∞) * ENNReal.ofReal ((r:ℝ)⁻¹) = 1 := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg r),
              mul_inv_cancel₀ hrR.ne', ENNReal.ofReal_one]
          rw [this, one_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOneStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  first | exact @GlobalTheory.lintegral_prod_pow_le_of_moments | exact GlobalTheory.lintegral_prod_pow_le_of_moments | (intros; apply GlobalTheory.lintegral_prod_pow_le_of_moments <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesSecond
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMoment

theorem prod_ratio {r : ℕ} (l : Fin (r + 1) → ℝ) (hl : ∀ a, 0 < l a) (a : Fin (r + 1)) :
    ∏ c ∈ Finset.univ.filter (fun c : Fin r => a.val ≤ c.val), l c.succ / l c.castSucc
      = l (Fin.last r) / l a := by
  induction a using Fin.reverseInduction with
  | last =>
    have : Finset.univ.filter (fun c : Fin r => (Fin.last r).val ≤ c.val) = ∅ := by
      ext c
      have := c.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, Finset.notMem_empty, iff_false]
      omega
    rw [this, Finset.prod_empty, div_self (hl _).ne']
  | cast i ih =>
    have : Finset.univ.filter (fun c : Fin r => (Fin.castSucc i).val ≤ c.val)
        = insert i (Finset.univ.filter (fun c : Fin r => (Fin.succ i).val ≤ c.val)) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.val_succ,
        Fin.val_castSucc, Fin.ext_iff]
      omega
    rw [this, Finset.prod_insert (by simp), ih]
    have h1 := (hl i.succ).ne'
    have h2 := (hl i.castSucc).ne'
    field_simp

end GlobalTheory.InvLenMoment
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvMomentOfBessel
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem size_bound_inv {b v g x Cg Cu CT : ℝ} {r : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  calc x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2) * r) * (b ^ max 2 Cu) ^ (2 * r) := by gcongr
    _ = b ^ ((2 * Cg + 2) * r + max 2 Cu * ((2 * r : ℕ) : ℝ)) := by
        rw [Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le (max 2 Cu)]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
        push_cast
        have := abs_nonneg CT
        nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]

theorem rpow_bridge {b C x : ℝ} {q : ℕ} (hb : 0 ≤ b) : b ^ (2 * C * x * q) = (b ^ (C * x)) ^ (2 * q) := by
  rw [← Real.rpow_mul_natCast hb]; congr 1; push_cast; ring

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem hypTT_self (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (w : D.what₂.Word) : HypTT D w w := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, -, -, -, -, -, -, -⟩, hDat, -⟩ := hZ
  obtain ⟨-, -, -, -, -, -, -, -, hmod, -⟩ := hDat
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb2 : 2 < large₂.sc.b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hbe
  have hkb : 2 < (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hg : (2 : ℝ) < D.host.g 0 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg1)
  have hg' : 2 < D.host.g 0 := by exact_mod_cast hg
  have hgg : (2 : ℝ) < D.host.g 1 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg2)
  have hgg' : 2 < D.host.g 1 := by exact_mod_cast hgg
  have hp := (D.mem w).A.T_prime
  have h3 : 3 ≤ (D.mem w).A.T := by
    rcases (D.mem w).A.T_prime.two_le.eq_or_lt with h | h
    · exfalso
      have hm := (hmod w).2
      rw [← h] at hm
      have hN : 4 < (D.host.g 0 * D.host.g 1) ^ 2 := by
        have h9 : 9 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul (show 3 ≤ D.host.g 0 from hg') (show 3 ≤ D.host.g 1 from hgg')
        nlinarith
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      omega
    · omega
  exact ⟨hp, hp, h3, h3, Int.ModEq.refl _⟩

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem rd_le_b (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl)
    (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) : D.host.rdE ≤ large₂.sc.b := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -⟩, -, -⟩ := hZ
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have h0 : 0 < D.host.rdE := by rw [hrd]; linarith
  have h1 : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
  show D.host.rdE ≤ Real.exp large₂.sc.L
  exact (Real.log_le_iff_le_exp h0).1 (hrdL.trans h1)

end GlobalTheory.TwoSidedMoments
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InverseMajorantLengthMomentLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedMassHighestToLowestKTypeLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedMassHighestToLowestKTypeLargeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMassGap

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset GlobalTheory.LowTypeMass
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

theorem lev_zero_of_wt_gap (hH : HypsG) (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Q : Mx k r}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hE : R.IsE Q E) (S : Submodule ℂ R.H) (hfin : FiniteDimensional ℂ S)
    (hst : PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S)
    (hmax : ∀ (μ : Fin (2 * r + k + 1) → ℝ) (v : R.H), v ∈ S → v ≠ 0 →
      PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) μ v →
      PI.UpqRep.CDom ε μ (Formalism.QuantumDeterminants.lowK ε mu))
    (w : R.smSub) (hwS : (w : R.H) ∈ S)
    (hw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) (w : R.H)) :
    Lev ε E mu 0 w := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hRS : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hR
  obtain ⟨-, hS2⟩ := GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hRS Q hQ S hfin hst
  obtain ⟨hw1, hw2⟩ := GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hRS Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w hw
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hH k r ε mu R hk hR Q E hQ hE
  refine GlobalTheory.lev_zero_of_kHighest _ _ _ E _ w hMod.1 hMod.2.1 ⟨hw1, ?_⟩ ?_
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he _ hwS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨hwS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

theorem weightedMass_bound_lowestType_largeGap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg) (ν : Fin (2 * r + k + 1) → ℤ) (hν0 : n1 ν ≤ q0)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞) (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hbd : ∀ (Q : Mx k r) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub),
      PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q →
      (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) →
      ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
        (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd)
    (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w) :
    ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  classical
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hbd' := hbd Q E hQ hE
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) :=
    GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.1 k r lam u b bv ga h q0 R hNum hFam ν hν0
  have hDS := GlobalTheory.isDS_of_isDG hDG
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have hlenv : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) νq :=
    aemeasurable_pi_iff.2 hlen
  rcases eq_or_ne Bd ⊤ with rfl | hBd
  · exact le_top
  have hCB : ENNReal.ofReal Bd.toReal = Bd := ENNReal.ofReal_toReal hBd
  rw [← hCB]
  rw [← hCB] at hbd'
  have key := GlobalTheory.MomOne.lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((Real.sqrt (φ (fun a => lenA k r z (Matrix.of x) a)) * Real.sqrt (dg ν) : ℝ) : ℂ) •
      lb ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ Bd.toReal ENNReal.toReal_nonneg ?_ w hwL hw1
  · simpa only [norm_sq_sqrt_scaled (hφ0 _) hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add (f := _), hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable ?_).smul (hmeas (lb ν) hBeL.1 v hv)
    exact (((hφm.comp_aemeasurable hlenv).sqrt).mul_const _).aestronglyMeasurable
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := GlobalTheory.MomOne.conj_back hQ hg
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hBc := (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (lb ν) hBeL.1.1 hBeL.1.2.1
      hBeL.1.2.2.2 v hv).1
    have hF := measurable_piecewise_mass z hSide.1 hT φ hφm (dg ν) (fun x => lb ν ((R ν).σ x v)) hBc
    have := lintegral_rmul_of_measurable hSide
      (fun x => ENNReal.ofReal (φ (fun a => lenA k r z x a)) * ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ x v)‖ ^ 2))
      hF ?_ hgG
    · have e1 : ∀ x : Formalism.QuantumDeterminants.Mt k r, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
          (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)) =
          ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
            ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) :=
        fun x => ENNReal.ofReal_mul (hφ0 _)
      simp only [e1]
      rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      simp only [GlobalTheory.MomOne.lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
      rw [ENNReal.ofReal_mul (hφ0 _)]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      simp only [e]
      rw [hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    have hLev := lev_zero_of_wt_gap hH.1 hk hDG hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
    have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
    exact hbd' ⟨v, hvs⟩ hLev hv1'

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem mass_low_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd :=
  fun hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw =>
    weightedMass_bound_lowestType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw

end main

end GlobalTheory.LowTypeMassGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedMassHighestToLowestKTypeLargeGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedMass_highestToLowestKType_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  first | exact @GlobalTheory.LowTypeMassGap.mass_low_gap | exact GlobalTheory.LowTypeMassGap.mass_low_gap | (intros; apply GlobalTheory.LowTypeMassGap.mass_low_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InverseMajorantLengthMomentLargeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMomentGap

theorem inv_len_moment_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS hT ν q hν hq w hw a
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  have hS' := hS
  obtain ⟨hN, hF, hG, hSF⟩ := hS'
  have hb : 1 ≤ b := by
    obtain ⟨hk, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
    have e1 := h7 (Fin.last _) (by simp only [Fin.val_last]; omega)
    have e2 := h8 (Fin.last _)
    have e3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have e4 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := one_le_pow₀ e3
    have e5 := neg_abs_le (lam (Fin.last _))
    linarith [e1.2]
  have hdg : 0 < dg ν := (hSF ν hν).2.1
  obtain ⟨m1, -, m3, m4⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq
    (hF ν hν) hG
  refine GlobalTheory.T.weightedMass_highestToLowestKType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν
    (fun y => (y a)⁻¹ ^ (2 * q)) _ (by fun_prop) (fun y => Even.pow_nonneg (even_two_mul q) _) ?_ w hw
  intro Q E hQ hE v hv hv1
  have hmass := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν).1 v v.2
  have hv1' : ‖(v : (R ν).H)‖ = 1 := hv1
  simp only [one_mul, hv1', one_pow, ENNReal.ofReal_one] at hmass
  have hpos : ∀ᵐ x ∂νq, 1 ≤ lenA k r z (Matrix.of x) (Fin.last r) ∧ ∀ c, 0 < lenA k r z (Matrix.of x) c := by
    filter_upwards [m1] with x hx
    obtain ⟨e1, e2⟩ := GlobalTheory.T.last_majorant_length_sq_ge_and_pos k r z hG.1 hG.2.1 _ hx
    refine ⟨?_, fun c => (e2 c).1⟩
    have := (e2 (Fin.last r)).1
    nlinarith
  have hmeas : AEMeasurable (fun x : Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) νq :=
    (((m4 (lb ν) (hSF ν hν).1.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _
  have key := GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one (Mt k r) νq r q
    (fun c x => lenA k r z (Matrix.of x) c.succ / lenA k r z (Matrix.of x) c.castSucc)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (b ^ 2)
    (Finset.univ.filter (fun c : Fin r => a.val ≤ c.val))
    (fun c => (m3 _).div (m3 _))
    (fun c => by
      filter_upwards [hpos] with x hx
      exact div_nonneg (hx.2 _).le (hx.2 _).le)
    hmeas (fun x => by positivity) hmass (one_le_pow₀ hb)
    (fun c => by
      have := Gp91.GlobalTheory.T.family_setup_cayley_bound hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ hE ν hν
        0 (r * q) (by omega) c v hv
      rwa [hv1, one_pow, mul_one] at this)
  have hpw : (b ^ 2) ^ (2 * (r * q)) = (b ^ (2 * r)) ^ (2 * q) := by
    rw [← pow_mul, ← pow_mul]; congr 1; ring
  rw [← hpw]
  refine le_trans (lintegral_mono_ae ?_) key
  filter_upwards [hpos] with x hx
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [GlobalTheory.InvLenMoment.prod_ratio (fun c => lenA k r z (Matrix.of x) c) hx.2 a]
  refine pow_le_pow_left₀ (inv_nonneg.2 (hx.2 a).le) ?_ _
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hx.1 (hx.2 a).le

end GlobalTheory.InvLenMomentGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InverseMajorantLengthMomentLargeGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseMajorantLength_moment_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  first | exact @GlobalTheory.InvLenMomentGap.inv_len_moment_gap | exact GlobalTheory.InvLenMomentGap.inv_len_moment_gap | (intros; apply GlobalTheory.InvLenMomentGap.inv_len_moment_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTwoSidedMomentsLargeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.TwoSidedMomentsGap

open GlobalTheory.AmpMoments GlobalTheory.TwoSidedMoments

theorem family_through_gap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (ν₀ : Fin (2 * r + k + 1) → ℤ) (R0 : Rep k r) (hN : Num k r lam u b bv ga h q0)
    (hR0 : R0.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν₀ a : ℝ))) (hν₀ : n1 ν₀ ≤ q0) :
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFamG lam q0 R ∧ R ν₀ = R0 := by
  classical
  have hex : DSExistG := hH.1.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  obtain ⟨hN1, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = ν₀ → R = R0) := by
    intro ν
    by_cases h0 : ν = ν₀
    · refine ⟨R0, fun hq => ?_, fun _ => rfl⟩
      subst h0
      exact ⟨hR0.1, hR0.2, h / 2, (hfam ν hq).2.2.1, hN1.2.2.2.2⟩
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (hfam ν hq).1 hC ⟨h / 2, (hfam ν hq).2.2.1, hN1.2.2.2.2⟩
        exact ⟨R, fun _ => hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR ν₀).2 rfl⟩

theorem moment_of_bessel_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ}
    {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}
    {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r} {l : ∀ ν, (R ν).H → Wp} {dg : (Fin (2 * r + k + 1) → ℤ) → ℝ}
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (ν) (q : ℕ) (h1 : n1 ν + (r + 1) * q ≤ q0)
    (h2 : (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2) (R0 : Rep k r) (hR : R ν = R0) (B : R0.H → Wp)
    (hB : IsBes R0 z π B) (v : R0.H) (hv : v ≠ 0)
    (hlow : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P ∧
      v ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (fun g => R0.σ (P⁻¹ * g * P)))
    (h0 : l2SG νq (fun g => B (R0.σ g v)) ≠ 0) (ht : l2SG νq (fun g => B (R0.σ g v)) ≠ ⊤) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q)) * (‖B (R0.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂νq ≤
      ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) * l2SG νq (fun g => B (R0.σ g v)) := by
  subst hR
  have hν : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) h1
  have hSG := ((GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS)
  obtain ⟨hNum, hFam, hSide, hSF⟩ := id hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  have hDG := hSG.2.1 ν hν
  obtain ⟨hBe, hpos, -⟩ := hSF ν hν
  obtain ⟨-, -, -, hsm, hTK, -, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r _ _ (R ν) hDS
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : (R ν).H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hvw : v = ((‖v‖ : ℝ) : ℂ) • w := by
    rw [hw, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwl : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w := by
    obtain ⟨P, hP, hvP⟩ := hlow
    exact ⟨P, hP, hw1, Submodule.smul_mem _ _ hvP⟩
  have hwK : (R ν).KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hwl
  have hvK : (R ν).KFin v := by
    obtain ⟨S, hS1, hS2, hS3⟩ := hwK
    exact ⟨S, hS1, by rw [hvw]; exact S.smul_mem _ hS2, hS3⟩
  have hws : w ∈ (R ν).sm := hTK _ (hKT _ hwK)
  obtain ⟨v₁, hv₁, hl⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq B (l ν) v hDS hgap hOK hSide hB
    hvK h0 ht hBe
  have hnz : NzOn (R ν) (l ν) := ⟨v₁, hTK _ (hKT _ hv₁), hl⟩
  obtain ⟨c, hc⟩ := GlobalTheory.GapLine.bessel_line_gap hH k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) B hDG hSide hBe.1 hnz hB
  have hmass := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hSG ν hν).2 hnz).2 w hws
  have hmom := GlobalTheory.T.oneMajorantLength_moment_lowestKType hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν q h1 h2 w hwl a
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 m0 m1 hq
  set K : ℝ := (‖v‖ * ‖c‖) ^ 2 / dg ν with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ᵐ x ∂νq, ‖B ((R ν).σ (Matrix.of x) v)‖ ^ 2 = K * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) := by
    filter_upwards [hae] with x hx
    have hxs := hsm _ hx w hws
    have : B ((R ν).σ (Matrix.of x) v) = ((‖v‖ : ℝ) : ℂ) • c • l ν ((R ν).σ (Matrix.of x) w) := by
      conv_lhs => rw [hvw, map_smul]
      rw [hB.2.1 _ _ hxs, hc _ hxs]
    rw [this, norm_smul, norm_smul, Complex.norm_real, norm_norm, hK]
    field_simp
  have e1 : l2SG νq (fun g => B ((R ν).σ g v)) = ENNReal.ofReal K := by
    rw [hw1, one_pow, ENNReal.ofReal_one] at hmass
    rw [← mul_one (ENNReal.ofReal K), ← hmass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [sq_nnnorm, hx, one_mul, ENNReal.ofReal_mul hK0]
  rw [e1, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal K)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hmom _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  have hl0 : 0 ≤ lenA k r z (Matrix.of x) a ^ (2 * q) := pow_nonneg Metric.infDist_nonneg _
  rw [sq_nnnorm, hx, ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hK0]
  congr 1; ring

theorem inv_moment_of_bessel_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ}
    {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}
    {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r} {l : ∀ ν, (R ν).H → Wp} {dg : (Fin (2 * r + k + 1) → ℤ) → ℝ}
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (hT : 1 ≤ Tz k r z) (ν) (q : ℕ) (hν : n1 ν ≤ q0)
    (h2 : r * q ≤ 2 * (2 * r + k + 1) ^ 2) (R0 : Rep k r) (hR : R ν = R0) (B : R0.H → Wp)
    (hB : IsBes R0 z π B) (v : R0.H) (hv : v ≠ 0)
    (hlow : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P ∧
      v ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (fun g => R0.σ (P⁻¹ * g * P)))
    (h0 : l2SG νq (fun g => B (R0.σ g v)) ≠ 0) (ht : l2SG νq (fun g => B (R0.σ g v)) ≠ ⊤) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖B (R0.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂νq ≤
      ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) * l2SG νq (fun g => B (R0.σ g v)) := by
  subst hR
  have hSG := ((GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS)
  obtain ⟨hNum, hFam, hSide, hSF⟩ := id hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  have hDG := hSG.2.1 ν hν
  obtain ⟨hBe, hpos, -⟩ := hSF ν hν
  obtain ⟨-, -, -, hsm, hTK, -, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r _ _ (R ν) hDS
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : (R ν).H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hvw : v = ((‖v‖ : ℝ) : ℂ) • w := by
    rw [hw, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwl : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w := by
    obtain ⟨P, hP, hvP⟩ := hlow
    exact ⟨P, hP, hw1, Submodule.smul_mem _ _ hvP⟩
  have hwK : (R ν).KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hwl
  have hvK : (R ν).KFin v := by
    obtain ⟨S, hS1, hS2, hS3⟩ := hwK
    exact ⟨S, hS1, by rw [hvw]; exact S.smul_mem _ hS2, hS3⟩
  have hws : w ∈ (R ν).sm := hTK _ (hKT _ hwK)
  obtain ⟨v₁, hv₁, hl⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq B (l ν) v hDS hgap hOK hSide hB
    hvK h0 ht hBe
  have hnz : NzOn (R ν) (l ν) := ⟨v₁, hTK _ (hKT _ hv₁), hl⟩
  obtain ⟨c, hc⟩ := GlobalTheory.GapLine.bessel_line_gap hH k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) B hDG hSide hBe.1 hnz hB
  have hmass := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hSG ν hν).2 hnz).2 w hws
  have hmom := GlobalTheory.T.inverseMajorantLength_moment_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS hT ν q hν h2 w hwl a
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 m0 m1 hq
  set K : ℝ := (‖v‖ * ‖c‖) ^ 2 / dg ν with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ᵐ x ∂νq, ‖B ((R ν).σ (Matrix.of x) v)‖ ^ 2 = K * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) := by
    filter_upwards [hae] with x hx
    have hxs := hsm _ hx w hws
    have : B ((R ν).σ (Matrix.of x) v) = ((‖v‖ : ℝ) : ℂ) • c • l ν ((R ν).σ (Matrix.of x) w) := by
      conv_lhs => rw [hvw, map_smul]
      rw [hB.2.1 _ _ hxs, hc _ hxs]
    rw [this, norm_smul, norm_smul, Complex.norm_real, norm_norm, hK]
    field_simp
  have e1 : l2SG νq (fun g => B ((R ν).σ g v)) = ENNReal.ofReal K := by
    rw [hw1, one_pow, ENNReal.ofReal_one] at hmass
    rw [← mul_one (ENNReal.ofReal K), ← hmass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [sq_nnnorm, hx, one_mul, ENNReal.ofReal_mul hK0]
  rw [e1, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal K)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hmom _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  have hl0 : 0 ≤ (lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) := pow_nonneg (inv_nonneg.2 Metric.infDist_nonneg) _
  rw [sq_nnnorm, hx, ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hK0]
  congr 1; ring

end GlobalTheory.TwoSidedMomentsGap

namespace GlobalTheory.TwoSidedMomentsGap

open GlobalTheory.AmpMoments GlobalTheory.TwoSidedMoments

theorem two_sided_moments_gap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CH : ℝ, 0 ≤ CH ∧
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w (W : LocW D.R.k D.R.rS), GoodW D τ w w 1 W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    ∀ q : ℕ, q ≤ D.R.k * D.R.m ^ 3 → MomBd W.z W.νS A.Φ q (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧
      ∀ a : Fin (D.R.rS + 1), ∫⁻ x, ENNReal.ofReal ((lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹ ^ (2 * q)) *
        (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤
        ENNReal.ofReal ((large₂.sc.b ^ (CH * (D.R.m : ℝ))) ^ (2 * q)) * l2SG W.νS A.Φ := by
  intro hH Cg cb Cu cT CT C0
  refine ⟨2 * |Cg| + 2 + |CT| + 10 * max 2 Cu, by positivity, ?_⟩
  intro D large₂ C' Cl hCl hZ τ w W hW A hA q hq
  haveI := FiniteDimensional.complete ℂ W.Wp
  obtain ⟨-, -, hb, hm, -, -, -, hmk, hv, -, hka, hvb, hg, hgb, hCg, -, hT, -⟩ :=
    GlobalTheory.Amp.RangeModel.sizes_of D large₂ C' Cl Cg cb Cu cT CT C0 (rd_le_b D large₂ C' Cl Cg cb Cu cT CT C0 hCl hZ) hZ
  have hTT := hypTT_self D large₂ C' Cl Cg cb Cu cT CT C0 hZ w
  have hb1 : 1 ≤ large₂.sc.b := by have := Real.add_one_le_exp 1; linarith
  have hb0 : 0 ≤ large₂.sc.b := by linarith
  obtain ⟨hNum, -, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w (uOne D w τ) (fun i => by
    have := i.isLt
    simp only [uOne]
    rw [dite_eq_left ⟨by omega, by omega⟩]; rfl)
  set ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ := 0 with hν0
  have e0 : (fun i => lamD D τ i + (ν i : ℝ)) = lamD D τ := funext fun i => by simp [hν0]
  have hn0 : n1 ν = 0 := by simp [hν0, n1]

  have hm1 : D.R.rS + 1 ≤ D.R.m := by omega
  have hkm : D.R.k * D.R.m ^ 4 ≤ D.R.k * D.R.k := Nat.mul_le_mul_left _ hmk
  have hq1 : (D.R.rS + 1) * q ≤ D.R.k * D.R.m ^ 4 :=
    calc (D.R.rS + 1) * q ≤ D.R.m * (D.R.k * D.R.m ^ 3) := Nat.mul_le_mul hm1 hq
      _ = D.R.k * D.R.m ^ 4 := by ring
  have hr1 : n1 ν + (D.R.rS + 1) * q ≤ D.R.k * D.R.m ^ 5 := by
    rw [hn0, zero_add]
    exact hq1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num)))
  have hr2 : (D.R.rS + 1) * q ≤ 2 * (2 * D.R.rS + D.R.k + 1) ^ 2 := by
    refine hq1.trans (hkm.trans ?_)
    nlinarith
  have hr3 : D.R.rS * q ≤ 2 * (2 * D.R.rS + D.R.k + 1) ^ 2 :=
    (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans hr2
  let R0 : Rep D.R.k D.R.rS := { H := A.H, σ := A.σ }
  obtain ⟨hA1, hA2, hA3, -, hA5, hA6, hA7, hA8, hA9, -⟩ := hA
  rw [← heps] at hA2 hA7
  have hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (fun i => lamD D τ i + (ν i : ℝ)) := by
    rw [e0]; exact ⟨hA1, hA2⟩
  have hA7' : ∃ P, PI.UpqRep.IsCayleyU D.R.k D.R.rS (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) P ∧
      A.v0 ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (fun a => lamD D τ a + (ν a : ℝ))
        (fun g => R0.σ (P⁻¹ * g * P)) := by
    rw [e0]; exact hA7
  obtain ⟨R, hFamG, hR⟩ := family_through_gap hH _ _ _ _ _ _ _ _ _ ν R0 hNum hDS (by rw [hn0]; exact Nat.zero_le _)
  have hFam : IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R := fun ν' hν' => GlobalTheory.isDS_of_isDG (hFamG ν' hν')

  set c : ℝ := 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) with hc
  have hc2 : c = 2 * (Real.pi / D.host.v / gg D) := by rw [hc, hka, gg]; ring
  have hc0 : 0 < c := by rw [hc2]; have := Real.pi_pos; positivity
  obtain ⟨t, htG, htN, htz, hts⟩ := GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter D.R.k D.R.rS (c : ℂ) (by exact_mod_cast hc0.ne')
  choose s hs0 hs1 hs2 hs3 using hts
  have htd : IsUnit t.det := Matrix.isUnit_det_of_right_inverse (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv htG).2.1
  obtain ⟨U, U', l, l', dg, hS, -⟩ := GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w 1 W hTT one_pos hW t htG
    htN (fun z hz => (htz z hz).2) R hFam
  obtain ⟨-, -, hz, -, hTz, -, hG, -, -, -, -, -, hQ, -⟩ := hW
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hS.2.2.1
  have hSide : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨g1, g2, g3, g4, g5, haar_of_conj htd htN g6, g7, hQ⟩
  have hB := (((GlobalTheory.BesselMoveGap.bessel_move_gap hH _ _ W.Wp W.z W.π U (c : ℂ) W.μW W.μN W.μG W.νS t htG htN
    (htz _ hz).2.1 (htz _ hz).2.2 hSide).2 R0 (GlobalTheory.TensCompare.isURepOn_of_isDS hDS)).1 A.B).1 (isBesselMapSm_of hA3)
  obtain ⟨hmul, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 _ _ _ _ R0 hDS
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts g5 g6
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot g7.2.2.1 m0 m1 g8
  set νq := W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j with hνq
  have hpt : ∀ᵐ x ∂νq, A.Φ (t * Matrix.of x) = A.B (R0.σ t (R0.σ (Matrix.of x) A.v0)) := by
    filter_upwards [hae] with x hx
    exact congrArg A.B (hmul t htG _ hx A.v0)
  have e1 : l2SG W.νS A.Φ = l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) := by
    unfold l2SG
    rw [lintegral_translate W.νS t htd]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx]; rfl
  have hfr : 0 < Module.finrank ℂ W.Wp := by
    obtain ⟨_, _, -, hρ⟩ := g3
    haveI := hρ.1
    exact Module.finrank_pos
  have hne0 : l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) ≠ 0 := by
    rw [← e1, hA9]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hneT : l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) ≠ ⊤ := by
    rw [← e1, hA9]; exact ENNReal.ofReal_ne_top
  have hTz1 : 1 ≤ Tz D.R.k D.R.rS W.z := by
    rw [hTz]; unfold Tr; exact_mod_cast (le_trans (by norm_num) hTT.2.2.1)
  have hCH : (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ) ≤ (2 * |Cg| + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ) := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Cg)]
  have hpow : (large₂.sc.b ^ ((2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ))) ^ (2 * q) ≤
      (large₂.sc.b ^ ((2 * |Cg| + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ))) ^ (2 * q) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hb0 _) (Real.rpow_le_rpow_of_exponent_le hb1 hCH) _
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  have hsa : ∀ a, ‖s a‖ ≤ max (Real.pi / D.host.v / gg D) (Real.pi / D.host.v / gg D)⁻¹ ^ D.R.rS ∧
      ‖s a‖⁻¹ ≤ max (Real.pi / D.host.v / gg D) (Real.pi / D.host.v / gg D)⁻¹ ^ D.R.rS := fun a => by
    have h1 := hs1 a
    have h2 := hs2 a
    rw [Complex.norm_real, Real.norm_of_nonneg hc0.le, ← inv_div c 2, hc2,
      mul_div_cancel_left₀ _ (two_ne_zero (α := ℝ))] at h1 h2
    exact ⟨h1, h2⟩
  constructor
  · intro a
    have key := moment_of_bessel_gap hH hS ν q hr1 hr2 R0 hR _ hB A.v0 hA6 hA7' hne0 hneT a
    have hsz := size_bound (q := q) (Cu := Cu) hb hv hvb hg hgb hCg (T := Tz D.R.k D.R.rS W.z) (CT := CT)
      (r := D.R.rS) (by rw [hTz]; have := hT w; rw [hm] at this; exact_mod_cast this) (norm_nonneg (s a)) (hsa a).1
    rw [rpow_bridge hb0, ← hm'] at hsz
    rw [e1]
    refine le_trans ?_ (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hsz.trans hpow)) _)
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    refine le_trans (le_of_eq ?_) (mul_le_mul_right key _)
    rw [lintegral_translate W.νS t htd, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
      ← lenA_mul W.z t (Matrix.of x) s hs0 (fun b => hs3 b _ hz), BranchingSupport.TensInh.lenA_eq_lA]
    rfl
  · intro a
    have key := inv_moment_of_bessel_gap hH hS hTz1 ν q (by rw [hn0]; exact Nat.zero_le _) hr3 R0 hR _ hB A.v0 hA6
      hA7' hne0 hneT a
    have hsz := size_bound_inv (Cu := Cu) (CT := CT) hb hv hvb hg hgb hCg (r := D.R.rS)
      (inv_nonneg.2 (norm_nonneg (s a))) (hsa a).2
    rw [← hm'] at hsz
    have hsz2 : (‖s a‖⁻¹) ^ (2 * q) * ((large₂.sc.b ^ max 2 Cu) ^ (2 * D.R.rS)) ^ (2 * q) ≤
        (large₂.sc.b ^ ((2 * |Cg| + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ))) ^ (2 * q) := by
      rw [← mul_pow]
      exact (pow_le_pow_left₀ (by positivity) hsz _).trans hpow
    rw [e1]
    refine le_trans ?_ (mul_le_mul_left (ENNReal.ofReal_le_ofReal hsz2) _)
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    refine le_trans (le_of_eq ?_) (mul_le_mul_right key _)
    rw [lintegral_translate W.νS t htd, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow, ← mul_inv,
      ← lenA_mul W.z t (Matrix.of x) s hs0 (fun b => hs3 b _ hz), BranchingSupport.TensInh.lenA_eq_lA]
    rfl

end GlobalTheory.TwoSidedMomentsGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTwoSidedMomentsLargeGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLength_twoSidedMoments_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w (W : LocW D.R.k D.R.rS), GoodW D τ w w 1 W → ∀ A : LocS W, GoodS D (lamD D τ) A → ∀ q : ℕ, q ≤ D.R.k * D.R.m ^ 3 → MomBd W.z W.νS A.Φ q (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧ ∀ a : Fin (D.R.rS + 1), ∫⁻ x, ENNReal.ofReal ((lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤ ENNReal.ofReal ((large₂.sc.b ^ (CH * (D.R.m : ℝ))) ^ (2 * q)) * l2SG W.νS A.Φ := by
  first | exact @GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | exact GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap | (intros; apply GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap <;> assumption)
end
