module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffBumpG
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section bump

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def sqN (y : B.Mat k ρ) : ℝ := ∑ i, ∑ j, ‖y i j‖ ^ 2

theorem sqN_eq (y : B.Mat k ρ) : sqN y = B.gN y ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, Complex.normSq (y i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have h1 := Real.sq_sqrt h0
  have h2 : B.gN y = Real.sqrt (∑ i, ∑ j, Complex.normSq (y i j)) := rfl
  rw [h2, h1]
  unfold sqN
  simp only [Complex.normSq_eq_norm_sq]

theorem contDiff_sqN : ContDiff ℝ ∞ (sqN (k := k) (ρ := ρ)) := by
  unfold sqN
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hl : ContDiff ℝ ∞ (fun y : B.Mat k ρ => y i j) := contDiff_apply_apply ℝ i j
  exact (contDiff_norm_sq ℝ).comp hl

def bumpG (R : ℝ) (y : B.Mat k ρ) : ℝ := Real.smoothTransition (R ^ 2 + 1 - sqN y)

theorem contDiff_bumpG (R : ℝ) : ContDiff ℝ ∞ (bumpG (k := k) (ρ := ρ) R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_sqN)

theorem bumpG_nonneg (R : ℝ) (y : B.Mat k ρ) : 0 ≤ bumpG R y := Real.smoothTransition.nonneg _

theorem bumpG_le_one (R : ℝ) (y : B.Mat k ρ) : bumpG R y ≤ 1 := Real.smoothTransition.le_one _

theorem bumpG_eq_one {R : ℝ} {y : B.Mat k ρ} (hy : B.gN y ≤ R) : bumpG R y = 1 := by
  unfold bumpG
  apply Real.smoothTransition.one_of_one_le
  have h0 : 0 ≤ B.gN y := Real.sqrt_nonneg _
  have : B.gN y ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 hy 2
  rw [sqN_eq]; linarith

theorem bumpG_supp (R : ℝ) {y : B.Mat k ρ} (hy : bumpG R y ≠ 0) : B.gN y ≤ Real.sqrt (R ^ 2 + 1) := by
  unfold bumpG at hy
  have h : 0 < R ^ 2 + 1 - sqN y := by
    by_contra hc
    exact hy (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
  rw [sqN_eq] at h
  rw [show B.gN y = Real.sqrt (B.gN y ^ 2) from (Real.sqrt_sq (Real.sqrt_nonneg _)).symm]
  exact Real.sqrt_le_sqrt (by linarith)

end bump

section triv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def trivSet (Bj : B.RealPlaceData k ρ Wp Wq) : B.RealPlaceData k ρ ℂ ℂ where
  z := Bj.z
  z' := Bj.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := Bj.μG
  μW := Bj.μW
  μN := Bj.μN
  μW' := Bj.μW'
  μsec := Bj.μsec
  χ := Bj.χ
  k_pos := Bj.k_pos
  z_mem := Bj.z_mem
  z'_mem := Bj.z'_mem
  T_pos := Bj.T_pos
  T'_pos := Bj.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := Bj.haarG
  haarW := Bj.haarW
  haarN := Bj.haarN
  haarW' := Bj.haarW'
  sec := Bj.sec
  χ_smooth := Bj.χ_smooth
  χ_supp := Bj.χ_supp
  χ_int := Bj.χ_int

theorem norm_psi (z : Fin (2 * ρ + k + 1) → ℂ) (c : ℂ) (g : B.Mat k ρ) : ‖psi k ρ z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_xiP (Bs : B.RealPlaceData k ρ Wp Wq) (P : B.SS k ρ) : ‖JF.xiP Bs P‖ = 1 := by
  unfold JF.xiP
  rw [norm_mul, norm_star, norm_psi, norm_psi, one_mul]

theorem bump_int (Bj : B.RealPlaceData k ρ Wp Wq) {g : B.Mat k ρ} (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (R : ℝ) :
    Integrable (fun P : B.SS k ρ => bumpG R (B.sgs P g)) Bj.μSS := by
  set F : B.Mat k ρ → (ℂ →L[ℂ] ℂ) := fun y => ((bumpG R y : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) with hFdef
  have hFc : ContDiff ℝ ∞ F :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_bumpG R)).smul contDiff_const
  have hCk : B.CkOn ⊤ (B.GV k ρ) F := fun g₀ _ =>
    ⟨Set.univ, F, isOpen_univ, Set.mem_univ _, hFc.contDiffOn, fun _ _ _ => rfl⟩
  set n : ℝ := ((2 * ρ + k + 1 : ℕ) : ℝ) with hn
  set A : ℝ := 9 * ((ρ : ℝ) + 1) * (n ^ 2 + 1) with hA
  have hthr : JF.TransportedAlt k ρ A 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((ρ : ℝ) + 1) := by positivity
    have e : (A - 6 * (ρ : ℝ) * ((0 : ℕ) : ℝ)) / (9 * ((ρ : ℝ) + 1)) = n ^ 2 + 1 := by
      rw [hA]; push_cast; field_simp; ring
    rw [← hn, e]; linarith
  have hcc : B.InCC A 0 F := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hCk (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ (Real.sqrt (R ^ 2 + 1)))
    (fun y _ hyC => by
      by_contra h0
      apply hyC
      refine bumpG_supp R (fun hb => h0 ?_)
      simp [hFdef, hb]) A 0
  have hInt := (Formalism.FourierDecayAlt.P.bessel_integral_converges k ρ ℂ ℂ (trivSet Bj) A F hthr hcc).1 g hg
  refine hInt.norm.congr (ae_of_all _ fun P => ?_)
  show ‖JF.xiP (trivSet Bj) P • B.rho (trivSet Bj) P F g‖ = bumpG R (B.sgs P g)
  rw [norm_smul, norm_xiP, one_mul]
  simp only [B.rho, trivSet, hFdef]
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpG_nonneg R _)]
  simp

end triv

section fmoc

variable {k p ρ : ℕ}

theorem fmoc_RC : MeasureTheory.IsFiniteMeasureOnCompacts (U.muRC k p ρ) := by
  have h1 : IsFiniteMeasureOnCompacts (volume : Measure (Fin (2 * ρ + k + 1) → Fin p → ℂ)) := inferInstance
  have h2 : IsFiniteMeasureOnCompacts (volume : Measure ((G.UT p → ℂ) × (Fin p → ℝ))) := inferInstance
  have h3 : SigmaFinite (volume : Measure ((G.UT p → ℂ) × (Fin p → ℝ))) := inferInstance
  unfold U.muRC
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsFiniteMeasureOnCompacts _ _

theorem fmoc_Xi (σ : Equiv.Perm (Fin p)) : MeasureTheory.IsFiniteMeasureOnCompacts (U.muXi k p 0 ρ σ) := by
  have h1 : IsFiniteMeasureOnCompacts (U.muRC k p ρ) := fmoc_RC
  have h1' : SigmaFinite (U.muRC k p ρ) := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC p ρ
  have h2 : IsFiniteMeasureOnCompacts ((U.muRC k p ρ).prod (U.muRC k p ρ)) :=
    Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have a1 : IsFiniteMeasureOnCompacts (volume : Measure (Fin 0 → Fin p → ℂ)) := inferInstance
  have a2 : IsFiniteMeasureOnCompacts (volume : Measure (Fin p → Fin 0 → ℂ)) := inferInstance
  have a2' : SigmaFinite (volume : Measure (Fin p → Fin 0 → ℂ)) := inferInstance
  have a3 : IsFiniteMeasureOnCompacts (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : IsFiniteMeasureOnCompacts (volume : Measure (G.UT p → ℂ)) := inferInstance
  have a4' : SigmaFinite (volume : Measure (G.UT p → ℂ)) := inferInstance
  have b1 : IsFiniteMeasureOnCompacts (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))) := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have b2 : IsFiniteMeasureOnCompacts (volume : Measure ((U.LW σ → ℂ) × (G.UT p → ℂ))) := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have b2' : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT p → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : IsFiniteMeasureOnCompacts (U.muXiH p 0 σ) := by
    unfold U.muXiH; rw [Measure.volume_eq_prod]; exact Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have b3' : SigmaFinite (U.muXiH p 0 σ) := by
    unfold U.muXiH; rw [Measure.volume_eq_prod]; infer_instance
  unfold U.muXi
  exact Measure.prod.instIsFiniteMeasureOnCompacts _ _

end fmoc

section bound

variable {k p ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem detM_zero (Z : G.Mat 0) : G.detM Z = 1 := by
  unfold G.detM
  exact Matrix.det_isEmpty

theorem slice_bound (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k (p + 0 + ρ) → E)
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + 0 + ρ) ∧ U.DjU k (p + 0) ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + 0 + ρ), H x ≠ 0 → B.gN x ≤ R) :
    ∃ M C R' : ℝ, 0 ≤ M ∧
      Integrable (fun ξ : U.Xi k p 0 ρ σ => M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) ξ)
        (U.muXi k p 0 ρ σ) ∧ ∀ (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0) (γ : B.Mat k ρ), γ ∈ B.GV k ρ →
      ‖H (U.gaXi k ρ σ d ξ Z γ)‖ ≤
        M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) ξ * bumpG R' γ := by
  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.block3_apply_embedding k (p + 0) ρ hp
  obtain ⟨C2, hC2⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 p 0 σ d hd
  set δ0 : ℂ := (U.hMat σ d).det with hδ0
  have hδ0ne : δ0 ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd
  set m0 : ℝ := min 1 ‖δ0‖ with hm0
  have hm0pos : 0 < m0 := lt_min one_pos (norm_pos_iff.mpr hδ0ne)
  set K : Set (B.Mat k (p + 0 + ρ)) := B.GV k (p + 0 + ρ) ∩ {x | B.gN x ≤ R} ∩ {x | U.DjU k (p + 0) ρ x = δ0}
    with hKdef
  have hK : IsCompact K := by
    refine ((Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (p + 0 + ρ) R).inter_left
      (Formalism.FourierDecayAlt.P.unitary_group_closed k (p + 0 + ρ)).closed).inter_right ?_
    exact isClosed_eq (Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k (p + 0) ρ) continuous_const
  have hKsub : K ⊆ {x | x ∈ B.GV k (p + 0 + ρ) ∧ U.DjU k (p + 0) ρ x ≠ 0} := by
    rintro x ⟨⟨hx1, -⟩, hx3⟩
    exact ⟨hx1, by rw [Set.mem_setOf_eq.mp hx3]; exact hδ0ne⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hHc.mono hKsub)
  set c1 : ℝ := max C1 0 with hc1
  set c2 : ℝ := max C2 0 with hc2
  have hc1n : 0 ≤ c1 := le_max_right _ _
  have hc2n : 0 ≤ c2 := le_max_right _ _
  set R0 : ℝ := max R 0 with hR0
  have hR0n : 0 ≤ R0 := le_max_right _ _
  set B1 : ℝ := c1 * R0 ^ (p + 0) / m0 with hB1
  set B2 : ℝ := c2 * (c1 * R0) ^ p with hB2
  refine ⟨max M 0, max B1 B2, c1 * R0 ^ (2 * (p + 0) + 1) / m0 ^ 2, le_max_right _ _, ?_, fun ξ Z γ hγ => ?_⟩
  · have : MeasureTheory.IsFiniteMeasureOnCompacts (U.muXi k p 0 ρ σ) := fmoc_Xi σ
    have : BorelSpace ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) := Prod.borelSpace
    have : BorelSpace ((U.LW σ → ℂ) × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (U.XiH p 0 σ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.Xi k p 0 ρ σ) := Prod.borelSpace
    refine Integrable.const_mul ?_ _
    exact (integrableOn_const (measure_closedBall_lt_top).ne).integrable_indicator measurableSet_closedBall
  have hZ1 : G.detM Z = 1 := detM_zero Z
  by_cases h0 : H (U.gaXi k ρ σ d ξ Z γ) = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      (bumpG_nonneg _ _)
  have hG := Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ Z
    (by rw [hZ1]; exact one_ne_zero) hγ
  have hgR := hR _ hG h0
  have hgN0 : 0 ≤ B.gN (U.gaXi k ρ σ d ξ Z γ) := Real.sqrt_nonneg _
  have hgR0 : B.gN (U.gaXi k ρ σ d ξ Z γ) ≤ R0 := hgR.trans (le_max_left _ _)
  have hD : U.DjU k (p + 0) ρ (U.gaXi k ρ σ d ξ Z γ) = δ0 := by
    rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hZ1, mul_one]
  have hMb : ‖H (U.gaXi k ρ σ d ξ Z γ)‖ ≤ max M 0 := (hM _ ⟨⟨hG, hgR⟩, hD⟩).trans (le_max_left _ _)

  have hdetZ : (U.ZjH σ d ξ.2 Z).det ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.level_determinant_z, hZ1, mul_one]; exact hδ0ne
  have hdetZ' : ‖(U.ZjH σ d ξ.2 Z).det‖ = ‖δ0‖ := by
    rw [Formalism.FourierDecayAlt.P.level_determinant_z, hZ1, mul_one]
  obtain ⟨b1, b2, b3, -, b5⟩ := hC1 ξ.1.1 ξ.1.2 (U.ZjH σ d ξ.2 Z) γ hdetZ hγ
  have hgaXi : U.gaXi k ρ σ d ξ Z γ =
      (U.Rn k (p + 0) ρ ξ.1.1)⁻¹ * U.mMap k (p + 0) ρ (U.ZjH σ d ξ.2 Z) γ * U.Rn k (p + 0) ρ ξ.1.2 := rfl
  rw [← hgaXi, hdetZ', ← hm0] at b1 b2 b5
  rw [← hgaXi] at b3
  have hpow : ∀ n : ℕ, B.gN (U.gaXi k ρ σ d ξ Z γ) ^ n ≤ R0 ^ n := fun n => pow_le_pow_left₀ hgN0 hgR0 n
  have bx1 : ‖ξ.1.1‖ ≤ B1 := by
    refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.1).trans (b1.trans ?_)
    rw [hB1]
    exact div_le_div_of_nonneg_right (mul_le_mul (le_max_left _ _) (hpow _) (pow_nonneg hgN0 _) hc1n) hm0pos.le
  have bx2 : ‖ξ.1.2‖ ≤ B1 := by
    refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.2).trans (b2.trans ?_)
    rw [hB1]
    exact div_le_div_of_nonneg_right (mul_le_mul (le_max_left _ _) (hpow _) (pow_nonneg hgN0 _) hc1n) hm0pos.le
  have hmx : U.mx (U.ZjH σ d ξ.2 Z) ≤ c1 * R0 :=
    b3.trans (mul_le_mul (le_max_left _ _) hgR0 hgN0 hc1n)
  have hmx0 : 0 ≤ U.mx (U.ZjH σ d ξ.2 Z) := norm_nonneg _
  obtain ⟨e1, e2, e3, e4, -⟩ := hC2 ξ.2 Z
  have hη : ∀ t : ℝ, t ≤ C2 * U.mx (U.ZjH σ d ξ.2 Z) ^ p → t ≤ B2 := fun t ht =>
    ht.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hmx0 hmx p) (pow_nonneg hmx0 _) hc2n)
  have hξ : ‖ξ‖ ≤ max B1 B2 := by
    rw [norm_prod_le_iff]
    refine ⟨?_, ?_⟩
    · rw [norm_prod_le_iff]
      exact ⟨bx1.trans (le_max_left _ _), bx2.trans (le_max_left _ _)⟩
    · rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
      exact ⟨⟨(hη _ e1).trans (le_max_right _ _), (hη _ e2).trans (le_max_right _ _)⟩,
        ⟨(hη _ e3).trans (le_max_right _ _), (hη _ e4).trans (le_max_right _ _)⟩⟩
  have hind : (Metric.closedBall (0 : U.Xi k p 0 ρ σ) (max B1 B2)).indicator (fun _ => (1 : ℝ)) ξ = 1 := by
    rw [Set.indicator_of_mem (by rw [Metric.mem_closedBall, dist_zero_right]; exact hξ)]
  have hbump : bumpG (c1 * R0 ^ (2 * (p + 0) + 1) / m0 ^ 2) γ = 1 := by
    apply bumpG_eq_one
    refine b5.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul (le_max_left _ _) (hpow _) (pow_nonneg hgN0 _) hc1n)
      (pow_nonneg hm0pos.le _)
  rw [hind, hbump, mul_one, mul_one]
  exact hMb

end bound

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightCosetActionMeasurePreserving
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section embG

variable {k p ρ : ℕ}

theorem embG_mul (a b : B.Mat k ρ) : U.embG k p ρ (a * b) = U.embG k p ρ a * U.embG k p ρ b := by
  simp only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem embG_one' : U.embG k p ρ (1 : B.Mat k ρ) = 1 := by
  ext i j
  obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective j
  simp only [Matrix.one_apply, (U.eB k p ρ).injective.eq_iff]
  simp only [U.embG, U.blk3, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with (a | b) | c <;> rcases y with (a' | b') | c' <;> simp [Matrix.one_apply]

theorem embG_inv {a : B.Mat k ρ} (ha : IsUnit a.det) : U.embG k p ρ a⁻¹ = (U.embG k p ρ a)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← embG_mul, Matrix.nonsing_inv_mul _ ha, embG_one']

end embG

section muN

variable {k : ℕ}

def psiL (k p ρ : ℕ) (x : U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ)) : Mt k (p + ρ) :=
  Matrix.of.symm (U.embG k p ρ (Matrix.of x.2.2) * U.muP k p ρ (G.upper x.2.1) * U.Rn k p ρ x.1)

theorem psiL_cont (p ρ : ℕ) : Continuous (psiL k p ρ) := by
  unfold psiL
  exact (((Formalism.FourierDecayAlt.P.Dx2.SplitF.embg_cont (k := k) p ρ).comp (continuous_snd.comp continuous_snd)).matrix_mul
    ((Formalism.FourierDecayAlt.P.Dx2.SplitF.mup_cont (k := k) p ρ).comp (continuous_fst.comp continuous_snd))).matrix_mul
    ((Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_fst)

theorem psiL_meas (p ρ : ℕ) : Measurable (psiL k p ρ) := by
  have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace ((G.UT p → ℂ) × Mt k ρ) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ)) := Prod.borelSpace
  exact (psiL_cont p ρ).measurable

theorem unipotent_measure_left_invariant : MuNLeft := by
  intro k p ρ
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_muN (k := k) ρ
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite (volume : Measure (G.UT p → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  have hs := Formalism.FourierDecayAlt.P.Dx2.SplitF.split_all (k := k) p ρ
  have hinv := Formalism.FourierDecayAlt.P.haar_measure_inversion k (p + ρ) (Nset k (p + ρ)) (D.muN k (p + ρ))
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)) (Formalism.FourierDecayAlt.P.Dx2.MN.haar (k := k) (p + ρ))
  have hinvρ := Formalism.FourierDecayAlt.P.haar_measure_inversion k ρ (Nset k ρ) (D.muN k ρ)
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ) (Formalism.FourierDecayAlt.P.Dx2.MN.haar (k := k) ρ)
  set μ := (U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ)) with hμ
  set T : U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ) → U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ) :=
    fun z => (-z.1, (Formalism.FourierDecayAlt.P.PBM.utInv p z.2.1, B2.invM z.2.2)) with hT
  have hTmp : MeasurePreserving T μ μ :=
    Formalism.FourierDecayAlt.P.PBM.negRC_mp.prod ((Formalism.FourierDecayAlt.P.PBM.utInv_mp p).prod ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.invM_meas, hinvρ⟩)
  have hae : ∀ᵐ z ∂μ, (Matrix.of z.2.2 : B.Mat k ρ) ∈ Nset k ρ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae
      (Formalism.FourierDecayAlt.P.B5.haar_ae (Formalism.FourierDecayAlt.P.Dx2.MN.haar (k := k) ρ)))
  have hfun : (B2.invM ∘ Formalism.FourierDecayAlt.P.Dx2.SplitF.Psi k p ρ) =ᵐ[μ] (psiL k p ρ ∘ T) := by
    filter_upwards [hae] with z hz
    obtain ⟨x, q, y⟩ := z
    have hy : IsUnit (Matrix.of y : B.Mat k ρ).det := Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_unit (Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ) hz.1
    have hu : IsUnit (G.upper q).det := by
      rw [Formalism.FourierDecayAlt.P.StabilizerDisintegration.UC.det_UT (Formalism.FourierDecayAlt.P.StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
    show Matrix.of.symm ((Matrix.of (Matrix.of.symm (U.Rn k p ρ x * U.muP k p ρ (G.upper q) *
        U.embG k p ρ (Matrix.of y))))⁻¹) =
      Matrix.of.symm (U.embG k p ρ (Matrix.of (B2.invM y)) * U.muP k p ρ (G.upper (Formalism.FourierDecayAlt.P.PBM.utInv p q)) *
        U.Rn k p ρ (-x))
    rw [Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Formalism.FourierDecayAlt.P.PBM.rn_inv,
      Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hu, Formalism.FourierDecayAlt.P.PBM.upper_utInv, ← embG_inv hy]
    simp only [Matrix.mul_assoc]
    rfl
  rw [← hinv, hs, Measure.map_map Formalism.FourierDecayAlt.P.TwoByOneBlock.invM_meas (Formalism.FourierDecayAlt.P.Dx2.SplitF.psi_meas p ρ),
    Measure.map_congr hfun, ← Measure.map_map (psiL_meas p ρ) hTmp.measurable, hTmp.map_eq]
  rfl

end muN

section rc

variable {k p ρ : ℕ}

def actLin (y : B.Mat k ρ) : (Fin (2 * ρ + k + 1) → Fin p → ℂ) →ₗ[ℂ] (Fin (2 * ρ + k + 1) → Fin p → ℂ) where
  toFun c := fun v a => (y * Matrix.of c) v a
  map_add' c c' := by funext v a; rw [← Matrix.of_add_of, Matrix.mul_add]; rfl
  map_smul' t c := by funext v a; rw [← Matrix.smul_of, Matrix.mul_smul]; rfl

def swapL : (Fin (2 * ρ + k + 1) → Fin p → ℂ) ≃ₗ[ℂ] (Fin p → Fin (2 * ρ + k + 1) → ℂ) where
  toFun c := fun a v => c v a
  invFun c := fun v a => c a v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_actLin (y : B.Mat k ρ) : LinearMap.det (actLin (p := p) y) = y.det ^ p := by
  have e : actLin (p := p) y = (swapL (k := k) (ρ := ρ) (p := p)).symm.conj
      (LinearMap.pi fun a : Fin p => Matrix.toLin' y ∘ₗ LinearMap.proj a) := by
    apply LinearMap.ext
    intro c
    funext v a
    simp [actLin, swapL, LinearEquiv.conj_apply, Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

theorem rcAct_fst_mp (y : B.Mat k ρ) (hy : ‖y.det‖ = 1) :
    MeasurePreserving (fun c : Fin (2 * ρ + k + 1) → Fin p → ℂ => fun v a => (y * Matrix.of c) v a) volume volume := by
  have := Formalism.FourierDecayAlt.P.HermitianFormFactor.isAddHaarMeasure_matrix_volume (A := Fin (2 * ρ + k + 1)) (B := Fin p)
  have hdet : LinearMap.det ((actLin (p := p) y).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, det_actLin, Algebra.norm_complex_apply, map_pow,
      Complex.normSq_eq_norm_sq, hy]; norm_num
  have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin (2 * ρ + k + 1) → Fin p → ℂ))
    (f := (actLin (p := p) y).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h1
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h1
  exact ⟨(LinearMap.continuous_of_finiteDimensional ((actLin (p := p) y).restrictScalars ℝ)).measurable, h1⟩

theorem right_coset_action_measure_preserving : RcActMP := by
  intro k p ρ y hy
  unfold U.muRC
  rw [Measure.volume_eq_prod]
  exact (rcAct_fst_mp y hy).prod (MeasurePreserving.id _)

end rc

section right

theorem rcAct_cont {k p ρ : ℕ} :
    Continuous (fun q : Mt k ρ × U.RC k p ρ => rcAct (Matrix.of q.1) q.2) := by
  unfold rcAct
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    apply continuous_pi
    intro a
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  · fun_prop

theorem right_measure_preserving : RightMP := by
  intro k p ρ z' μj μ0' hH h1 hμ0
  have : IsFiniteMeasure μj := ⟨by rw [h1]; exact ENNReal.one_lt_top⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_muN (k := k) ρ
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_muN (k := k) (p + ρ)
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite (volume : Measure (G.UT p → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  have : IsFiniteMeasure μ0' := by rw [hμ0]; infer_instance

  have s1 := measurePreserving_prodAssoc μj (D.muN k ρ) ((U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))

  set g : Mt k ρ → Mt k ρ × (U.RC k p ρ × (G.UT p → ℂ)) → U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ) :=
    fun h' w => (rcAct (Matrix.of h') w.2.1, (w.2.2, w.1)) with hg
  have hgm : Measurable (Function.uncurry g) := by
    have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × (U.RC k p ρ × (G.UT p → ℂ))) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × (Mt k ρ × (U.RC k p ρ × (G.UT p → ℂ)))) := Prod.borelSpace
    have : BorelSpace ((G.UT p → ℂ) × Mt k ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × ((G.UT p → ℂ) × Mt k ρ)) := Prod.borelSpace
    have hc : Continuous (Function.uncurry g) := by
      refine Continuous.prodMk ?_ ?_
      · exact rcAct_cont.comp (continuous_fst.prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      · exact (continuous_snd.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd)
    exact hc.measurable
  have hae : ∀ᵐ h' ∂μj, Measure.map (g h') ((D.muN k ρ).prod ((U.muRC k p ρ).prod volume)) =
      (U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae hH] with h' hh'
    have hdet : ‖(Matrix.of h' : B.Mat k ρ).det‖ = 1 :=
      Formalism.FourierDecayAlt.P.HermitianFormFactor.det_norm_one (Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ) hh'.1
    have a1 := Measure.measurePreserving_swap (μ := D.muN k ρ) (ν := (U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))
    have a2 := measurePreserving_prodAssoc (U.muRC k p ρ) (volume : Measure (G.UT p → ℂ)) (D.muN k ρ)
    have a3 := (right_coset_action_measure_preserving k p ρ (Matrix.of h') hdet).prod
      (MeasurePreserving.id ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ)))
    exact (a3.comp (a2.comp a1)).map_eq
  have s2 := (MeasurePreserving.id μj).skew_product hgm hae

  have hlev : MeasurePreserving (Formalism.FourierDecayAlt.P.PBM.levMt (k := k) p ρ rfl) μj μ0' :=
    ⟨(Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).measurable, hμ0.symm⟩
  have hN : MeasurePreserving (psiL k p ρ)
      ((U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ))) (D.muN k (p + ρ)) :=
    ⟨psiL_meas p ρ, (unipotent_measure_left_invariant k p ρ).symm⟩
  have s3 := hlev.prod hN
  exact s3.comp (s2.comp s1)

end right

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vars

variable (k p ρ : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

abbrev XL (σ : Equiv.Perm (Fin p)) : Type :=
  (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)))

abbrev XR : Type := (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (G.UT p → ℂ))

variable {k p ρ}

def muL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) : Measure (XL k p ρ σ) :=
  (Bj.μW.prod Bj.μN).prod ((U.muRC k p ρ).prod
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ))))

def muR (Bj : B.RealPlaceData k ρ Wp Wq) : Measure (XR k p ρ) :=
  (Bj.μW'.prod Bj.μN).prod ((U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))

def splitE (σ : Equiv.Perm (Fin p)) : B.SS k ρ × U.Xi k p 0 ρ σ ≃ᵐ XL k p ρ σ × XR k p ρ where
  toFun q := ((q.1.1, (q.2.1.1, (q.2.2.1, q.2.2.2.1))), (q.1.2, (q.2.1.2, q.2.2.2.2)))
  invFun x := ((x.1.1, x.2.1), ((x.1.2.1, x.2.2.1), (x.1.2.2.1, (x.1.2.2.2, x.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable fun q : B.SS k ρ × U.Xi k p 0 ρ σ =>
      ((q.1.1, (q.2.1.1, (q.2.2.1, q.2.2.2.1))), (q.1.2, (q.2.1.2, q.2.2.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun x : XL k p ρ σ × XR k p ρ =>
      ((x.1.1, x.2.1), ((x.1.2.1, x.2.2.1), (x.1.2.2.1, (x.1.2.2.2, x.2.2.2))))
    fun_prop

theorem splitE_mp (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (splitE σ) (Bj.μSS.prod (U.muXi k p 0 ρ σ)) ((muL Bj σ).prod (muR Bj)) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : SigmaFinite Bj.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have hXi : U.muXi k p 0 ρ σ = ((U.muRC k p ρ).prod (U.muRC k p ρ)).prod
      ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        ((volume : Measure (U.LW σ → ℂ)).prod (volume : Measure (G.UT p → ℂ)))) := by
    unfold U.muXi U.muXiH
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod (α := U.LW σ → ℂ)]
    rfl

  have h1 := (measurePreserving_prodAssoc
    (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))) (volume : Measure (U.LW σ → ℂ))
    (volume : Measure (G.UT p → ℂ))).symm
  have h2 := (MeasurePreserving.id ((U.muRC k p ρ).prod (U.muRC k p ρ))).prod h1
  have h3 := Formalism.FourierDecayAlt.P.Dx2.SplitM.middle_four_swap_measure_preserving (U.muRC k p ρ) (U.muRC k p ρ)
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))
    (volume : Measure (G.UT p → ℂ))
  have h4 := (MeasurePreserving.id Bj.μSS).prod (h3.comp h2)
  have h5 := Formalism.FourierDecayAlt.P.Dx2.SplitM.middle_four_swap_measure_preserving (Bj.μW.prod Bj.μN) (Bj.μW'.prod Bj.μN)
    ((U.muRC k p ρ).prod
      ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ))))
    ((U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))
  rw [hXi]
  have hall := h5.comp h4
  convert hall using 1
  · funext q; rfl
  · rfl

end vars

section defs

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def GoodL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : Prop :=
  (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧ (Matrix.of x.1.2 : B.Mat k ρ) ∈ Nset k ρ

def GoodR (Bj : B.RealPlaceData k ρ Wp Wq) (y : XR k p ρ) : Prop :=
  (Matrix.of y.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z' ∧ (Matrix.of y.1.2 : B.Mat k ρ) ∈ Nset k ρ


open Classical in
def sxL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : B.Mat k (p + ρ) :=
  if GoodL Bj σ x then
    U.Rn k p ρ (-x.2.1) * U.muP k p ρ (lhOf σ x.2.2.2)ᴴ⁻¹ *
      U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
  else 1

def cL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : ℂ :=
  psi k ρ Bj.z cStd (Matrix.of x.1.2) * psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ x.2.1) *
    G.psi U.betaU (U.subS (lhOf σ x.2.2.2))

def ellL (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  cL Bj σ x • ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1))

def NR (y : XR k p ρ) : B.Mat k (p + ρ) :=
  U.embG k p ρ (Matrix.of y.1.2) * U.muP k p ρ (G.upper y.2.2) * U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1)

def PsiR (y : XR k p ρ) : Mt k (p + ρ) × Mt k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl y.1.1, Matrix.of.symm (NR y))

def KrI (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ))
    (q : Mt k (p + ρ) × Mt k (p + ρ)) : Wq →L[ℂ] Wp :=
  star (psi k (p + ρ) B0.z' cStd (Matrix.of q.2)) • (H (y₀ * Matrix.of q.2 * Matrix.of q.1)).comp (B0.π' (Matrix.of q.1)⁻¹)

theorem kr_eq_int (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ)) :
    PBG.Kr B0 H y₀ = ∫ q, KrI B0 H y₀ q ∂(B0.μW'.prod B0.μN) := rfl

def FL (Bj : B.RealPlaceData k ρ Wp Wq) (z0 z0' : Fin (2 * (p + ρ) + k + 1) → ℂ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (q : B.SS k ρ × U.Xi k p 0 ρ σ) : Wq →L[ℂ] Wp :=
  JF.xiP Bj q.1 • (Bj.π (Matrix.of q.1.1.1)).comp
    ((U.psiStar k ρ σ z0 z0' q.2 • H (U.gaXi k ρ σ d q.2 (fun a => a.elim0) (B.sgs q.1 g))).comp
      (Bj.π' (Matrix.of q.1.2.1)⁻¹))

end defs

section djU

variable {k p m : ℕ}

theorem n_col (nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) (b : Fin p) (c : Fin (2 * (p + m) + k + 1))
    (hc : b.val ≤ c.val) : nn c ⟨b.val, by omega⟩ = if c.val = b.val then 1 else 0 := by
  have h := hn.2.1 ⟨b.val, by omega⟩ c hc
  have e : eI k (p + m) ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := rfl
  rw [e] at h
  rw [h]
  by_cases hcb : c.val = b.val
  · rw [if_pos (Fin.ext hcb), if_pos hcb]
  · rw [if_neg (fun h' => hcb (congrArg Fin.val h')), if_neg hcb]

theorem zh_mul_N (g nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) :
    U.Zh k p m (g * nn) = U.Zh k p m g * Matrix.of (fun c b : Fin p => nn ⟨c.val, by omega⟩ ⟨b.val, by omega⟩) := by
  ext a b
  simp only [U.Zh, Matrix.mul_apply, Matrix.of_apply]
  symm
  refine Finset.sum_bij_ne_zero (fun c _ _ => (⟨c.val, by omega⟩ : Fin (2 * (p + m) + k + 1))) ?_ ?_ ?_ ?_
  · intro c _ _; exact Finset.mem_univ _
  · intro c₁ _ _ c₂ _ _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro c _ hc
    have hcp : c.val < p := by
      by_contra hcp
      apply hc
      rw [n_col nn hn b c (by omega), if_neg (by omega), mul_zero]
    exact ⟨⟨c.val, hcp⟩, Finset.mem_univ _, by simpa using hc, rfl⟩
  · intro c _ _; rfl

theorem det_N_block (nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) :
    (Matrix.of (fun c b : Fin p => nn ⟨c.val, by omega⟩ ⟨b.val, by omega⟩)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun c _ => ?_
    simp only [Matrix.of_apply]
    rw [n_col nn hn c _ le_rfl, if_pos rfl]
  · intro c b hcb
    have hcb' : b.val < c.val := hcb
    simp only [Matrix.of_apply]
    rw [n_col nn hn b _ (le_of_lt hcb'), if_neg (by simp only; omega)]

theorem djU_mul_N (g nn : B.Mat k (p + m)) (hn : nn ∈ Nset k (p + m)) : U.DjU k p m (g * nn) = U.DjU k p m g := by
  unfold U.DjU
  rw [zh_mul_N g nn hn, Matrix.det_mul, det_N_block nn hn, mul_one]

theorem djU_mul_UW (z : Fin (2 * (p + m) + k + 1) → ℂ) (g h : B.Mat k (p + m)) (hh : h ∈ UWset k (p + m) z) :
    U.DjU k p m (g * h) = U.DjU k p m g := by
  unfold U.DjU
  congr 1
  ext a b
  simp only [U.Zh, Matrix.mul_apply]
  have hcol : ∀ c : Fin (2 * (p + m) + k + 1), h c ⟨b.val, by omega⟩ = if c.val = b.val then 1 else 0 := by
    intro c
    have h1 := congrFun (hh.2.1 ⟨b.val, by omega⟩).1 c
    have e : eI k (p + m) ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := rfl
    rw [e] at h1
    rw [← Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply h ⟨b.val, by omega⟩ c, h1]
    unfold bvec
    by_cases hcb : c.val = b.val
    · rw [if_pos hcb, Pi.single_apply, if_pos (Fin.ext hcb)]
    · rw [if_neg hcb, Pi.single_apply, if_neg (fun h' => hcb (congrArg Fin.val h'))]
  rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
  · rw [hcol, if_pos rfl, mul_one]
  · intro c _ hc
    rw [hcol, if_neg (fun h' => hc (Fin.ext h')), mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end djU

section split

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gpsi_add (β a b : ℂ) : G.psi β (a + b) = G.psi β a * G.psi β b := by
  unfold G.psi
  rw [← Complex.exp_add, mul_add, Complex.add_re, Complex.ofReal_add, mul_add]

theorem cornerA_zero {p : ℕ} (a : Fin 0 → Fin p → ℂ) : U.cornerA a = 0 := by
  unfold U.cornerA; rw [dite_eq_right (fun h => absurd h.1 (lt_irrefl 0))]

theorem cornerB_zero {p : ℕ} (b : Fin p → Fin 0 → ℂ) : U.cornerB b = 0 := by
  unfold U.cornerB; rw [dite_eq_right (fun h => absurd h.1 (lt_irrefl 0))]

theorem of_levMt (x : Mt k ρ) : (Matrix.of (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl x) : B.Mat k (p + ρ)) =
    U.embG k p ρ (Matrix.of x) := by
  unfold Formalism.FourierDecayAlt.P.PBM.levMt
  rw [Equiv.apply_symm_apply, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]

theorem fl_split (hGS : GaXiSplit) (hPR : PsiRight) (hPA : PsiRnAct) (hPM : PsiMuP)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (x : XL k p ρ σ) (y : XR k p ρ)
    (hx : GoodL Bj σ x) (hy : GoodR Bj y) :
    FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g ((splitE σ).symm (x, y)) =
      ellL Bj σ x (KrI B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g) (PsiR y)) := by
  obtain ⟨hh, hν⟩ := hx
  obtain ⟨hh', hν'⟩ := hy
  have uh : IsUnit (Matrix.of x.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z).unit _ hh
  have uν : IsUnit (Matrix.of x.1.2 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).unit _ hν
  have uh' : IsUnit (Matrix.of y.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z').unit _ hh'
  have hH' : (Matrix.of y.1.1 : B.Mat k ρ)ᴴ * Hpk k ρ * Matrix.of y.1.1 = Hpk k ρ := hh'.1

  have hpt : U.gaXi k ρ σ d ((splitE σ).symm (x, y)).2 (fun a => a.elim0) (B.sgs ((splitE σ).symm (x, y)).1 g) =
      sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g * Matrix.of (PsiR y).2 * Matrix.of (PsiR y).1 := by
    have := hGS k p ρ σ d ((splitE σ).symm (x, y)).2 (fun a => a.elim0) (Matrix.of x.1.1) (Matrix.of x.1.2)
      (Matrix.of y.1.1) (Matrix.of y.1.2) g uh uν hH'
    rw [show B.sgs ((splitE σ).symm (x, y)).1 g = (Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g *
      Matrix.of y.1.2 * Matrix.of y.1.1 from rfl]
    convert this using 1
    simp only [sxL, if_pos (show GoodL Bj σ x from ⟨hh, hν⟩), PsiR, NR, of_levMt, Equiv.apply_symm_apply]
    rfl

  have hpi : B0.π' (Matrix.of (PsiR y).1)⁻¹ = Bj.π' (Matrix.of y.1.1)⁻¹ := by
    simp only [PsiR, of_levMt]
    rw [← Formalism.FourierDecayAlt.P.LeftFubiniLemmas.embG_inv uh', hπ']

  have hN : psi k (p + ρ) B0.z' cStd (Matrix.of (PsiR y).2) =
      psi k ρ Bj.z' cStd (Matrix.of y.1.2) * psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper y.2.2)) *
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.Rn k p ρ y.2.1) := by
    simp only [PsiR, NR, Equiv.apply_symm_apply, hz']
    rw [hPR k p ρ Bj.z' _ _ _ Bj.z'_mem hν', hPA k p ρ Bj.z' _ _ Bj.z'_mem hh']
  have hM := hPM k p ρ Bj.z' y.2.2 Bj.z'_mem
  have hS : U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') ((splitE σ).symm (x, y)).2 =
      psi k (p + ρ) (liftVec k p ρ Bj.z) cStd (U.Rn k p ρ x.2.1) *
        star (psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.Rn k p ρ y.2.1)) *
        (G.psi U.betaU (U.subS (lhOf σ x.2.2.2)) * G.psi U.betaU (U.supS (G.upper y.2.2))) := by
    simp only [U.psiStar, U.psiH, splitE, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      cornerA_zero, cornerB_zero, add_zero, gpsi_add]
    rfl
  unfold FL ellL KrI
  rw [hpt, hpi, hS, hN]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp, smul_smul, JF.xiP, cL, star_mul', ← hM]
  congr 1
  · simp only [splitE, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk]
    ring

end split

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
