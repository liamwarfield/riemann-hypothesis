module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulNearOneLuSplitSmallChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulNearOneLuSplitSmallChart
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.LUNear

open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf Metric

theorem lmulC_split_near_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      IsOrth X x → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : X.Ψ → Matrix (Fin r) (Fin r) ℂ,
        (∀ τ a b, ‖m τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε) →
          ∃ z : V (nd X), ‖z‖ < δ ∧ ∃ b ∈ Bor X.Ψ r, X.lmulC m x = rmul (cpt X x z) b := by
  intro E _ _ _ r X x hx δ hδ
  have hdom : x ∈ X.dom := KU.orth_dom X hx
  have hU : IsOpen (cellL X x) :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (Delta_diff (x0 := x)).continuous continuous_const)
  have hxU : x ∈ cellL X x := ⟨hdom, by rw [orthogonalFrame_delta_eq_one hx]; exact one_ne_zero⟩
  have hz0 : zF X x x = 0 := by
    have h := (uniq_all hx (z := 0) (ExtFPf.oneF_mem X)).2.1
    rwa [PoinPf.cpt_zero, ExtFPf.rmul_oneF] at h
  have hzc : ContinuousAt (zF X x) x :=
    ((zF_diffOn (x0 := x)).continuousOn).continuousAt (hU.mem_nhds hxU)
  have hS : {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 x := by
    change cellL X x ∩ {y | ‖zF X x y‖ < δ} ∈ 𝓝 x
    refine Filter.inter_mem (hU.mem_nhds hxU) ?_
    have : ∀ᶠ y in 𝓝 x, ‖zF X x y‖ < δ :=
      hzc.norm.eventually (Iio_mem_nhds (by show ‖zF X x x‖ < δ; rw [hz0, norm_zero]; exact hδ))
    exact this

  let g : Frame X.Ψ r → Frame X.Ψ r := fun M τ a c => ∑ k, M τ a k * x τ k c
  have hg : Continuous g := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    refine continuous_finsetSum _ fun k _ => ?_
    fun_prop
  have hg1 : g (ExtFPf.oneF X) = x := by
    funext τ a c
    simp [g, ExtFPf.oneF, Matrix.one_apply]
  have hpre : g ⁻¹' {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 (ExtFPf.oneF X) := by
    refine hg.continuousAt.preimage_mem_nhds ?_
    rw [hg1]; exact hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hε, fun m hm => ?_⟩
  let M : Frame X.Ψ r := fun τ a c => m τ a c
  have hM : M ∈ ball (ExtFPf.oneF X) ε := by
    rw [mem_ball, dist_pi_lt_iff hε]; intro τ
    rw [dist_pi_lt_iff hε]; intro a
    rw [dist_pi_lt_iff hε]; intro c
    rw [dist_eq_norm]
    exact hm τ a c
  have hgM : X.lmulC m x = g M := by
    funext τ a c
    rfl
  obtain ⟨⟨hyd, hyΔ⟩, hyz⟩ := hball hM
  refine ⟨zF X x (g M), hyz, bF X x (g M), bF_mem hyd hyΔ, ?_⟩
  rw [hgM]
  exact split_eq hx (g M)

end GlobalTheory.LUNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulNearOneLuSplitSmallChartStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftMul_near_one_lu_split_small_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : X.Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ τ a b, ‖m τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε) → ∃ z : V (nd X), ‖z‖ < δ ∧ ∃ b ∈ Bor X.Ψ r, X.lmulC m x = rmul (cpt X x z) b := by
  first | exact @GlobalTheory.LUNear.lmulC_split_near_one | exact GlobalTheory.LUNear.lmulC_split_near_one | (intros; apply GlobalTheory.LUNear.lmulC_split_near_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPhaseFrameSmallAngles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPhaseFrameSmallAngles
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.RiemConst

lemma exp_I_arg_exp_I (t : ℝ) :
    Complex.exp (Complex.I * ((Complex.exp (Complex.I * (t : ℂ))).arg : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) := by
  have h := Complex.norm_mul_exp_arg_mul_I (Complex.exp (Complex.I * (t : ℂ)))
  have h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I t
  rw [h1] at h
  simpa [mul_comm] using h

lemma exp_I_neg_sum {n : ℕ} (f : Fin n → ℝ) :
    Complex.exp (Complex.I * ((-∑ k, f k : ℝ) : ℂ)) =
      (∏ k, Complex.exp (Complex.I * (f k : ℂ)))⁻¹ := by
  push_cast
  rw [mul_neg, Complex.exp_neg, Finset.mul_sum, Complex.exp_sum]

theorem phaseFrame_small_angles : ∀ (E : Type) [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (δ : ℝ), 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ θ : Ψ → Fin (r - 1) → ℝ, (∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η) → ∃ θ' : Ψ → Fin (r - 1) → ℝ, ‖θ'‖ < δ ∧ phaseFrame θ' = phaseFrame θ := by
  intro E _ Ψ r δ hδ
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (Complex.continuousAt_arg (Complex.one_mem_slitPlane)) δ hδ
  refine ⟨η, hη, fun θ hθ => ?_⟩
  refine ⟨fun τ k => (Complex.exp (Complex.I * (θ τ k : ℂ))).arg, ?_, ?_⟩
  · rw [pi_norm_lt_iff hδ]
    intro τ
    rw [pi_norm_lt_iff hδ]
    intro k
    have hk := hθ τ (Fin.castLE (Nat.sub_le r 1) k)
    have hentry : phaseFrame θ τ (Fin.castLE (Nat.sub_le r 1) k) (Fin.castLE (Nat.sub_le r 1) k)
        = Complex.exp (Complex.I * (θ τ k : ℂ)) := by
      simp only [phaseFrame, Matrix.diagonal_apply_eq, angles, Fin.coe_castLE, k.isLt, dif_pos]
    rw [hentry] at hk
    have := hcont (x := Complex.exp (Complex.I * (θ τ k : ℂ))) (by rwa [dist_eq_norm])
    rw [Complex.arg_one, Real.dist_eq, sub_zero] at this
    simpa [Real.norm_eq_abs] using this
  · funext τ
    simp only [phaseFrame]
    congr 1
    funext a
    unfold angles
    split_ifs with h
    · exact exp_I_arg_exp_I _
    · rw [exp_I_neg_sum, exp_I_neg_sum]
      congr 1
      exact Finset.prod_congr rfl fun k _ => exp_I_arg_exp_I _

end GlobalTheory.RiemConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPhaseFrameSmallAnglesStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalPhaseFrame_small_angles : ∀ (E : Type) [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (δ : ℝ), 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ θ : Ψ → Fin (r - 1) → ℝ, (∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η) → ∃ θ' : Ψ → Fin (r - 1) → ℝ, ‖θ'‖ < δ ∧ phaseFrame θ' = phaseFrame θ := by
  first | exact @GlobalTheory.RiemConst.phaseFrame_small_angles | exact GlobalTheory.RiemConst.phaseFrame_small_angles | (intros; apply GlobalTheory.RiemConst.phaseFrame_small_angles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvSectionMulEntriesNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvSectionMulEntriesNearOne
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.SUVol

theorem conj_inv_section_mul_entries_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm), IsOrth X x → σ 0 = 1 → ContinuousAt σ 0 → ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ z : V (nd X), ‖z‖ < κ → ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∀ τ a b, ‖((mat x τ)⁻¹ * (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < η := by
  intro E _ _ _ r X x σ hx hσ0 hσc η hη
  classical
  let One : X.Ψ → Fin r → Fin r → ℂ := fun _ a b => (1 : Matrix (Fin r) (Fin r) ℂ) a b
  let F : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) → (X.Ψ → Fin r → Fin r → ℂ) :=
    fun PQ τ => (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
  have hFc : Continuous F := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.1 τ) :=
      (continuous_apply τ).comp continuous_fst
    have h2 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.2 τ) :=
      (continuous_apply τ).comp continuous_snd
    show Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
      (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
    exact (continuous_const.matrix_mul (h1.matrix_mul h2)).matrix_mul continuous_const
  have hF1 : F (One, One) = One := by
    funext τ
    have hu : IsUnit (mat x τ).det :=
      isUnit_iff_ne_zero.mpr (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ)
    have h1 : Matrix.of (One τ) = 1 := rfl
    show (mat x τ)⁻¹ * (Matrix.of (One τ) * Matrix.of (One τ)) * mat x τ = Matrix.of (One τ)
    rw [h1, Matrix.mul_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hFc.continuousAt (ε := η) hη
  rw [hF1] at hδF
  let A : V (nd X) → (X.Ψ → Fin r → Fin r → ℂ) := fun z τ =>
    ((((σ z)⁻¹ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hAc : ContinuousAt A 0 := by
    refine continuousAt_pi.2 fun τ => ?_
    have : ContinuousAt (fun z => (σ z)⁻¹) 0 := ContinuousAt.comp (f := σ) continuous_inv.continuousAt hσc
    exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).continuousAt.comp this
  have hA0 : A 0 = One := by
    funext τ
    simp only [A, One, hσ0, inv_one]
    rfl
  obtain ⟨κ, hκ, hκA⟩ := Metric.continuousAt_iff.1 hAc (ε := δ) hδ
  rw [hA0] at hκA
  refine ⟨δ, hδ, κ, hκ, fun z hz g hg τ a b => ?_⟩
  let B : X.Ψ → Fin r → Fin r → ℂ := fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hzA : dist (A z) One < δ := hκA (by simpa [dist_zero_right] using hz)
  have hgB : dist B One < δ := by
    refine (dist_pi_lt_iff hδ).2 fun τ => (dist_pi_lt_iff hδ).2 fun a => (dist_pi_lt_iff hδ).2 fun b => ?_
    rw [dist_eq_norm]
    exact hg τ a b
  have hPQ : dist (A z, B) (One, One) < δ := by
    rw [Prod.dist_eq]; exact max_lt hzA hgB
  have hout := hδF hPQ
  have hent : dist (F (A z, B) τ a b) (One τ a b) < η :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ b).trans ((dist_le_pi_dist _ _ a).trans (dist_le_pi_dist _ _ τ))) hout
  rw [dist_eq_norm] at hent
  convert hent using 3
  all_goals rfl

end GlobalTheory.SUVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvSectionMulEntriesNearOneStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_inv_section_mul_entries_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm), IsOrth X x → σ 0 = 1 → ContinuousAt σ 0 → ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ z : V (nd X), ‖z‖ < κ → ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∀ τ a b, ‖((mat x τ)⁻¹ * (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < η := by
  first | exact @GlobalTheory.SUVol.conj_inv_section_mul_entries_near_one | exact GlobalTheory.SUVol.conj_inv_section_mul_entries_near_one | (intros; apply GlobalTheory.SUVol.conj_inv_section_mul_entries_near_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryNearOneEqChartMul
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory

theorem eq_chart_mul_of_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  intro E _ _ _ r X x σ t ρ hx hρ hσ0 hσc hσB ht _ _ hstab δ hδ
  obtain ⟨η, hη, hB⟩ := GlobalTheory.T.diagonalPhaseFrame_small_angles E X.Ψ r δ hδ
  have hσa : ContinuousAt σ 0 := hσc.continuousAt (Metric.ball_mem_nhds 0 hρ)
  obtain ⟨ε1, hε1, κ, hκ, hC⟩ := GlobalTheory.T.exists_conj_inv_section_mul_entries_near_one E r X x σ hx hσ0 hσa η hη
  obtain ⟨ε2, hε2, hA⟩ := GlobalTheory.T.leftMul_near_one_lu_split_small_chart E r X x hx (min (min δ ρ) κ) (lt_min (lt_min hδ hρ) hκ)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun g hg => ?_⟩
  have hg1 : g ∈ grpBall (realSU X.Ψ X.Gm) ε1 := fun τ a b => lt_of_lt_of_le (hg τ a b) (min_le_left _ _)
  obtain ⟨z, hz, b, hb, hgx⟩ := hA (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
    (fun τ a c => lt_of_lt_of_le (hg τ a c) (min_le_right _ _))
  have hz1 : ‖z‖ < δ := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : z ∈ Metric.ball (0 : V (nd X)) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
  have hz3 : ‖z‖ < κ := lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨b', hb', hσx⟩ := hσB z hz2
  have hxu : ∀ τ, IsUnit (mat x τ) := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ))

  have hstep : ∃ b'' ∈ Bor X.Ψ r, X.lmulC (fun τ => (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b'' := by
    refine ⟨fun τ => ((mat b' τ)⁻¹ * mat b τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_, ?_⟩
    · have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      refine ⟨?_, fun a c hca => ?_⟩
      · show ((mat b' τ)⁻¹ * mat b τ).det ≠ 0
        rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
        exact mul_ne_zero (inv_ne_zero (hb' τ).1) (hb τ).1
      · show ((mat b' τ)⁻¹ * mat b τ) a c = 0
        letI := Matrix.invertibleOfIsUnitDet _ hb'u
        have h1 : (mat b' τ)⁻¹.BlockTriangular id :=
          Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => (hb' τ).2 a c h)
        have h2 : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
        exact (h1.mul h2) hca
    · funext τ
      have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      set S : GL (Fin r) ℂ := ((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hS
      set G : GL (Fin r) ℂ := ((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hG
      have eM : ((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ) = S⁻¹ * G := rfl
      have e1 : (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b' τ := congrFun hσx τ
      have e2 : (G : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b τ := congrFun hgx τ
      have e3 : mat x τ * mat (nmat X z) τ = (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ * (mat b' τ)⁻¹ := by
        rw [e1, Matrix.mul_assoc (mat x τ * mat (nmat X z) τ), Matrix.mul_nonsing_inv _ hb'u, Matrix.mul_one]
      show (((S⁻¹ * G : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) =
        mat x τ * ((mat b' τ)⁻¹ * mat b τ)
      rw [Units.val_mul, Matrix.mul_assoc, e2, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc]
  obtain ⟨θ, hθ⟩ := hstab _ hstep
  have hP : ∀ θ₀, ∀ τ, (mat x τ)⁻¹ * ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat (phaseFrame θ₀) τ := by
    intro θ₀ τ
    have h1 : ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (phaseFrame θ₀) τ := congrFun (ht θ₀) τ
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hxu τ)), Matrix.one_mul]
  have hph : ∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η := by
    intro τ a
    have h := hC z hz3 g hg1 τ a a
    rw [hθ, hP θ τ] at h
    simpa [mat] using h
  obtain ⟨θ', hθ', hPP⟩ := hB θ hph
  have htt : t θ' = t θ := by
    apply Subtype.ext; funext τ; apply Units.ext
    have h1 := congrFun ((ht θ').trans ((congrArg (rmul x) hPP).trans (ht θ).symm)) τ
    exact (hxu τ).mul_left_injective h1
  refine ⟨(z, θ'), ?_, ?_⟩
  · rw [Prod.norm_def]; exact max_lt hz1 hθ'
  · show σ z * t θ' = g
    rw [htt, ← hθ, mul_inv_cancel_left]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryNearOneEqChartMulStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitary_near_one_eq_chart_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  first | exact @GlobalTheory.eq_chart_mul_of_near_one | exact GlobalTheory.eq_chart_mul_of_near_one | (intros; apply GlobalTheory.eq_chart_mul_of_near_one <;> assumption)
end
