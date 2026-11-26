module

public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CayleyChartDomainIsOpen
noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

theorem slm_sq_lintegral_le {f : ℝ → ENNReal} (hf : AEMeasurable f (volume.restrict (Ioc (0:ℝ) 1))) :
    (∫⁻ s in Ioc (0:ℝ) 1, f s) ^ (2:ℝ) ≤ ∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0:ℝ) 1))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one] at hH
  calc (∫⁻ s in Ioc (0:ℝ) 1, f s) ^ (2:ℝ)
      ≤ ((∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ)) ^ (1 / (2:ℝ))) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow hH (by norm_num)
    _ = ∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num

private lemma eLpNorm_two_rpow_two_eq_lintegral {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (f : Y → ℂ) (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ (2:ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf, ← ENNReal.rpow_mul]
  norm_num

theorem slm_eLpNorm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (r : X → ℂ) (D : ℝ → X → ℂ) (hD : Measurable (Function.uncurry D))
    (hr : ∀ x, r x = ∫ s in (0:ℝ)..1, D s x) (B : ENNReal)
    (hB : ∀ s ∈ Ioc (0:ℝ) 1, eLpNorm (D s) 2 μ ≤ B) : eLpNorm r 2 μ ≤ B := by
  have hmeas : ∀ x, Measurable fun s => D s x := fun x => hD.of_uncurry_right
  have hrmeas : AEStronglyMeasurable r μ := by
    rw [funext hr]
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact (hD.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc (0 : ℝ) 1))).aestronglyMeasurable
  have hpt : ∀ x, ‖r x‖ₑ ≤ ∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ := fun x => by
    rw [hr x, intervalIntegral.integral_of_le zero_le_one]
    exact eNorm_integral_le_lintegral_eNorm _
  have hsq : ∀ s ∈ Ioc (0:ℝ) 1, ∫⁻ x, ‖D s x‖ₑ ^ (2:ℝ) ∂μ ≤ B ^ (2:ℝ) := fun s hs => by
    rw [← eLpNorm_two_rpow_two_eq_lintegral (D s) (hD.of_uncurry_left (x := s)).aestronglyMeasurable]
    exact ENNReal.rpow_le_rpow (hB s hs) (by norm_num)
  have hmain : eLpNorm r 2 μ ^ (2:ℝ) ≤ B ^ (2:ℝ) := by
    rw [eLpNorm_two_rpow_two_eq_lintegral r hrmeas]
    calc ∫⁻ x, ‖r x‖ₑ ^ (2:ℝ) ∂μ
        ≤ ∫⁻ x, (∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ) ^ (2:ℝ) ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num)
      _ ≤ ∫⁻ x, (∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ ^ (2:ℝ)) ∂μ :=
          lintegral_mono fun x => slm_sq_lintegral_le (hmeas x).eNorm.aemeasurable
      _ = ∫⁻ s in Ioc (0:ℝ) 1, ∫⁻ x, ‖D s x‖ₑ ^ (2:ℝ) ∂μ :=
          lintegral_lintegral_swap (((hD.comp measurable_swap).eNorm.pow_const (2:ℝ)).aemeasurable)
      _ ≤ ∫⁻ s in Ioc (0:ℝ) 1, B ^ (2:ℝ) := setLIntegral_mono' measurableSet_Ioc hsq
      _ = B ^ (2:ℝ) := by simp [Real.volume_Ioc]
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 2)).mp hmain

section Mat

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}

theorem slm_cd_iff {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiffOn ℝ k f s ↔ ∀ i j, ContDiffOn ℝ k (fun x => f x i j) s := contDiffOn_pi.trans (forall_congr' fun _ => contDiffOn_pi)

theorem slm_cd_mul {f g : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s)
    (hg : ContDiffOn ℝ k g s) : ContDiffOn ℝ k (fun x => f x * g x) s := by
  rw [slm_cd_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hf i l).mul (hg l j)

theorem slm_cd_conjT {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x)ᴴ) s := by
  rw [slm_cd_iff] at hf ⊢
  intro i j
  have := (Complex.conjCLE.contDiff (n := k)).comp_contDiffOn (hf j i)
  simpa [Function.comp_def, Matrix.conjTranspose_apply] using this

theorem slm_cd_det {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x).det) s := by
  rw [slm_cd_iff] at hf
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => ?_
  exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem slm_cd_adj {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x).adjugate) s := by
  rw [slm_cd_iff]
  intro i j
  simp only [Matrix.adjugate_apply]
  apply slm_cd_det
  rw [slm_cd_iff] at hf ⊢
  intro a b
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne h]
    exact hf a b

theorem slm_cd_inv {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s)
    (hd : ∀ x ∈ s, (f x).det ≠ 0) : ContDiffOn ℝ k (fun x => (f x)⁻¹) s := by
  have hdi : ContDiffOn ℝ k (fun x => ((f x).det)⁻¹) s := (slm_cd_det hf).inv hd
  have hadj := slm_cd_adj hf
  rw [slm_cd_iff] at hadj ⊢
  intro i j
  refine (hdi.mul (hadj i j)).congr fun x _ => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']

end Mat

section Ret

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem slm_JJ (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * X) = X := by
  rw [← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]

theorem slm_inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : Formalism.REAL.inUJ ε a)
    (hb : Formalism.REAL.inUJ ε b) : Formalism.REAL.inUJ ε (a * b) := by
  unfold Formalism.REAL.inUJ at ha hb ⊢
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha, hb]

def slmJi (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε

theorem slm_Ji_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) : slmJi ε g * g = 1 := by
  unfold slmJi
  unfold Formalism.REAL.inUJ at hg
  calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Formalism.REAL.Jm_mul_self]

theorem slm_mul_Ji {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) : g * slmJi ε g = 1 := by
  rw [← Matrix.inv_eq_left_inv (slm_Ji_mul hg)]
  exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse (slm_Ji_mul hg))

theorem slm_Ji_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (slmJi ε g) := by
  have h1 : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1 := by
    have := slm_mul_Ji hg
    unfold slmJi at this
    simpa only [Matrix.mul_assoc] using this
  unfold Formalism.REAL.inUJ slmJi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.REAL.Jm_conjTranspose,
    Matrix.mul_assoc, slm_JJ, h1, Matrix.mul_one]

def slmP (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Y - Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε)

theorem skewAdjointPart_isSkewAdjoint (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.inG ε (slmP ε Y) := by
  have hs : (star (1 / 2 : ℂ)) = 1 / 2 := by simp
  unfold Formalism.REAL.inG slmP
  rw [Matrix.conjTranspose_smul, hs, Matrix.conjTranspose_sub]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.REAL.Jm_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, slm_JJ,
    Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  rw [← smul_add]
  simp

theorem skewAdjointPart_eq_self_of_isSkewAdjoint {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Formalism.REAL.inG ε Y) : slmP ε Y = Y := by
  unfold Formalism.REAL.inG at hY
  have h1 : Yᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
  have h2 : Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε = -Y := by
    calc Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Yᴴ * Formalism.REAL.Jm ε) := Matrix.mul_assoc _ _ _
      _ = -(Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y)) := by rw [h1, Matrix.mul_neg]
      _ = -Y := by rw [slm_JJ]
  unfold slmP
  rw [h2, sub_neg_eq_add, ← two_smul ℂ Y, smul_smul]
  norm_num

theorem slm_Y_inG {h : Matrix (Fin n) (Fin n) ℂ} (hh : Formalism.REAL.inUJ ε h) (hd : (h + 1).det ≠ 0) :
    Formalism.REAL.inG ε ((h - 1) * (h + 1)⁻¹) := by
  have hu : IsUnit (h + 1).det := isUnit_iff_ne_zero.mpr hd
  have hA1 : (h + 1) * (h + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hA2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((h + 1)⁻¹)ᴴ * ((h + 1)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hA1, Matrix.conjTranspose_one, Matrix.one_mul]
  have hm : (h - 1)ᴴ * Formalism.REAL.Jm ε * (h + 1) + (h + 1)ᴴ * Formalism.REAL.Jm ε * (h - 1) = 0 := by
    unfold Formalism.REAL.inUJ at hh
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hh]
    abel
  unfold Formalism.REAL.inG
  generalize h + 1 = A at hA1 hA2 hm ⊢
  generalize h - 1 = B at hm ⊢
  calc (B * A⁻¹)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (B * A⁻¹)
      = (A⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm ε * A + Aᴴ * Formalism.REAL.Jm ε * B) * A⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hA1, hA2, Matrix.mul_one]
    _ = 0 := by rw [hm, Matrix.mul_zero, Matrix.zero_mul]

theorem slm_cay_inUJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (hd : (1 - X).det ≠ 0) :
    Formalism.REAL.inUJ ε ((1 + X) * (1 - X)⁻¹) := by
  have hu : IsUnit (1 - X).det := isUnit_iff_ne_zero.mpr hd
  have hC1 : (1 - X) * (1 - X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hC2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((1 - X)⁻¹)ᴴ * ((1 - X)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hC1, Matrix.conjTranspose_one, Matrix.one_mul]
  have hm : (1 + X)ᴴ * Formalism.REAL.Jm ε * (1 + X) = (1 - X)ᴴ * Formalism.REAL.Jm ε * (1 - X) := by
    unfold Formalism.REAL.inG at hX
    have hX' : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hX']
    abel
  unfold Formalism.REAL.inUJ
  calc ((1 + X) * (1 - X)⁻¹)ᴴ * Formalism.REAL.Jm ε * ((1 + X) * (1 - X)⁻¹)
      = ((1 - X)⁻¹)ᴴ * ((1 + X)ᴴ * Formalism.REAL.Jm ε * (1 + X)) * (1 - X)⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - X)⁻¹)ᴴ * ((1 - X)ᴴ * Formalism.REAL.Jm ε * (1 - X)) * (1 - X)⁻¹ := by rw [hm]
    _ = Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc, hC1, hC2, Matrix.mul_one]

theorem slm_cay_left {h : Matrix (Fin n) (Fin n) ℂ} (hd : (h + 1).det ≠ 0)
    (hd2 : (1 - (h - 1) * (h + 1)⁻¹).det ≠ 0) :
    (1 + (h - 1) * (h + 1)⁻¹) * (1 - (h - 1) * (h + 1)⁻¹)⁻¹ = h := by
  have hu : IsUnit (h + 1).det := isUnit_iff_ne_zero.mpr hd
  have hA1 : (h + 1) * (h + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hc : (h + 1) * (h - 1) = (h - 1) * (h + 1) := by noncomm_ring
  have e : (h + 1) * ((h - 1) * (h + 1)⁻¹) = h - 1 := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, hA1, Matrix.mul_one]
  have key : 1 + (h - 1) * (h + 1)⁻¹ = h * (1 - (h - 1) * (h + 1)⁻¹) := by
    calc 1 + (h - 1) * (h + 1)⁻¹ = h - (h + 1) * ((h - 1) * (h + 1)⁻¹) + (h - 1) * (h + 1)⁻¹ := by
          rw [e]; abel
      _ = h * (1 - (h - 1) * (h + 1)⁻¹) := by noncomm_ring
  have hu2 : IsUnit (1 - (h - 1) * (h + 1)⁻¹).det := isUnit_iff_ne_zero.mpr hd2
  rw [key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.mul_one]

def slmX (ε : Fin n → Bool) (g0 g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  slmP ε ((slmJi ε g0 * g - 1) * (slmJi ε g0 * g + 1)⁻¹)

def slmRet (ε : Fin n → Bool) (g0 g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  g0 * ((1 + slmX ε g0 g) * (1 - slmX ε g0 g)⁻¹)

def cayleyChartDomain (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | (slmJi ε g0 * g + 1).det ≠ 0}

def slmV (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  cayleyChartDomain ε g0 ∩ (fun g => (1 - slmX ε g0 g).det) ⁻¹' {0}ᶜ

theorem slm_X_cd (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmX ε g0) (cayleyChartDomain ε g0) := by
  have h1 : ContDiffOn ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => slmJi ε g0 * g) (cayleyChartDomain ε g0) :=
    slm_cd_mul contDiffOn_const contDiffOn_id
  have hA : ContDiffOn ℝ ∞ (fun g => slmJi ε g0 * g - 1) (cayleyChartDomain ε g0) := h1.sub contDiffOn_const
  have hB : ContDiffOn ℝ ∞ (fun g => slmJi ε g0 * g + 1) (cayleyChartDomain ε g0) := h1.add contDiffOn_const
  have hY := slm_cd_mul hA (slm_cd_inv hB fun g hg => hg)
  have hJYJ := slm_cd_mul (slm_cd_mul (contDiffOn_const (c := Formalism.REAL.Jm ε)) (slm_cd_conjT hY))
    (contDiffOn_const (c := Formalism.REAL.Jm ε))
  exact (hY.sub hJYJ).const_smul (1 / 2 : ℂ)

theorem cayleyChartDomain_isOpen (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : IsOpen (cayleyChartDomain ε g0) := by
  show IsOpen {g : Matrix (Fin n) (Fin n) ℂ | (slmJi ε g0 * g + 1).det ≠ 0}
  exact isOpen_ne_fun ((continuous_const.matrix_mul continuous_id).add continuous_const).matrix_det
    continuous_const

theorem slm_V_open (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : IsOpen (slmV ε g0) :=
  ContinuousOn.isOpen_inter_preimage (f := fun g => (1 - slmX ε g0 g).det)
    ((continuous_id.matrix_det).comp_continuousOn (continuousOn_const.sub (slm_X_cd ε g0).continuousOn))
    (cayleyChartDomain_isOpen ε g0) isOpen_compl_singleton

theorem slm_ret_cd (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmRet ε g0) (slmV ε g0) := by
  have hX : ContDiffOn ℝ ∞ (slmX ε g0) (slmV ε g0) := (slm_X_cd ε g0).mono fun _ hg => hg.1
  have hM : ContDiffOn ℝ ∞ (fun g => 1 - slmX ε g0 g) (slmV ε g0) := contDiffOn_const.sub hX
  have hP : ContDiffOn ℝ ∞ (fun g => 1 + slmX ε g0 g) (slmV ε g0) := contDiffOn_const.add hX
  have hI := slm_cd_inv hM fun g hg => hg.2
  exact slm_cd_mul contDiffOn_const (slm_cd_mul hP hI)

theorem slm_ret_inUJ {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∀ g ∈ slmV ε g0, Formalism.REAL.inUJ ε (slmRet ε g0 g) := fun g hg => slm_inUJ_mul hg0 (slm_cay_inUJ (skewAdjointPart_isSkewAdjoint ε _) hg.2)

theorem slm_ret_self {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∀ g ∈ slmV ε g0, Formalism.REAL.inUJ ε g → slmRet ε g0 g = g := by
  intro g hg hgU
  have hh : Formalism.REAL.inUJ ε (slmJi ε g0 * g) := slm_inUJ_mul (slm_Ji_inUJ hg0) hgU
  have hd : (slmJi ε g0 * g + 1).det ≠ 0 := hg.1
  have hXY : slmX ε g0 g = (slmJi ε g0 * g - 1) * (slmJi ε g0 * g + 1)⁻¹ :=
    skewAdjointPart_eq_self_of_isSkewAdjoint (slm_Y_inG hh hd)
  have hd2 : (1 - slmX ε g0 g).det ≠ 0 := hg.2
  rw [hXY] at hd2
  show g0 * ((1 + slmX ε g0 g) * (1 - slmX ε g0 g)⁻¹) = g
  rw [hXY, slm_cay_left hd hd2, ← Matrix.mul_assoc, slm_mul_Ji hg0, Matrix.one_mul]

theorem slm_mem_V {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) : g0 ∈ slmV ε g0 := by
  have h1 : slmJi ε g0 * g0 = 1 := slm_Ji_mul hg0
  have hW : g0 ∈ cayleyChartDomain ε g0 := by
    show (slmJi ε g0 * g0 + 1).det ≠ 0
    rw [h1, ← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), Matrix.det_smul, Matrix.det_one]
    simp
  have hX0 : slmX ε g0 g0 = 0 := by
    unfold slmX slmP
    rw [h1]
    simp
  show g0 ∈ cayleyChartDomain ε g0 ∧ (1 - slmX ε g0 g0).det ≠ 0
  refine ⟨hW, ?_⟩
  rw [hX0]
  simp

theorem slm_exists_ret (ε : Fin n → Bool) {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∃ (V : Set (Matrix (Fin n) (Fin n) ℂ)) (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ),
      IsOpen V ∧ g0 ∈ V ∧ ContDiffOn ℝ ∞ γ V ∧ (∀ g ∈ V, Formalism.REAL.inUJ ε (γ g)) ∧
        ∀ g ∈ V, Formalism.REAL.inUJ ε g → γ g = g :=
  ⟨slmV ε g0, slmRet ε g0, slm_V_open ε g0, slm_mem_V hg0, slm_ret_cd ε g0, slm_ret_inUJ hg0, slm_ret_self hg0⟩

end Ret

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

section Curve

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem slm_le_inf (N : ℕ) : (N : WithTop ℕ∞) + 1 ≤ ∞ := by
  exact_mod_cast (le_top : ((N + 1 : ℕ) : ℕ∞) ≤ ⊤)

theorem slm_le_inf' (N : ℕ) : (N : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : ((N : ℕ) : ℕ∞) ≤ ⊤)

theorem slm_hd_iff {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} :
    HasDerivAt f f' s ↔ ∀ i j, HasDerivAt (fun t => f t i j) (f' i j) s := by
  exact hasDerivAt_pi.trans (forall_congr' fun i => hasDerivAt_pi)

theorem slm_hd_mul {f g : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' g' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => f t * g t) (f' * g s + f s * g') s := by
  refine slm_hd_iff.mpr fun i j => ?_
  have hf' := slm_hd_iff.mp hf
  have hg' := slm_hd_iff.mp hg
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hf' i k).mul (hg' k j)

theorem slm_hd_conjT {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) : HasDerivAt (fun t => (f t)ᴴ) f'ᴴ s := by
  refine slm_hd_iff.mpr fun i j => ?_
  have h1 := (slm_hd_iff.mp hf j i).star
  simpa [Matrix.conjTranspose_apply] using h1

theorem slm_Ji_mul_mul (a b : Matrix (Fin n) (Fin n) ℂ) : slmJi ε (a * b) = slmJi ε b * slmJi ε a := by
  unfold slmJi
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul]

theorem slm_inG_of_curve {c : ℝ → Matrix (Fin n) (Fin n) ℂ} {c' : Matrix (Fin n) (Fin n) ℂ} {s0 : ℝ}
    (hc : HasDerivAt c c' s0) (hcU : ∀ᶠ s in 𝓝 s0, Formalism.REAL.inUJ ε (c s)) :
    Formalism.REAL.inG ε (slmJi ε (c s0) * c') := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hJt := Formalism.REAL.Jm_conjTranspose ε
  have e1 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← mul_assoc, hJ, one_mul]
  have h1 : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε) (c'ᴴ * Formalism.REAL.Jm ε) s0 := by
    have := slm_hd_mul (slm_hd_conjT hc) (hasDerivAt_const s0 (Formalism.REAL.Jm ε))
    simpa using this
  have hD : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε * c s)
      (c'ᴴ * Formalism.REAL.Jm ε * c s0 + (c s0)ᴴ * Formalism.REAL.Jm ε * c') s0 := slm_hd_mul h1 hc
  have hD0 : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε * c s) 0 s0 := by
    apply (hasDerivAt_const s0 (Formalism.REAL.Jm ε)).congr_of_eventuallyEq
    filter_upwards [hcU] with s hs
    exact hs
  have hsum := hD.unique hD0
  show (slmJi ε (c s0) * c')ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (slmJi ε (c s0) * c') = 0
  unfold slmJi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJt, mul_assoc, hJ,
    Matrix.mul_one, e1]
  simpa [mul_assoc] using hsum

end Curve

section GenG

variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

def slmG (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) : X →L[ℝ] E :=
  ∑ i, ((C i).comp fd).smulRight (w i)

theorem slmG_apply (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) (W : X) :
    slmG C fd w W = ∑ i, (C i (fd W)) • w i := by
  simp [slmG, ContinuousLinearMap.sum_apply]

theorem slmG_cd {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {N : ℕ} {w : ι → X → E} (hw : ∀ i, ContDiffOn ℝ N (w i) V) :
    ContDiffOn ℝ N (fun q => slmG C (fderiv ℝ γ q) (fun i => w i q)) V := by
  have hfd : ContDiffOn ℝ N (fun q => fderiv ℝ γ q) V := hγ.fderiv_of_isOpen hV (slm_le_inf N)
  unfold slmG
  exact ContDiffOn.sum fun i _ => (contDiffOn_const.clm_comp hfd).smulRight (hw i)

theorem contDiffOn_zero_of_continuousOn {V : Set X} {f : X → E} (h : ContinuousOn f V) : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) f V := by
  exact contDiffOn_zero.mpr h

theorem slm_gen_hD {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {A : Type*} (c : ι → X → ℂ) (hc : ∀ i, ContDiffOn ℝ ∞ (c i) V)
    (P : A → Prop) (Op : ι → A → A) (hP : ∀ F, P F → ∀ i, P (Op i F)) (Φ : A → X → E)
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : X, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG C (fderiv ℝ γ (q + s • W))
          (fun i => c i (q + s • W) • Φ (Op i F) (q + s • W)) W -
        slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) :
    ∀ F, P F → ∀ q ∈ V,
      HasFDerivAt (Φ F) (slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q)) q := by
  intro F hF q hq
  set L : X → (X →L[ℝ] E) := fun x => slmG C (fderiv ℝ γ x) (fun i => c i x • Φ (Op i F) x)
    with hLdef
  have hw0 : ∀ i, ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun x => c i x • Φ (Op i F) x) V :=
    fun i => contDiffOn_zero_of_continuousOn (((hc i).continuousOn).smul (hcont (Op i F) (hP F hF i)))
  have hLc : ContinuousAt L q :=
    ((slmG_cd hV hγ C hw0).continuousOn).continuousAt (hV.mem_nhds hq)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hρL⟩ := Metric.continuousAt_iff.mp hLc ε hε
  obtain ⟨δ, hδ, hδh⟩ := hint F hF q hq
  have hball : ∀ᶠ W in 𝓝 (0 : X), ‖W‖ < min δ ρ := by
    have := Metric.ball_mem_nhds (0 : X) (lt_min hδ hρ)
    filter_upwards [this] with W hW
    simpa using hW
  filter_upwards [hball] with W hW
  apply hδh W (lt_of_lt_of_le hW (min_le_left _ _)) (ε * ‖W‖)
  intro s hs
  have hd : dist (q + s • W) q < ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖W‖ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ‖W‖ := one_mul _
      _ < ρ := lt_of_lt_of_le hW (min_le_right _ _)
  have h1 := hρL hd
  rw [dist_eq_norm] at h1
  calc ‖L (q + s • W) W - L q W‖ = ‖(L (q + s • W) - L q) W‖ := by
        rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖L (q + s • W) - L q‖ * ‖W‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖W‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)

theorem slm_gen {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {A : Type*} (c : ι → X → ℂ) (hc : ∀ i, ContDiffOn ℝ ∞ (c i) V)
    (P : A → Prop) (Op : ι → A → A) (hP : ∀ F, P F → ∀ i, P (Op i F)) (Φ : A → X → E)
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : X, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG C (fderiv ℝ γ (q + s • W))
          (fun i => c i (q + s • W) • Φ (Op i F) (q + s • W)) W -
        slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) :
    ∀ F, P F → ContDiffOn ℝ ∞ (Φ F) V := by
  intro F hF
  have key : ∀ N : ℕ, ∀ F, P F → ContDiffOn ℝ N (Φ F) V := by
    intro N
    induction N with
    | zero => intro F hF; exact contDiffOn_zero_of_continuousOn (hcont F hF)
    | succ N ih =>
      intro F hF
      have hD := slm_gen_hD hV hγ C c hc P Op hP Φ hcont hint F hF
      have hw : ∀ i, ContDiffOn ℝ N (fun q => c i q • Φ (Op i F) q) V := fun i =>
        ((hc i).of_le (slm_le_inf' N)).smul (ih (Op i F) (hP F hF i))
      have hfd : ContDiffOn ℝ N (fderiv ℝ (Φ F)) V :=
        (slmG_cd hV hγ C hw).congr fun q hq => (hD q hq).fderiv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hV]
      exact ⟨fun q hq => (hD q hq).differentiableAt.differentiableWithinAt, by simp, hfd⟩
  exact contDiffOn_infty.mpr fun N => key N F hF

end GenG

section GenM

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def slmEnt (k b : Fin n) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) k)

theorem slmEnt_apply (k b : Fin n) (W : Fin n → Fin n → ℂ) : slmEnt k b W = W k b := rfl

def slmC (i : Fin n × Fin n × Fin n × Bool) :=
  if i.2.2.2 then Complex.reCLM.comp (slmEnt i.2.2.1 i.2.1) else Complex.imCLM.comp (slmEnt i.2.2.1 i.2.1)

def slmc (m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (i : Fin n × Fin n × Fin n × Bool)
    (q : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if i.2.2.2 then m q i.1 i.2.2.1 else Complex.I * m q i.1 i.2.2.1

theorem re_mul_add_im_mul_I (z c : ℂ) : (z.re : ℂ) * c + (z.im : ℂ) * (Complex.I * c) = c * z := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring

theorem slmc_cd {V : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hm : ContDiffOn ℝ ∞ m V) (i : Fin n × Fin n × Fin n × Bool) : ContDiffOn ℝ ∞ (slmc m i) V := by
  have h1 : ContDiffOn ℝ ∞ (fun q => m q i.1 i.2.2.1) V :=
    (slmEnt i.1 i.2.2.1).contDiff.comp_contDiffOn hm
  unfold slmc
  split_ifs
  · exact h1
  · exact contDiffOn_const.mul h1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem slmG_mat_apply (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (q : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → Fin n → E) (W : Matrix (Fin n) (Fin n) ℂ) :
    slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) (fun i => slmc m i q • v i.1 i.2.1) W =
      ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • v a b := by
  refine (slmG_apply (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) _ W).trans ?_
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slmC, slmc, ↓reduceIte, Bool.false_eq_true,
    ContinuousLinearMap.coe_comp', Function.comp_apply, slmEnt_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Matrix.mul_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [← re_mul_add_im_mul_I (fderiv ℝ γ q W k b) (m q a k)]
  simp only [add_smul, mul_smul, Complex.coe_smul]
  rfl

theorem slm_mat_hint {V : Set (Matrix (Fin n) (Fin n) ℂ)}
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) :
    ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ (q + s • W))
          (fun i => slmc m i (q + s • W) • Φ (Op i.1 i.2.1 F) (q + s • W)) W -
        slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q)
        (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q) W‖ ≤ B := by
  intro F hF q hq
  obtain ⟨δ, hδ, h⟩ := hint F hF q hq
  refine ⟨δ, hδ, fun W hW B hB => ?_⟩
  rw [slmG_mat_apply γ m q (fun a b => Φ (Op a b F) q) W]
  refine h W hW B fun s hs => ?_
  have h1 := hB s hs
  rwa [slmG_mat_apply γ m (q + s • W) (fun a b => Φ (Op a b F) (q + s • W)) W,
    slmG_mat_apply γ m q (fun a b => Φ (Op a b F) q) W] at h1

theorem slm_mat_hD {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V)
    (hm : ContDiffOn ℝ ∞ m V) (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hP : ∀ F, P F → ∀ a b, P (Op a b F))
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B)
    (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (hF : P F) (q : Matrix (Fin n) (Fin n) ℂ) (hq : q ∈ V) :
    HasFDerivAt (Φ F) (slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q)
      (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q)) q :=
  slm_gen_hD hV hγ slmC (fun i => slmc m i) (fun i => slmc_cd hm i) P (fun i => Op i.1 i.2.1)
    (fun F hF i => hP F hF i.1 i.2.1) Φ hcont (slm_mat_hint Φ P Op hint) F hF q hq

theorem slm_mat {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V)
    (hm : ContDiffOn ℝ ∞ m V) (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hP : ∀ F, P F → ∀ a b, P (Op a b F))
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) :
    ∀ F, P F → ContDiffOn ℝ ∞ (Φ F) V :=
  slm_gen hV hγ slmC (fun i => slmc m i) (fun i => slmc_cd hm i) P (fun i => Op i.1 i.2.1)
    (fun F hF i => hP F hF i.1 i.2.1) Φ hcont (slm_mat_hint Φ P Op hint)

end GenM

section Lp

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem slm_coeFn_sum {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 μ) :
    (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  · intro i t hi ih
    rw [Finset.sum_insert hi]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with x hx
    simp only [Pi.add_apply, hx, Finset.sum_insert hi]

end Lp

end ReciprocityTheory.ChartRestriction.DS
