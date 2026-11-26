module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF
variable {n : ℕ}

lemma map_star_mul (a b : Matrix (Fin n) (Fin n) ℂ) : (a * b).map star = a.map star * b.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

lemma map_star_star (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star).map star = a := by
  ext i j
  simp

lemma map_star_one : (1 : Matrix (Fin n) (Fin n) ℂ).map star = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma map_star_ct (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star)ᴴ = aᴴ.map star := by
  ext i j
  simp

lemma Jm_star (ε : Fin n → Bool) : (Jm ε).map star = Jm ε := by
  ext i j
  simp only [Matrix.map_apply, Formalism.REAL.Jm, Matrix.diagonal_apply]
  split_ifs <;> simp

lemma UJ_star {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) : g.map star ∈ UJset ε := by
  have h' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := h
  show (g.map star)ᴴ * Formalism.REAL.Jm ε * g.map star = Formalism.REAL.Jm ε
  have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) h'
  simp only [map_star_mul, Jm_star] at e
  rw [map_star_ct]
  exact e

lemma K_star {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g.map star ∈ Kset ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  obtain ⟨hu, hc⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hu
    simp only [map_star_mul, map_star_one, Matrix.star_eq_conjTranspose] at e
    rw [Matrix.star_eq_conjTranspose, map_star_ct]
    exact e
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hc
    simpa only [map_star_mul, Jm_star] using e

lemma P_star {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) : inP ε (X.map star) := by
  have h' : (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := h
  obtain ⟨hg, hp⟩ := h'
  show ((X.map star)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X.map star = 0) ∧
    X.map star * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X.map star)
  refine ⟨?_, ?_⟩
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hg
    have ha : ∀ M N : Matrix (Fin n) (Fin n) ℂ, (M + N).map star = M.map star + N.map star :=
      fun M N => by
        ext i j
        simp
    have hz : (0 : Matrix (Fin n) (Fin n) ℂ).map star = 0 := by
      ext i j
      simp
    simp only [ha, hz, map_star_mul, Jm_star] at e
    rw [map_star_ct]
    exact e
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hp
    have hn : ∀ M : Matrix (Fin n) (Fin n) ℂ, (-M).map star = -(M.map star) := fun M => by
      ext i j
      simp
    simpa only [hn, map_star_mul, Jm_star] using e

lemma exp_star (X : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp X).map star = NormedSpace.exp (X.map star) := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map star = Mᴴᵀ := fun M => by
    ext i j
    simp
  rw [e (NormedSpace.exp X), e X, Matrix.exp_transpose, Matrix.exp_conjTranspose]

lemma Phi_star (lam : Fin n → ℝ) (z : Matrix (Fin n) (Fin n) ℂ) : Phi lam (z.map star) = star (Phi lam z) := by
  have e : ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ), (M.map star).det = star M.det := by
    intro N M
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose Mᴴ]
    congr 1
  simp only [GlobalTheory.Dec.Phi, star_prod, star_zpow₀]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1
  simp only [Formalism.MainNotions.S.leadMinor]
  rw [← e]
  rfl

lemma K_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g ∈ UJset ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  obtain ⟨hu, hc⟩ := h'
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.one_mul]

lemma one_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε := by
  refine ⟨one_mem _, ?_⟩
  rw [Matrix.one_mul, Matrix.mul_one]

lemma K_inv {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g⁻¹ = gᴴ := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp h'.1

lemma K_KC {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g ∈ KC ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  exact ⟨⟨⟨g, star g, Matrix.mem_unitaryGroup_iff.mp h'.1, Matrix.mem_unitaryGroup_iff'.mp h'.1⟩, rfl⟩, h'.2⟩

lemma exp_posDef {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) : (NormedSpace.exp X).PosDef := by
  have h' : (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := h
  obtain ⟨hg, hp⟩ := h'
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have h1 : Xᴴ * Formalism.REAL.Jm ε = X * Formalism.REAL.Jm ε := by
    rw [hp]
    exact eq_neg_of_add_eq_zero_left hg
  have hH : Xᴴ = X := by
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = X * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [h1]
      _ = X := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hYH : ((2⁻¹ : ℝ) • X)ᴴ = (2⁻¹ : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, hH, star_trivial]
  have hYY : (2⁻¹ : ℝ) • X + (2⁻¹ : ℝ) • X = X := by
    rw [← add_smul]
    norm_num
  rw [← hYY, Formalism.REAL.exp_add_self]
  have hE := Formalism.REAL.exp_conjTranspose_of_hermitian hYH
  have hsq : NormedSpace.exp ((2⁻¹ : ℝ) • X) * NormedSpace.exp ((2⁻¹ : ℝ) • X) =
      (NormedSpace.exp ((2⁻¹ : ℝ) • X))ᴴ * NormedSpace.exp ((2⁻¹ : ℝ) • X) := by
    rw [hE]
  rw [hsq]
  apply Matrix.PosDef.conjTranspose_mul_self
  intro u v huv
  have e := congrArg (NormedSpace.exp (-((2⁻¹ : ℝ) • X))).mulVec huv
  simpa only [Matrix.mulVec_mulVec, Formalism.REAL.matrix_exp_neg_mul_exp, Matrix.one_mulVec] using e

lemma URep_K {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (UJset ε) σ) : IsURepOn (Kset ε) σ := by
  obtain ⟨⟨h1, hm⟩, hi, hc⟩ := h
  exact ⟨⟨h1, fun a ha b hb => hm a (K_UJ ha) b (K_UJ hb)⟩, fun g hg v => hi g (K_UJ hg) v,
    fun v => (hc v).mono (fun g hg => K_UJ hg)⟩


end GlobalTheory.Dec.FormF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverage
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Schur

theorem avg_sq {X V ι : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (f : X → V) (hf : AEStronglyMeasurable f μ) (c : ℝ) (hn : ∀ᵐ x ∂μ, ‖f x‖ = c)
    (T : ι → V →L[ℂ] V) (hT : ∀ i a b, ⟪T i a, T i b⟫_ℂ = ⟪a, b⟫_ℂ)
    (m : ι → X → X) (hm : ∀ i, MeasurePreserving (m i) μ μ)
    (hfm : ∀ i, ∀ᵐ x ∂μ, f (m i x) = T i (f x))
    (hirr : ∀ S : Submodule ℂ V, (∀ i, ∀ v ∈ S, T i v ∈ S) → S = ⊥ ∨ S = ⊤) (w : V) :
    Integrable (fun x => ‖⟪w, f x⟫_ℂ‖ ^ 2) μ ∧
      ∫ x, ‖⟪w, f x⟫_ℂ‖ ^ 2 ∂μ = ‖w‖ ^ 2 * c ^ 2 / Module.finrank ℂ V := by
  have hci : ∀ s : V, Integrable (fun x => ‖⟪s, f x⟫_ℂ‖ ^ 2) μ := by
    intro s
    refine Integrable.of_bound (((aestronglyMeasurable_const (b := s)).inner hf).norm.pow 2)
      ((‖s‖ * c) ^ 2) ?_
    filter_upwards [hn] with x hx
    rw [norm_pow, norm_norm, ← hx]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  refine ⟨hci w, ?_⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [Subsingleton.elim w 0]; simp
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let Fy : V → X → V := fun y x => ⟪f x, y⟫_ℂ • f x
  have hFm : ∀ y, AEStronglyMeasurable (Fy y) μ := fun y =>
    (hf.inner (aestronglyMeasurable_const (b := y))).smul hf
  have hFi : ∀ y, Integrable (Fy y) μ := by
    intro y
    refine Integrable.of_bound (hFm y) (c * ‖y‖ * c) ?_
    filter_upwards [hn] with x hx
    simp only [Fy]
    rw [norm_smul, ← hx]
    exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
  let R : V →ₗ[ℂ] V :=
    { toFun := fun y => ∫ h, Fy y h ∂μ
      map_add' := by
        intro y z
        rw [← integral_add (hFi y) (hFi z)]
        congr 1; funext h; simp only [Fy, inner_add_right, add_smul]
      map_smul' := by
        intro c y
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext h; simp only [Fy, inner_smul_right, mul_smul] }
  have hRdef : ∀ y, R y = ∫ h, Fy y h ∂μ := fun _ => rfl
  have hcomm : ∀ i y, R (T i y) = T i (R y) := by
    intro i y
    rw [hRdef, hRdef, ← (T i).integral_comp_comm (hFi y)]
    have h1 : ∫ h, Fy (T i y) h ∂μ = ∫ h, Fy (T i y) (m i h) ∂μ := by
      have := integral_map (μ := μ) (φ := m i) (hm i).measurable.aemeasurable (f := Fy (T i y))
        (by rw [(hm i).map_eq]; exact hFm _)
      rwa [(hm i).map_eq] at this
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hfm i] with x hx
    simp only [Fy, hx, map_smul, hT]
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue R
  have hE : Module.End.eigenspace R lam = ⊤ :=
    (hirr _ (fun h x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hcomm, hx, map_smul])).resolve_left hlam
  have hR : ∀ y, R y = lam • y := fun y =>
    Module.End.mem_eigenspace_iff.mp (hE ▸ Submodule.mem_top)
  have h4 : ∀ s : V, lam * ((‖s‖ ^ 2 : ℝ) : ℂ) = ((∫ h, ‖⟪s, f h⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro s
    have a : ⟪s, R s⟫_ℂ = lam * ((‖s‖ ^ 2 : ℝ) : ℂ) := by
      rw [hR, inner_smul_right, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have b : ⟪s, R s⟫_ℂ = ∫ h, ⟪s, Fy s h⟫_ℂ ∂μ := (integral_inner (hFi s) s).symm
    have c : ∀ h, ⟪s, Fy s h⟫_ℂ = ((‖⟪s, f h⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro h
      simp only [Fy, inner_smul_right]
      rw [← inner_conj_symm (f h) s, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← a, b]
    simp_rw [c]
    exact integral_ofReal
  have h5 : lam * (Module.finrank ℂ V : ℂ) = ((c ^ 2 : ℝ) : ℂ) := by
    let b := stdOrthonormalBasis ℂ V
    have e1 : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = c ^ 2 := by
      have : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = ∫ _h, c ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hn] with x hx
        rw [b.sum_sq_norm_inner_right, hx]
      rw [this]; simp
    rw [← e1, integral_finsetSum _ fun i _ => hci (b i)]
    push_cast
    simp_rw [← h4]
    have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
    simp [hb, mul_comm]
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  apply Complex.ofReal_injective
  rw [← h4, Complex.ofReal_div, Complex.ofReal_mul, ← h5]
  push_cast
  field_simp

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem type_irred {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} (hT : 0 < Tz k r z)
    {u : Fin k → ℝ} (hπ : IsHCTypeW k r z u π) :
    Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨h1, h2, h3, h4⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'
  obtain ⟨g, hg, hρ⟩ := hπ
  refine ⟨hρ.1, ⟨⟨h1, h2⟩, h3, h4⟩, fun S _ hS => ?_⟩
  refine hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv
  have hg' : PI.UpqRep.IsFrameW k r z g := hg
  have hx' : x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k) :=
    PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1)
  exact GlobalTheory.BesselFrame.conj_mem_UW hg' hx'

theorem avg_UW [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    {μW : Measure (Mt k r)} (hU : IsURepOn (UWset k r z) π) (hI : IsIrredOn (UWset k r z) π)
    (hH : IsHaarOn (UWset k r z) μW) (h1 : μW Set.univ = 1) (w ξ : Wp) :
    ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW =
      ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) := by
  haveI : IsProbabilityMeasure μW := ⟨h1⟩
  have hW := isClosedSub_UWset (k := k) (r := r) z
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.mpr hH.2.2.1
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
  have hf : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x) ξ) μW := by
    have hc : ContinuousOn (fun x : Mt k r => π (Matrix.of x) ξ) {x : Mt k r | Matrix.of x ∈ UWset k r z} :=
      hU.2.2 ξ
    have := hc.aestronglyMeasurable (μ := μW) (hW.2.1.preimage hof).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r z}) hae] at this
  have hlm : ∀ s : Mat k r, Continuous (lmulM s : Mt k r → Mt k r) := fun s =>
    (continuous_const (y := s)).matrix_mul hof
  obtain ⟨hi, hv⟩ := avg_sq μW (fun x : Mt k r => π (Matrix.of x) ξ) hf ‖ξ‖
    (hae.mono fun x hx => hU.2.1 _ hx ξ) (fun s : UWset k r z => π s)
    (fun s => (LinearMap.norm_map_iff_inner_map_map ((π s : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hU.2.1 s s.2))
    (fun s => lmulM (s : Mat k r))
    (fun s => ⟨(hlm s).measurable, hH.2.2.2 s s.2⟩)
    (fun s => hae.mono fun x hx => DFunLike.congr_fun (hU.1.2 s s.2 _ hx) ξ)
    (fun S hS => hI S S.closed_of_finiteDimensional fun g hg => hS ⟨g, hg⟩) w
  rw [← hv, ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

theorem type_irred_and_avg : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → (∀ u, IsHCTypeW k r z u π → Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π) ∧ ∀ μW : Measure (Mt k r), IsURepOn (UWset k r z) π → IsIrredOn (UWset k r z) π → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∀ w ξ : Wp, ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW = ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) :=
  fun _ _ _ _ _ _ _ _ _ hT => ⟨fun _ hπ => type_irred hT hπ, fun _ hU hI hH h1 w ξ => avg_UW hU hI hH h1 w ξ⟩

end GlobalTheory.Amp.Schur
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverageStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hcTypeW_irreducible_and_schur_average : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → (∀ u, IsHCTypeW k r z u π → Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π) ∧ ∀ μW : Measure (Mt k r), IsURepOn (UWset k r z) π → IsIrredOn (UWset k r z) π → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∀ w ξ : Wp, ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW = ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) := by
  first | exact @GlobalTheory.Amp.Schur.type_irred_and_avg | exact GlobalTheory.Amp.Schur.type_irred_and_avg | (intros; apply GlobalTheory.Amp.Schur.type_irred_and_avg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeRightInv

open Topology

theorem map_mul_right_of_conj_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : ν B ≠ 0) (ht : ν B ≠ ⊤) (l : G) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    ν.map (fun g => g * l) = ν := by
  have hU : (interior B).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hB⟩
  have hmeas : Measurable (fun g : G => g * l) := measurable_mul_const l
  haveI : IsFiniteMeasureOnCompacts ν :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant' hU ht hK⟩

  have hVo : IsOpen ((fun g : G => g * l⁻¹) ⁻¹' interior B) :=
    isOpen_interior.preimage (continuous_mul_const l⁻¹)
  have hV : ν.map (fun g => g * l) ((fun g : G => g * l⁻¹) ⁻¹' interior B) = ν (interior B) := by
    rw [Measure.map_apply hmeas hVo.measurableSet]
    congr 1
    ext g
    simp [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts (ν.map (fun g => g * l)) :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hVo
      ⟨l, by simpa using mem_interior_iff_mem_nhds.2 hB⟩
      (by rw [hV]; exact ((measure_mono interior_subset).trans_lt ht.lt_top).ne) hK⟩

  obtain ⟨c₁, e₁⟩ : ∃ c : NNReal, ν = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν Measure.haar⟩
  obtain ⟨c₂, e₂⟩ : ∃ c : NNReal, ν.map (fun g => g * l) = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ Measure.haar⟩

  have hBB : ν.map (fun g => g * l) B = ν B := by
    rw [Measure.map_apply hmeas hBm,
      show (fun g => g * l) ⁻¹' B = (fun g => l * g) ⁻¹' B from Set.ext hl]
    exact measure_preimage_mul ν l B
  have hpos : (Measure.haar : Measure G) B ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hB).ne'
  have hc₁ : (c₁ : ENNReal) ≠ 0 := by
    rintro h
    apply h0
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, zero_mul]
  have hfin : (Measure.haar : Measure G) B ≠ ⊤ := by
    intro h
    apply ht
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, ENNReal.mul_top hc₁]
  rw [e₂, e₁, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul, ENNReal.mul_left_inj hpos hfin] at hBB
  rw [e₂, e₁, ENNReal.coe_injective hBB]

theorem map_mul_right_of_conj_nhds_subgroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) (hM : IsClosed (M : Set G)) (μ : Measure G) (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : μ B ≠ 0) (ht : μ B ≠ ⊤) (l : G) (hlM : l ∈ M) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    μ.map (fun g => g * l) = μ := by
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (M : Set G))
  haveI : BorelSpace M := inferInstanceAs (BorelSpace (M : Set G))
  have emb : MeasurableEmbedding (Subtype.val : M → G) :=
    MeasurableEmbedding.subtype_coe hM.measurableSet

  set ν : Measure M := μ.comap Subtype.val with hν
  have hμν : ν.map Subtype.val = μ := by
    rw [hν, emb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)
  haveI : ν.IsMulLeftInvariant := ⟨fun s => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul s) hA, hν, emb.comap_apply, emb.comap_apply]
    have himg : Subtype.val '' ((fun x => s * x) ⁻¹' A) =
        (fun x : G => (s : G) * x) ⁻¹' (Subtype.val '' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨s * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hx : x ∈ M := by
          have : x = (s : G)⁻¹ * y := by rw [hyx, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this]
          exact M.mul_mem (M.inv_mem s.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        show s * (⟨x, hx⟩ : M) ∈ A
        rw [show s * (⟨x, hx⟩ : M) = y from Subtype.ext hyx.symm]
        exact hy
    rw [himg, ← Measure.map_apply (measurable_const_mul (s : G)) (emb.measurableSet_image' hA),
      hinv s s.2]⟩
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by
    conv_rhs => rw [← hμν]
    rw [Measure.map_apply measurable_subtype_coe hBm]
  have key := map_mul_right_of_conj_nhds ν (Subtype.val ⁻¹' B)
    (hBm.preimage measurable_subtype_coe)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hB)
    (by rwa [hνB]) (by rwa [hνB]) ⟨l, hlM⟩ (fun g => hl g)
  rw [← hμν, Measure.map_map (measurable_mul_const l) measurable_subtype_coe,
    show (fun g : G => g * l) ∘ Subtype.val = Subtype.val ∘ (fun g : M => g * ⟨l, hlM⟩) from rfl,
    ← Measure.map_map measurable_subtype_coe (measurable_mul_const _), key]

theorem hs_eq_re_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs X = (trace (X * Xᴴ)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem hs_mul_mul_conjTranspose_of_unitary {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * M * Lᴴ) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace, hs_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  calc trace (L * M * Lᴴ * (L * (Mᴴ * Lᴴ))) = trace (L * (M * Mᴴ) * Lᴴ) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]
    _ = trace (Lᴴ * (L * (M * Mᴴ))) := Matrix.trace_mul_comm _ _
    _ = trace (M * Mᴴ) := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem hs_conj {n : ℕ} (L X : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * X - 1) = Formalism.REAL.hs (X * L - 1) := by
  have hL' : L * Lᴴ = 1 := mul_eq_one_comm.mp hL

  have h : L * X - 1 = L * (X * L - 1) * Lᴴ := by
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hL']
  rw [h, hs_mul_mul_conjTranspose_of_unitary L _ hL]

theorem isGaugeSub_map_mul_right (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) (l : Formalism.REAL.UJ ε) (hlM : l ∈ M) (hlK : l ∈ maxK ε) :
    μ.map (fun g => g * l) = μ := by
  unfold IsGaugeSub at hμ
  obtain ⟨hμc, hinv, hlim⟩ := hμ
  have hlU : (uMat l)ᴴ * uMat l = 1 := by unfold maxK at hlK; exact hlK

  obtain ⟨r, ⟨h1, h2⟩, hr⟩ : ∃ r : ℝ,
      μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d) ∈ Set.Ioo 0 ⊤ ∧ 0 < r := by
    refine ((hlim.eventually (Ioo_mem_nhds ?_ ?_)).and self_mem_nhdsWithin).exists
    · exact Metric.measure_ball_pos _ _ one_pos
    · exact measure_ball_lt_top
  have hB0 : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ 0 := by
    intro h
    rw [h, ENNReal.zero_div] at h1
    exact lt_irrefl _ h1
  have hBt : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h2
    exact lt_irrefl _ h2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => uMat g := by
    unfold uMat
    fun_prop
  have hc : Continuous fun g : Formalism.REAL.UJ ε => √(Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    fun_prop
  have hBn : {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ∈ 𝓝 (1 : Formalism.REAL.UJ ε) := by
    have h1' : √(Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r := by
      rw [show uMat (1 : Formalism.REAL.UJ ε) = 1 from rfl, sub_self]
      simp [Formalism.REAL.hs, hr]
    exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds h1') fun g hg =>
      show √(Formalism.REAL.hs (uMat g - 1)) ≤ r from le_of_lt hg

  have hcomm : ∀ g, g * l ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ↔
      l * g ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro g
    show √(Formalism.REAL.hs (uMat (g * l) - 1)) ≤ r ↔ √(Formalism.REAL.hs (uMat (l * g) - 1)) ≤ r
    rw [show uMat (g * l) = uMat g * uMat l from rfl, show uMat (l * g) = uMat l * uMat g from rfl,
      hs_conj (uMat l) (uMat g) hlU]
  exact map_mul_right_of_conj_nhds_subgroup M hM μ hμc hinv _
    (isClosed_le hc continuous_const).measurableSet hBn hB0 hBt l hlM hcomm

end GlobalTheory.GaugeRightInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitaryStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_map_mul_right_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (M : Set (Formalism.REAL.UJ ε)) → IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ → ∀ l ∈ M, l ∈ maxK ε → μ.map (fun g => g * l) = μ := by
  first | exact @GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | exact GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | (intros; apply GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlace
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Carry

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


omit [NumberField E] in
theorem prVec_mulVec (v : HeightOneSpectrum (𝓞 F)) (y : GL (Fin n) (E ⊗[F] Ad F)) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (y.1 *ᵥ x) = (bc (prV (E := E) v) y).1 *ᵥ prVec v x := by
  funext i
  exact RingHom.map_mulVec (prV (E := E) v) y.1 x i

omit [NumberField E] in
theorem prVec_single_self (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec v (fun i => Formalism.UG.P.afsplitIE v (x i)) = x := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE v (x i)

omit [NumberField E] in
theorem prVec_single_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec w (fun i => Formalism.UG.P.afsplitIE v (x i)) = 0 := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE_ne v w h (x i)

theorem carry_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  intro F E _ _ _ _ _ n L M hL hM y
  have lgL := GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n L hL
  have lgM := GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n M hM
  constructor
  · intro h v x
    have h1 := h (fun i => Formalism.UG.P.afsplitIE v (x i))
    rw [lgL, lgM] at h1
    constructor
    · intro hx
      have h2 := h1.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw]; exact Submodule.zero_mem _) v
      rwa [prVec_mulVec, prVec_single_self] at h2
    · intro hx
      have h2 := h1.2 (fun w => by
        rw [prVec_mulVec]
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw, Matrix.mulVec_zero]; exact Submodule.zero_mem _) v
      rwa [prVec_single_self] at h2
  · intro h x
    rw [lgL, lgM]
    refine forall_congr' fun v => ?_
    rw [prVec_mulVec]
    exact h v _

end GlobalTheory.St.G.Carry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlaceStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_carry_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.Carry.carry_iff | exact GlobalTheory.St.G.Carry.carry_iff | (intros; apply GlobalTheory.St.G.Carry.carry_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DFactsHolds
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Count.Cartan

noncomputable section

namespace GlobalTheory.Dec

theorem dOp_fin_zero (g : Matrix (Fin 0) (Fin 0) ℂ) : dOp g = 0 := by

  rw [Subsingleton.elim g 0]
  simp [GlobalTheory.Count.dOp]

private theorem isHermitian_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Formalism.REAL.inP ε X) : X.IsHermitian := by
  have hX' : Formalism.REAL.inG ε X ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := hX
  have hG : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX'.1
  have h1 : Xᴴ * Formalism.REAL.Jm ε = X * Formalism.REAL.Jm ε := by
    rw [hX'.2]
    exact eq_neg_of_add_eq_zero_left hG
  have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
  simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h2
  exact h2

private theorem isUnit_of_inUJ_flag_measures' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : IsUnit g := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.REAL.Jm_mul_self]
  exact (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h)

private theorem dOp_one' {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) :
    dOp (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have hP : Formalism.REAL.inP ε 0 := by simp [Formalism.REAL.inP, Formalism.REAL.inG]
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn (Matrix.unitaryGroup (Fin n) ℂ).one_mem hP
  have hs0 : Formalism.REAL.hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [Formalism.REAL.hs]
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at h0 h1
  rw [hs0, Real.sqrt_zero] at h1
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hle : dOp (1 : Matrix (Fin n) (Fin n) ℂ) ≤ 0 := by
    by_contra h
    have := mul_pos hs2 (lt_of_not_ge h)
    linarith
  exact le_antisymm hle h0

theorem dFacts_holds : DFacts := by
  intro n ε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    refine ⟨fun g _ => ⟨by rw [dOp_fin_zero], by rw [dOp_fin_zero, dOp_fin_zero],
      fun g' _ => by rw [dOp_fin_zero, dOp_fin_zero, dOp_fin_zero, add_zero],
      fun k₁ _ k₂ _ => by rw [dOp_fin_zero, dOp_fin_zero]⟩,
      GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ⟨?_, ?_, ?_⟩⟩
    · exact GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX)
    · rw [dOp_fin_zero, mul_zero]
      exact Real.sqrt_nonneg _
    · rw [dOp_fin_zero, mul_zero]
      simp [Formalism.REAL.hs]
  · refine ⟨fun g hg => ?_, GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ?_⟩
    · have hgU : Formalism.REAL.inUJ ε g := hg
      have hu := isUnit_of_inUJ_flag_measures' hgU
      refine ⟨?_, GlobalTheory.Count.Cartan.dOp_inv hgU,
        fun g' hg' => GlobalTheory.Count.Cartan.dOp_mul_le hn hu (isUnit_of_inUJ_flag_measures' hg'),
        fun k₁ hk₁ k₂ hk₂ => GlobalTheory.Count.Cartan.dOp_unitary hk₁.1 hk₂.1 g⟩

      have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hu
      have hinv : IsUnit g⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hu
      have h := GlobalTheory.Count.Cartan.dOp_mul_le hn hu hinv
      rw [Matrix.mul_nonsing_inv g hdet, dOp_one' hn ε, GlobalTheory.Count.Cartan.dOp_inv hgU] at h
      linarith
    · obtain ⟨-, h1, h2⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hk.1 hX
      exact ⟨GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX), h1, h2⟩

end GlobalTheory.Dec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousUpperOff
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.USplit

def coords {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : UT r → ℂ := fun p => A p.1.1 p.1.2

theorem upper_of_lt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : a < b) : upper x a b = x ⟨(a, b), h⟩ := by
  unfold upper
  rw [dif_pos h]

theorem upper_diag {r : ℕ} (x : UT r → ℂ) (a : Fin r) : upper x a a = 1 := by
  unfold upper
  rw [dif_neg (lt_irrefl a), if_pos rfl]

theorem upper_of_gt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : b < a) : upper x a b = 0 := by
  unfold upper
  rw [dif_neg (lt_asymm h), if_neg (ne_of_gt h)]

theorem mul_apply_lt {r : ℕ} (x y : UT r → ℂ) {a b : Fin r} (h : a < b) :
    (upper x * upper y) a b = x ⟨(a, b), h⟩ + y ⟨(a, b), h⟩ +
      ∑ c, if a < c ∧ c < b then upper x a c * upper y c b else 0 := by
  rw [Matrix.mul_apply]
  have key : ∀ c, upper x a c * upper y c b =
      ((if c = a then y ⟨(a, b), h⟩ else 0) + (if c = b then x ⟨(a, b), h⟩ else 0)) +
        (if a < c ∧ c < b then upper x a c * upper y c b else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hac
    · have hcb : c ≠ b := ne_of_lt (hca.trans h)
      rw [upper_of_gt x hca, zero_mul, if_neg (ne_of_lt hca), if_neg hcb,
        if_neg (fun k => lt_asymm hca k.1)]
      simp
    · subst hca
      rw [upper_diag, one_mul, upper_of_lt y h, if_pos rfl, if_neg (ne_of_lt h),
        if_neg (fun k => lt_irrefl _ k.1)]
      simp
    · rcases lt_trichotomy c b with hcb | hcb | hbc
      · rw [if_neg (ne_of_gt hac), if_neg (ne_of_lt hcb), if_pos ⟨hac, hcb⟩]
        simp
      · subst hcb
        rw [upper_diag, mul_one, upper_of_lt x h, if_neg (ne_of_gt h), if_pos rfl,
          if_neg (fun k => lt_irrefl _ k.2)]
        simp
      · rw [upper_of_gt y hbc, mul_zero, if_neg (ne_of_gt hac), if_neg (ne_of_gt hbc),
          if_neg (fun k => lt_asymm hbc k.2)]
        simp
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a, Finset.sum_ite_eq' Finset.univ b]
  simp only [Finset.mem_univ, if_true]
  ring

theorem upper_coords_mul {r : ℕ} (x y : UT r → ℂ) : upper (coords (upper x * upper y)) = upper x * upper y := by
  ext a b
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [upper_of_lt _ hab]
    rfl
  · subst hab
    rw [upper_diag, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [upper_diag, upper_diag, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [upper_of_gt x hlt, zero_mul]
      · rw [upper_of_gt y hgt, mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [upper_of_gt _ hba, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rcases lt_or_ge c a with hca | hac
    · rw [upper_of_gt x hca, zero_mul]
    · rw [upper_of_gt y (lt_of_lt_of_le hba hac), mul_zero]

theorem continuous_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : a < b
  · simp only [upper, dif_pos h]
    exact continuous_apply _
  · simp only [upper, dif_neg h]
    exact continuous_const

theorem continuous_upperIn {r : ℕ} (β : Fin r → ℕ) : Continuous (upperIn β) := by
  have hg : Continuous fun (x : UTin β → ℂ) (p : UT r) =>
      if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 = β p.1.2
    · simp only [dif_pos h]
      exact continuous_apply _
    · simp only [dif_neg h]
      exact continuous_const
  exact (continuous_upper r).comp hg

theorem continuous_upperOff {r : ℕ} (β : Fin r → ℕ) : Continuous (upperOff β) := by
  have hg : Continuous fun (x : UToff β → ℂ) (p : UT r) =>
      if h : β p.1.1 ≠ β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 ≠ β p.1.2
    · simp only [dif_pos h]
      exact continuous_apply _
    · simp only [dif_neg h]
      exact continuous_const
  exact (continuous_upper r).comp hg

def prodMap {r : ℕ} (β : Fin r → ℕ) (u : UT r → ℂ) : UT r → ℂ :=
  coords (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1))

theorem continuous_prodMap {r : ℕ} (β : Fin r → ℕ) : Continuous (prodMap β) := by
  have h1 : Continuous fun u : UT r → ℂ => upperIn β (fun p => u p.1) :=
    (continuous_upperIn β).comp (continuous_pi fun p => continuous_apply _)
  have h2 : Continuous fun u : UT r → ℂ => upperOff β (fun p => u p.1) :=
    (continuous_upperOff β).comp (continuous_pi fun p => continuous_apply _)
  exact continuous_pi fun p => (h1.matrix_mul h2).matrix_elem p.1.1 p.1.2

private theorem shearCond_prodMap {r : ℕ} (β : Fin r → ℕ) :
    Formalism.FourierDecayAlt.P.ShearMeasurability.ShearCond (fun p : UT r => p.1.2.val - p.1.1.val) (prodMap β) := by
  intro q x y hxy
  obtain ⟨⟨a, b⟩, h⟩ := q
  have e : ∀ u : UT r → ℂ, prodMap β u ⟨(a, b), h⟩ - u ⟨(a, b), h⟩ = ∑ c, if a < c ∧ c < b then
      upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) a c *
      upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) c b else 0 := by
    intro u
    have hin : upperIn β (fun p => u p.1) = upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) := by
      unfold upperIn
      congr 1
    have hoff : upperOff β (fun p => u p.1) =
        upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) := by
      unfold upperOff
      congr 1
    show (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1)) a b - _ = _
    rw [hin, hoff, mul_apply_lt _ _ h]
    by_cases hb : β a = β b
    · have hb' : ¬ β a ≠ β b := not_not.mpr hb
      simp only [if_pos hb, if_neg hb', add_zero, add_sub_cancel_left]
    · simp only [if_neg hb, if_pos hb, zero_add, add_sub_cancel_left]
  rw [e x, e y]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 : c.val - a.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    have h2 : b.val - c.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    rw [upper_of_lt _ hc.1, upper_of_lt _ hc.2, upper_of_lt _ hc.1, upper_of_lt _ hc.2,
      hxy ⟨(a, c), hc.1⟩ h1, hxy ⟨(c, b), hc.2⟩ h2]
  · rfl

theorem prodMap_mp {r : ℕ} (β : Fin r → ℕ) : MeasurePreserving (prodMap β) volume volume := Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp _ (prodMap β) (continuous_prodMap β).measurable (shearCond_prodMap β)

theorem lebesgue_split : ∀ (r : ℕ) (β : Fin r → ℕ), Monotone β → (∀ (x : UTin β → ℂ) (y : UToff β → ℂ), ∃ u : UT r → ℂ, upper u = upperIn β x * upperOff β y) ∧ ∀ f : (Fin r → Fin r → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u)) = ∫⁻ y : UToff β → ℂ, ∫⁻ x : UTin β → ℂ, f (Matrix.of.symm (upperIn β x * upperOff β y)) := by
  intro r β _
  refine ⟨fun x y => ⟨coords (upperIn β x * upperOff β y), ?_⟩, fun f hf => ?_⟩
  · unfold upperIn upperOff
    exact upper_coords_mul _ _
  · have hc : Continuous fun u : UT r → ℂ => (Matrix.of.symm (upper u) : Fin r → Fin r → ℂ) :=
      continuous_upper r
    have hu : Measurable fun u : UT r → ℂ => f (Matrix.of.symm (upper u)) := hf.comp hc.measurable
    have hM : Continuous fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        (Matrix.of.symm (upperIn β z.1 * upperOff β z.2) : Fin r → Fin r → ℂ) :=
      ((continuous_upperIn β).comp continuous_fst).matrix_mul ((continuous_upperOff β).comp continuous_snd)
    have hG : Measurable fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) := hf.comp hM.measurable
    have hsplit := MeasureTheory.volume_preserving_piEquivPiSubtypeProd (fun _ : UT r => ℂ)
      (fun p : UT r => β p.1.1 = β p.1.2)
    have key : ∀ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) =
        f (Matrix.of.symm (upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1))) := by
      intro v
      have hp : upper (prodMap β v) = upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1) := by
        unfold prodMap upperIn upperOff
        exact upper_coords_mul _ _
      rw [hp]
    calc ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u))
        = ∫⁻ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) :=
          ((prodMap_mp β).lintegral_comp hu).symm
      _ = ∫⁻ v : UT r → ℂ, (fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
            f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)))
            (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : UT r => ℂ)
              (fun p : UT r => β p.1.1 = β p.1.2) v) := lintegral_congr fun v => key v
      _ = ∫⁻ z : (UTin β → ℂ) × (UToff β → ℂ), f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) :=
          hsplit.lintegral_comp hG
      _ = _ := lintegral_prod_symm _ hG.aemeasurable

end GlobalTheory.Amp.USplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKStableOfMemLowKSub
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem exists_kStable_of_mem_lowKSub (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (hw : w ∈ lowKSub ε lam σ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧ w ∈ S := by
  classical
  obtain ⟨s, hs, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  refine ⟨⨆ i ∈ s, i, ?_, ?_, hws⟩
  · have hfg : (⨆ i ∈ s, i).FG := by
      refine Submodule.fg_biSup s (fun i => i) (fun i hi => ?_)
      obtain ⟨hfin, -⟩ := hs hi
      exact (Submodule.fg_iff_finiteDimensional i).2 hfin
    exact (Submodule.fg_iff_finiteDimensional _).1 hfg
  · intro g hg v hv
    have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine iSup₂_le fun i hi => ?_
      obtain ⟨-, hstab, -⟩ := hs hi
      intro x hx
      exact (le_iSup₂ (f := fun j (_ : j ∈ s) => j) i hi) (hstab g hg x hx)
    exact hle hv

theorem isKFin_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), w ∈ lowKSub ε lam σ → IsKFin ε σ w := by
  intro n ε lam H _ _ σ w hw
  obtain ⟨S, hfin, hstab, hwS⟩ := exists_kStable_of_mem_lowKSub n ε lam H σ w hw
  exact ⟨S, hfin, hwS, hstab⟩

end GlobalTheory
end
