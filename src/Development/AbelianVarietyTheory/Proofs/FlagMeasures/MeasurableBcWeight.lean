module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHilbertSchmidtNormSqBesselAmplitudeLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelSchurOfFormalDegreeDensity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselDoubleCosetMeasureBigCellEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarOnBesselSubgroupProdMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarOnBesselSubgroupProdMap
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.ProdHaarS

theorem isHaarOn_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN →
    IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨-, -, h, -⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  exact h

end GlobalTheory.SgInf.ProdHaarS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarOnBesselSubgroupProdMapStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarOn_besselSubgroup_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN → IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  first | exact @GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | exact GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | (intros; apply GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitary
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AmpMeas

theorem stronglyMeasurable_indicator_of_continuousOn {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {S : Set X}
    (hS : MeasurableSet S) {f : X → W} (hf : ContinuousOn f S) : StronglyMeasurable (S.indicator f) := by
  classical
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  have := hf.measurable_piecewise (g := fun _ => (0 : W)) continuousOn_const hS
  have h2 : S.indicator f = S.piecewise f fun _ => (0 : W) := by
    funext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [h2]
  exact this.stronglyMeasurable

theorem continuous_hsNormSq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Continuous fun A : Wq →L[ℂ] Wp => hsNormSq A := by
  unfold hsNormSq hsInner
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
  have : Continuous fun A : Wq →L[ℂ] Wp => A (stdOrthonormalBasis ℂ Wq i) :=
    (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  exact this.inner this

theorem measurable_hsNormSq_ampJ : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  intro k r Wp _ _ _ _ Wq _ _ _ μG c Φ Φ' hH hΦ hΦ'
  haveI : SigmaFinite μG := hH.1
  have hcl : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hcl' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hcl
  set S : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ GG k r} with hSdef
  have hS : MeasurableSet S := hcl'.measurableSet
  have hmul : ∀ γ x : Mat k r, γ ∈ GG k r → x ∈ GG k r → γ * x ∈ GG k r := by
    intro γ x hγ hx
    have hs' : γᴴ * Hpk k r * γ = Hpk k r := hγ
    have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
    show (γ * x)ᴴ * Hpk k r * (γ * x) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * γᴴ * Hpk k r * (γ * x) = xᴴ * (γᴴ * Hpk k r * γ) * x := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hs', hx']
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  let F : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p =>
    (innerSL ℂ (Φ' (Matrix.of p.2))).smulRight (Φ (Matrix.of p.1 * Matrix.of p.2))
  have hcont : Continuous fun p : Wq × Wp => (innerSL ℂ p.1).smulRight p.2 := by
    have h1 : Continuous fun p : Wq × Wp => innerSL ℂ p.1 := (innerSL ℂ).continuous.comp continuous_fst
    exact ((ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂).comp (h1.prodMk continuous_snd)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => Φ' (Matrix.of p.2)) (S ×ˢ S) :=
    hΦ'.comp (hof.comp continuous_snd).continuousOn fun p hp => hp.2
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => Φ (Matrix.of p.1 * Matrix.of p.2)) (S ×ˢ S) :=
    hΦ.comp ((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).continuousOn
      fun p hp => hmul _ _ hp.1 hp.2
  have hF : ContinuousOn F (S ×ˢ S) := hcont.comp_continuousOn (h1.prodMk h2)
  have hsm : StronglyMeasurable ((S ×ˢ S).indicator F) :=
    stronglyMeasurable_indicator_of_continuousOn (hS.prod hS) hF
  have hint : StronglyMeasurable fun γ => ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG :=
    hsm.integral_prod_right'
  have hm : Measurable fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) :=
    (continuous_hsNormSq.comp_stronglyMeasurable (hint.const_smul (c : ℂ)⁻¹)).measurable
  have hae : ∀ᵐ x ∂μG, x ∈ S := by rw [ae_iff]; exact hH.2.2.1
  have heq : (S.indicator fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) =
      S.indicator fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) := by
    refine Set.indicator_congr fun γ hγ => ?_
    unfold ampJ
    congr 2
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    have : (γ, x) ∈ S ×ˢ S := ⟨hγ, hx⟩
    simp only [Set.indicator_of_mem this, F]
  rw [heq]
  exact hm.indicator hS

end GlobalTheory.Amp.AmpMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitaryStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  first | exact @GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | exact GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | (intros; apply GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ <;> assumption)
end
end

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.SchurBound

theorem psi_eq_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Formalism.QuantumDeterminants.psi k r z c = psiGen k r z (fun _ => c) := by
  funext g
  simp only [Formalism.QuantumDeterminants.psi, psiGen, Formalism.QuantumDeterminants.ell, ellA, Finset.mul_sum]

theorem volUn_pos (j : ℕ) : 0 < volUn j := by
  unfold volUn
  exact Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (by exact_mod_cast Nat.factorial_pos i)

theorem bcWeight_nonneg (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)
  · exact le_rfl

theorem measurable_bcWeight (k r : ℕ) (T T' : ℝ) : Measurable (bcWeight k r T T') := by
  unfold bcWeight
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const (Complex.continuous_normSq.measurable.comp measurable_snd)
  · exact (by fun_prop : Continuous fun q : (Fin r → ℂ) × ℂ =>
      (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) * (Complex.normSq q.2 - T * T') ^ (k - 1)).measurable

open scoped Matrix.Norms.Elementwise in
theorem smooth_smul {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (a : ℂ) (v : H) (h : IsSmoothVec (k := k) (r := r) σ v) :
    IsSmoothVec (k := k) (r := r) σ (a • v) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hEq⟩ := h g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩
  simp only [map_smul, hEq g hg hgH]

theorem DD_smul_le {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (a : ℂ) (v : H) : DD σ (a • v) ≤ DD σ v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)

theorem lintegral_cell {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (w : X → ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (φ : X → Y) (S : Set Y) (F : Y → ℝ) (a : ℝ) (ha : 0 < a)
    (hφ : AEMeasurable φ (μ.withDensity fun x => ENNReal.ofReal (w x)))
    (hS : (ENNReal.ofReal a • (μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) Sᶜ = 0)
    (hF : Measurable (S.indicator F)) :
    ∫⁻ y, ENNReal.ofReal (F y) ∂(ENNReal.ofReal a • (μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) =
      ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (w x * F (φ x)) ∂μ := by
  have ha' : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hdm : Measurable fun x => ENNReal.ofReal (w x) := ENNReal.measurable_ofReal.comp hw
  have hg : Measurable fun y => ENNReal.ofReal (S.indicator F y) := ENNReal.measurable_ofReal.comp hF
  have h1 : ((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) Sᶜ = 0 := by
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hS
    exact hS.resolve_left ha'
  have h2 : ∀ᵐ y ∂((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ), y ∈ S := by
    rw [ae_iff]
    exact h1
  have h3 : ∀ᵐ x ∂(μ.withDensity fun x => ENNReal.ofReal (w x)), φ x ∈ S := by
    rw [ae_iff]
    exact nonpos_iff_eq_zero.mp ((Measure.le_map_apply hφ Sᶜ).trans h1.le)
  have h4 : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) ≠ 0 → φ x ∈ S := (ae_withDensity_iff hdm).mp h3
  rw [lintegral_smul_measure]
  congr 1
  calc ∫⁻ y, ENNReal.ofReal (F y) ∂((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ)
      = ∫⁻ y, ENNReal.ofReal (S.indicator F y) ∂((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [h2] with y hy
        rw [Set.indicator_of_mem hy]
    _ = ∫⁻ x, ENNReal.ofReal (S.indicator F (φ x)) ∂(μ.withDensity fun x => ENNReal.ofReal (w x)) :=
        lintegral_map' hg.aemeasurable hφ
    _ = ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal (S.indicator F (φ x)) ∂μ :=
        lintegral_withDensity_eq_lintegral_mul₀' hdm.aemeasurable (hg.comp_aemeasurable hφ)
    _ = ∫⁻ x, ENNReal.ofReal (w x * F (φ x)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [h4] with x hx
        rw [ENNReal.ofReal_mul (hw0 x)]
        by_cases h0 : ENNReal.ofReal (w x) = 0
        · rw [h0, zero_mul, zero_mul]
        · rw [Set.indicator_of_mem (hx h0)]

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ w w' θ} {W : LocW D.R.k D.R.rS} (h : GoodW D τ w w' θ W) :
    GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam} {A : LocS W} (h : GoodS D lam A) :
    GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem factor_le (b m T T' θ CT C1 C : ℝ) (r : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m) (hT0 : 0 < T) (hT0' : 0 < T')
    (hθ0 : 0 < θ) (hT : T ≤ b ^ (CT * m)) (hT' : T' ≤ b ^ (CT * m)) (hθ : θ ≤ b ^ (C1 * m ^ 2))
    (hC : 2 * |CT| + 2 * C1 ≤ C) : T * T' * θ ^ 2 / 2 ^ (r + 1) ≤ b ^ (C * m ^ 2) := by
  have hb0 : 0 < b := by linarith
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hx1 : CT * m ≤ |CT| * m ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self CT) (by linarith)).trans
      (mul_le_mul_of_nonneg_left hm2 (abs_nonneg CT))
  have h1 : T * T' ≤ b ^ (2 * |CT| * m ^ 2) := by
    calc T * T' ≤ b ^ (CT * m) * b ^ (CT * m) := mul_le_mul hT hT' hT0'.le (Real.rpow_nonneg hb0.le _)
      _ = b ^ (CT * m + CT * m) := (Real.rpow_add hb0 _ _).symm
      _ ≤ b ^ (2 * |CT| * m ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have h2 : θ ^ 2 ≤ b ^ (2 * C1 * m ^ 2) := by
    have hq : θ ^ 2 ≤ b ^ (C1 * m ^ 2) * b ^ (C1 * m ^ 2) := by nlinarith
    calc θ ^ 2 ≤ b ^ (C1 * m ^ 2) * b ^ (C1 * m ^ 2) := hq
      _ = b ^ (C1 * m ^ 2 + C1 * m ^ 2) := (Real.rpow_add hb0 _ _).symm
      _ = b ^ (2 * C1 * m ^ 2) := by ring_nf
  have h3 : T * T' * θ ^ 2 ≤ b ^ (C * m ^ 2) := by
    calc T * T' * θ ^ 2 ≤ b ^ (2 * |CT| * m ^ 2) * b ^ (2 * C1 * m ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg hb0.le _)
      _ = b ^ (2 * |CT| * m ^ 2 + 2 * C1 * m ^ 2) := (Real.rpow_add hb0 _ _).symm
      _ ≤ b ^ (C * m ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by nlinarith [sq_nonneg m])
  have hpos : 0 ≤ T * T' * θ ^ 2 := mul_nonneg (mul_pos hT0 hT0').le (sq_nonneg θ)
  have h2r : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
  exact (div_le_self hpos h2r).trans h3

private theorem dp_dq_div_eq_mul_div (dp dq c Vn Vk1 Vk deg T T' θ X P t : ℝ) (hc : 0 < c) (hVn : 0 < Vn)
    (hVk1 : 0 < Vk1) (hVk : 0 < Vk) (hdeg : 0 < deg) (hT : 0 < T) (hT' : 0 < T') (hθ : 0 < θ) (hX : 0 < X)
    (hP : 0 < P) (ht : 0 < t) :
    dp * dq / (deg / (c * Vn)) / (c * t * Vk ^ 2 / Vk1 / (P * (T * T')) / (X⁻¹ * θ) ^ 2) =
      P * (dp * dq * Vn * Vk1 / (deg * Vk ^ 2 * X ^ 2)) * (T * T' * θ ^ 2 / t) := by
  field_simp

end GlobalTheory.Amp.SchurBound

namespace GlobalTheory.Amp

open SchurBound

theorem schurSt_of_big_tie : ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → cdScaleTie D → BSch D large₂ C' Cl Cg cb Cu cT CT C0 → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 → SchurSt D large₂ C' Cl Cg cb Cu cT CT C0 C1 C := by
  intro Cg cb Cu cT CT C0 C1
  refine ⟨2 * |CT| + 2 * C1, fun C hC => ⟨0, ?_⟩⟩
  intro D large₂ C' Cl hBig hTie hBS hLI hZ τ w w' hTT θ hθw W hW A hA μsec hsec
  obtain ⟨-, -, hb, hm, hr, -, -, hmk, hv, -, -, -, -, -, -, -, hTr, -, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hBig.1 hZ
  have hb2 : (2 : ℝ) ≤ large₂.sc.b := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hk1 : 1 ≤ D.R.k := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (show 1 ≤ D.R.m by omega)
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθw.1
  have hv0 : 0 < D.host.v := by linarith
  have h2v : 0 < 2 * D.host.v := by linarith
  have hTw : 0 < Tr D w := by
    have h3 := hTT.2.2.1
    unfold Tr
    exact_mod_cast (show 0 < (D.mem w).A.T by omega)
  have hTw' : 0 < Tr D w' := by
    have h3 := hTT.2.2.2.1
    unfold Tr
    exact_mod_cast (show 0 < (D.mem w').A.T by omega)
  have hW0 := hW
  obtain ⟨-, -, hz, hz', hTz, hTz', hμG, hμW, hμW1, hμW', hμW'1, hμN, -, -⟩ := hW0
  have hA0 := hA
  obtain ⟨-, -, hB, hB', hsm, hv0ne, -, hcN, hl2, hl2', P, hCay, hFdeg⟩ := hA0
  obtain ⟨hUR, hIR, -, hOS, hOS'⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W (lamD D τ) A hθ0 hv0 hTT hW hA
  obtain ⟨-, -, hnt, hπU, hπI, -, -, -, hμNH, hQ, -, -, hΦc, -, -⟩ := hOS
  obtain ⟨-, -, hnt', hπU', hπI', -, -, -, -, hQ', -, -, hΦc', -, -⟩ := hOS'
  obtain ⟨hM, hM', hDec⟩ := hLI hZ τ w w' θ W hTT hW A hA
  have hTzp : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hTw
  have hTzp' : 0 < Tz D.R.k D.R.rS W.z' := by rw [hTz']; exact hTw'
  have hSide : SideIrr W.z W.π (muProd W.μW W.μN) :=
    ⟨⟨hz, hTzp, hπU, GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ hz hTzp hμW hμNH, inferInstance⟩, hπI, hnt⟩
  have hSide' : SideIrr W.z' W.π' (muProd W.μW' W.μN) :=
    ⟨⟨hz', hTzp', hπU', GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ hz' hTzp' hμW' hμNH, inferInstance⟩, hπI', hnt'⟩

  obtain ⟨c, hc0, hcD, -⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity (2 * D.R.rS + D.R.k + 1) (GG D.R.k D.R.rS) W.μG
    (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group D.R.k D.R.rS) hμG

  have hSch := GlobalTheory.T.besselModel_schur_of_formalDegree_density D.R.k D.R.rS A.σ (epsSH D.R) D.cd (D.s.cdScale _ (epsSH D.R)) P A.deg c W.μG
    (fun p q e h1 h2 S hS => hTie _ _ p q e h1 h2 S hS) hCay hFdeg hc0 hμG hcD
  have hVn := volUn_pos (2 * D.R.rS + D.R.k + 1)
  have hdeg : 0 < A.deg := by
    have h := hSch.1
    by_contra hn
    rw [not_lt] at hn
    have := div_nonpos_of_nonpos_of_nonneg hn (mul_pos hc0 hVn).le
    linarith
  have hnorm : ‖(((‖A.v0‖ : ℝ) : ℂ))⁻¹ • A.v0‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0ne)]
  have hStd : StdSm A.σ ((((‖A.v0‖ : ℝ) : ℂ))⁻¹ • A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5) W.μG
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1))) :=
    ⟨⟨hk1, hUR, hIR, hnorm, hμG, hSch, le_rfl,
      hDec.mono (SetLike.coe_subset_coe.mpr (DD_smul_le A.σ _ A.v0)), inferInstance⟩,
      smooth_smul A.σ _ A.v0 hsm⟩

  have hpsi : ∀ z, psiS D z = psiGen D.R.k D.R.rS z
      (fun _ => ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) :=
    fun z => psi_eq_psiGen _ _ _ _
  simp only [hpsi] at hM hB hM' hB'

  have hIso := hBS hZ τ w w' θ W hW A hA hTw
  have hIso' := hBS hZ τ w' w θ (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA) hTw'

  have hκ : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := mul_pos (Real.rpow_pos_of_pos h2v _) hθ0
  obtain ⟨hφ, hDis⟩ := GlobalTheory.T.besselDoubleCosetMeasure_bigCell_eq D.R.k D.R.rS W.z W.z' μsec W.μG W.μW W.μW' c
    ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) hk1 hz hz' hTzp hTzp' hsec hc0 hκ hμG hcD hμW hμW1 hμW' hμW'1
  have hN : haarLie (Nset D.R.k D.R.rS) (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ)) = W.μN :=
    hμN.symm
  rw [hN, hTz, hTz'] at hDis
  rw [hTz, hTz'] at hφ

  have hF := GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary D.R.k D.R.rS W.μG A.cN A.Φ A.Φ' hμG hΦc hΦc'
  have hX : 0 < (2 * D.host.v) ^ (D.R.rS * D.R.k) := pow_pos h2v _
  have hP : 0 < (Tr D w * Tr D w') ^ (D.R.k - 1) := pow_pos (mul_pos hTw hTw') _
  have ha : 0 < c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 / volUn (D.R.k - 1) / (Tr D w * Tr D w') ^ D.R.k /
      ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) ^ 2 := by
    have := volUn_pos D.R.k
    have := volUn_pos (D.R.k - 1)
    have := mul_pos hTw hTw'
    positivity
  have hcell := SchurBound.lintegral_cell volume (bcWeight D.R.k D.R.rS (Tr D w) (Tr D w'))
    (measurable_bcWeight _ _ _ _) (bcWeight_nonneg _ _ _ _)
    (fun q : (Fin D.R.rS → ℂ) × ℂ => (Matrix.of.symm (bigCell D.R.k D.R.rS q.1 (μsec q.2)) : Mt D.R.k D.R.rS))
    {x : Mt D.R.k D.R.rS | Matrix.of x ∈ GG D.R.k D.R.rS}
    (fun γ => hsNormSq (ampJ W.μG A.cN A.Φ A.Φ' (Matrix.of γ))) _ ha hφ (by
      refine measure_mono_null ?_ hDis.2.1
      intro x hx hG
      exact hx (Greg_subset _ _ hG)) hF
  have hBound := GlobalTheory.T.lintegral_hilbertSchmidtNormSq_besselAmplitude_le D.R.k D.R.rS A.σ A.v0 _ _ A.cN W.μG (muProd W.μW W.μN) (muProd W.μW' W.μN)
    W.νS W.νS' _ W.z W.z' _ _ W.π W.π' A.B A.B' hv0ne hStd hSide hSide' hQ hQ' hM hM' hB hB' hcN hl2 hl2'
    hIso hIso' hDis
  have key : ENNReal.ofReal (c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 / volUn (D.R.k - 1) /
      (Tr D w * Tr D w') ^ D.R.k / ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) ^ 2) *
      MMv D w w' A μsec ≤ ENNReal.ofReal ((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
        (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1)))) :=
    hcell.symm.trans_le hBound
  have hXa : ∀ x y : ℝ, y ≠ 0 → y * (x / y) = x := fun x y hy => by field_simp
  have h2 : MMv D w w' A μsec ≤ ENNReal.ofReal ((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1))) / (c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 /
        volUn (D.R.k - 1) / (Tr D w * Tr D w') ^ D.R.k / ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) ^ 2)) := by
    refine (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top).mp ?_
    rw [← ENNReal.ofReal_mul ha.le, hXa _ _ ha.ne']
    exact key
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hVk := volUn_pos D.R.k
  have hVk1 := volUn_pos (D.R.k - 1)
  have hE : (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) = ((2 * D.host.v) ^ (D.R.rS * D.R.k))⁻¹ := by
    rw [Real.rpow_neg h2v.le, ← Nat.cast_mul, Real.rpow_natCast]
  have hX2 : (2 * D.host.v) ^ (2 * D.R.rS * D.R.k) = ((2 * D.host.v) ^ (D.R.rS * D.R.k)) ^ 2 := by ring
  have hk' : (Tr D w * Tr D w') ^ D.R.k = (Tr D w * Tr D w') ^ (D.R.k - 1) * (Tr D w * Tr D w') := by
    rw [← pow_succ, Nat.sub_add_cancel hk1]
  rw [hE, hk', hX2, hr, SchurBound.dp_dq_div_eq_mul_div _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hVn (volUn_pos _) (volUn_pos _) hdeg hTw hTw' hθ0
    hX hP (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hP.le (by positivity))
  exact factor_le _ _ _ _ _ _ _ _ _ (by linarith) hm1 hTw hTw' hθ0 (hTr w) (hTr w') hθw.2 hC

end GlobalTheory.Amp
