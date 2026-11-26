module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DKerHasCompactSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoostDecompositionNormBoundOfEmbeddingLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryNearIdentityEqExpLogBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerLeFinset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeLieWordNormBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLe
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegree
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev

theorem isDS_lowUnit_unitary_fdegOf : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  intro n ε lam H _ _ σ h
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hvS, hv, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · have hle : S ≤ lowKSub ε lam σ := le_sSup hS
      exact hle (S.smul_mem _ hvS)
  · intro x a b
    have hx : uMat x ∈ UJset ε := x.2
    let f : H →ₗᵢ[ℂ] H := ⟨(σ (uMat x) : H →ₗ[ℂ] H), hU.2.1 _ hx⟩
    exact f.inner_map_map a b
  · intro c d w hc hw hF
    obtain ⟨hd, hI⟩ := hF
    have h1 := (hI w w w w).2
    have hc' : (0 : ℝ) < (c : ℝ) := hc
    have hww : ⟪w, w⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hpt : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g))
        = fun g => ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hpt, integral_smul_measure, integral_complex_ofReal, hww, ENNReal.coe_toReal,
      Complex.real_smul] at h1
    have h2 : (c : ℝ) * ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 * 1 / d := by
      exact_mod_cast h1
    have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / ((c : ℝ) * d) := by
      field_simp at h2 ⊢
      linarith
    unfold fdegOf
    rw [h3, hw]
    simp

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegreeStatement
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  first | exact @GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | exact GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | (intros; apply GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLa
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLa
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.DerInt

theorem taylor_der (f f1 f2 : ℝ → ℂ) (τ M : ℝ) (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hS : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f t‖ ≤ τ ^ 2) (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f2 t‖ ≤ M) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ‖f1 0‖ ≤ (2 + M) * τ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_refl _, zero_le_one⟩)
  have hd1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f1 x - f1 0‖ ≤ M * (x - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun x _ => (hf1 x).hasDerivWithinAt)
      (fun x hx => hM x (Set.Ico_subset_Icc_self hx))
  have hg : ∀ x : ℝ, HasDerivAt (fun s : ℝ => f s - (s : ℂ) * f1 0) (f1 x - f1 0) x := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x := by
      have := (hasDerivAt_id x).ofReal_comp
      convert this using 1
      · rfl
    have h2 := (hf x).sub (h1.mul_const (f1 0))
    rw [one_mul] at h2
    exact h2
  have hd2 := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := τ) (C := M * τ)
    (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by
      have := hd1 x ⟨hx.1, (hx.2.le.trans hτ1)⟩
      calc _ ≤ M * (x - 0) := this
        _ ≤ M * τ := by gcongr; linarith [hx.2]) τ ⟨hτ0.le, le_rfl⟩
  have hfτ := hS τ ⟨hτ0.le, hτ1⟩
  have hf0 := hS 0 ⟨le_rfl, zero_le_one⟩
  have e : (τ : ℂ) * f1 0 = (f τ - f 0) - ((f τ - (τ : ℂ) * f1 0) - (f 0 - ((0 : ℝ) : ℂ) * f1 0)) := by
    push_cast; ring
  have hn : ‖(τ : ℂ) * f1 0‖ = τ * ‖f1 0‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
  have hb : τ * ‖f1 0‖ ≤ τ ^ 2 + τ ^ 2 + M * τ * (τ - 0) := by
    rw [← hn, e]
    calc _ ≤ ‖f τ - f 0‖ + ‖(f τ - (τ : ℂ) * f1 0) - (f 0 - ((0 : ℝ) : ℂ) * f1 0)‖ := norm_sub_le _ _
      _ ≤ (‖f τ‖ + ‖f 0‖) + M * τ * (τ - 0) := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have : τ * ‖f1 0‖ ≤ τ * ((2 + M) * τ) := by nlinarith
  exact le_of_mul_le_mul_left this hτ0

theorem coef_hasDerivAt {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (UJset ε) π) {Y : Mat m} (hY : Y ∈ lieOf (Jm ε)) {u : H}
    (hu : SmV (lieOf (Jm ε)) π u) (w : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪π (NormedSpace.exp (s • Y)) u, w⟫_ℂ) ⟪π (NormedSpace.exp (t • Y)) (dR π Y u), w⟫_ℂ t := by
  have hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Jm ε)) π := hπ
  have h0 := GlobalTheory.SmLinSub.hasDerivAt_dR hu hY
  have h1 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (t • Y)) (π (NormedSpace.exp (s • Y)) u))
      (π (NormedSpace.exp (t • Y)) (dR π Y u)) 0 :=
    ((π (NormedSpace.exp (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  have e : ∀ s : ℝ, π (NormedSpace.exp (t • Y)) (π (NormedSpace.exp (s • Y)) u) = π (NormedSpace.exp ((s + t) • Y)) u := by
    intro s
    rw [← GlobalTheory.SmLinSub.rep_mul hU' (GlobalTheory.SmLinSub.exp_mem hY t) (GlobalTheory.SmLinSub.exp_mem hY s),
      ← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left t).smul_right s), add_smul, add_comm (s • Y)]
  have h2 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp ((s + t) • Y)) u) (π (NormedSpace.exp (t • Y)) (dR π Y u)) 0 := by
    simpa only [e] using h1
  have h3 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • Y)) u) (π (NormedSpace.exp (t • Y)) (dR π Y u)) t := by
    have := HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self])
    simpa using this
  have h4 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3
  have h5 : HasDerivAt (fun s : ℝ => star ⟪w, π (NormedSpace.exp (s • Y)) u⟫_ℂ)
      (star ⟪w, π (NormedSpace.exp (t • Y)) (dR π Y u)⟫_ℂ) t := h4.star
  have e2 : ∀ a : H, star ⟪w, a⟫_ℂ = ⟪a, w⟫_ℂ := fun a => by rw [← starRingEnd_apply, inner_conj_symm]
  simpa only [e2] using h5

theorem norm_exp_sub_one_le' {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1 h2
  refine HasSum.norm_le_of_bounded h1 h2 (fun k => ?_)
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos k)) (by positivity)

theorem hsn_exp_le {m : ℕ} (Y : Mat m) (t : ℝ) (ht : |t| ≤ 1) (hY : hsn Y ≤ 1) :
    hsn (NormedSpace.exp (t • Y)) ≤ Real.sqrt m + 3 := by
  letI : NormedRing (Mat m) := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ (Mat m) := Matrix.frobeniusNormedAlgebra
  have hn : ∀ g : Mat m, hsn g = ‖g‖ := fun g => by
    rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
    simp only [Real.rpow_two]
  have h1 := norm_exp_sub_one_le' (t • Y)
  have h2 : ‖t • Y‖ ≤ 1 := by
    rw [norm_smul, ← hn, Real.norm_eq_abs]
    calc |t| * hsn Y ≤ 1 * 1 := mul_le_mul ht hY (Real.sqrt_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have h3 : ‖(1 : Mat m)‖ = Real.sqrt m := by
    rw [← hn, hsn]
    congr 1
    have : ∀ a : Fin m, ∑ b, ‖(1 : Mat m) a b‖ ^ 2 = 1 := fun a => by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Matrix.one_apply_ne' hb]
      · simp
    simp [this]
  have h4 : Real.exp ‖t • Y‖ ≤ Real.exp 1 := Real.exp_le_exp.2 h2
  have h5 := Real.exp_one_lt_d9
  have key : ‖NormedSpace.exp (t • Y)‖ ≤ Real.sqrt m + 3 := by
    have h6 := norm_le_norm_sub_add (NormedSpace.exp (t • Y)) 1
    rw [h3] at h6
    calc _ ≤ _ := h6
      _ ≤ (Real.exp ‖t • Y‖ - 1) + Real.sqrt m := add_le_add h1 le_rfl
      _ ≤ Real.sqrt m + 3 := by linarith
  rw [hn]
  exact key

theorem hsn_pos {m : ℕ} (hm : 1 ≤ m) (g : Mat m) (hg : IsUnit g) : 0 < hsn g := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rcases (Real.sqrt_nonneg _).lt_or_eq with h | h
  · exact h
  · exfalso
    have hs : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0 := by
      have h0 : 0 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2 := by positivity
      have := h.symm
      unfold hsn at this
      rwa [Real.sqrt_eq_zero h0] at this
    have hz : g = 0 := by
      ext a b
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hs a (Finset.mem_univ a)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).1 h1 b (Finset.mem_univ b)
      simpa using h2
    rw [hz] at hg
    exact not_isUnit_zero hg

theorem const_le (C₀ : ℝ) (hC₀ : 0 < C₀) (m L R : ℝ) (hm : 4 ≤ m) (hL : m + 3 ≤ L) (hR1 : 1 ≤ R) (hR : R ≤ L ^ (C₀ * m)) :
    (2 + (L ^ 2 * R ^ 2) ^ 2) * (Real.exp (50 * m ^ 3) * ((Real.sqrt m + 3) * R ^ 2) ^ (20 * m ^ 2)) * Real.exp (10 * (m - 1) ^ 2)
      ≤ Real.exp ((100 + 50 * C₀) * m ^ 4 * Real.log L) := by
  have hL7 : 7 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := by linarith
  set l := Real.log L with hl
  set r := Real.log R with hr
  have hl1 : 1 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  have hr0 : 0 ≤ r := Real.log_nonneg hR1
  have hrl : r ≤ C₀ * m * l := by
    have := Real.log_le_log hR0 hR
    rwa [Real.log_rpow hL0] at this

  have hF1 : 2 + (L ^ 2 * R ^ 2) ^ 2 ≤ Real.exp (5 * l + 4 * r) := by
    have e : Real.exp (5 * l + 4 * r) = L ^ 5 * R ^ 4 := by
      rw [Real.exp_add, hl, hr, show (5 : ℝ) * Real.log L = ((5 : ℕ) : ℝ) * Real.log L by norm_num,
        show (4 : ℝ) * Real.log R = ((4 : ℕ) : ℝ) * Real.log R by norm_num, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log hL0, Real.exp_log hR0]
    rw [e]
    have h1 : 1 ≤ R ^ 4 := one_le_pow₀ hR1
    have h2 : 7 ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL7 4
    have h3 : 1 ≤ L ^ 4 * R ^ 4 := by nlinarith
    have h4 : L ^ 5 * R ^ 4 = L * (L ^ 4 * R ^ 4) := by ring
    have h5 : (L ^ 2 * R ^ 2) ^ 2 = L ^ 4 * R ^ 4 := by ring
    rw [h4, h5]
    nlinarith

  have hb0 : 0 < (Real.sqrt m + 3) * R ^ 2 := by positivity
  have hF2 : ((Real.sqrt m + 3) * R ^ 2) ^ (20 * m ^ 2) ≤ Real.exp ((l + 2 * r) * (20 * m ^ 2)) := by
    rw [Real.rpow_def_of_pos hb0]
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hr]
    have hs : Real.sqrt m + 3 ≤ L := by
      have : Real.sqrt m ≤ m := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      linarith
    have := Real.log_le_log (by positivity) hs
    push_cast
    linarith
  have hm2 : 10 * (m - 1) ^ 2 ≤ 10 * m ^ 2 * l := by nlinarith
  have hm3 : 50 * m ^ 3 ≤ 50 * m ^ 3 * l := by
    have : 0 ≤ m ^ 3 := by positivity
    nlinarith
  have hp1 : 5 + 30 * m ^ 2 + 50 * m ^ 3 ≤ 100 * m ^ 4 := by nlinarith
  have hp2 : 4 * m + 40 * m ^ 3 ≤ 50 * m ^ 4 := by nlinarith
  have hq1 := mul_le_mul_of_nonneg_right hp1 (by linarith : (0 : ℝ) ≤ l)
  have hq2 := mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ C₀ * l)
  have hr4 : 4 * r ≤ 4 * (C₀ * m * l) := by linarith
  have hr40 : 40 * m ^ 2 * r ≤ 40 * m ^ 2 * (C₀ * m * l) := mul_le_mul_of_nonneg_left hrl (by positivity)
  calc _ ≤ Real.exp (5 * l + 4 * r) * (Real.exp (50 * m ^ 3) * Real.exp ((l + 2 * r) * (20 * m ^ 2))) *
        Real.exp (10 * (m - 1) ^ 2) := by gcongr
    _ = Real.exp ((5 * l + 4 * r) + (50 * m ^ 3 + (l + 2 * r) * (20 * m ^ 2)) + 10 * (m - 1) ^ 2) := by
        simp only [Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        linarith

theorem mem_mul {m : ℕ} {ε : Fin m → Bool} {g g' : Mat m} (hg : g ∈ UJset ε) (hg' : g' ∈ UJset ε) : g * g' ∈ UJset ε := by
  have h1 : gᴴ * Jm ε * g = Jm ε := hg
  have h2 : g'ᴴ * Jm ε * g' = Jm ε := hg'
  show (g * g')ᴴ * Jm ε * (g * g') = Jm ε
  have : g'ᴴ * (gᴴ * Jm ε * g) * g' = Jm ε := by rw [h1, h2]
  simpa [Matrix.mul_assoc, conjTranspose_mul] using this

theorem mem_inv {m : ℕ} {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  have hJ : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmLinSub.isUnit_of_mem hJ hg)
  have h1 : gᴴ * Jm ε * g = Jm ε := hg
  show (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε
  calc (g⁻¹)ᴴ * Jm ε * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Jm ε * g) * g⁻¹ := by rw [h1]
    _ = ((g⁻¹)ᴴ * gᴴ) * Jm ε * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd]; simp

theorem inner_rep {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (UJset ε) π) {a : Mat m} (ha : a ∈ UJset ε) (x y : H) :
    ⟪π a x, π a y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let Li : H →ₗᵢ[ℂ] H := { toLinearMap := (π a).toLinearMap, norm_map' := hπ.2.1 _ ha }
  exact Li.inner_map_map x y

theorem rep_mul_apply {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (UJset ε) π) {a b : Mat m} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (x : H) :
    π (a * b) x = π a (π b x) := by
  rw [hπ.1.2 a ha b hb]; rfl

theorem derBounds_of : EmbLaws → PowInt → DecPow → LieBound → DerBounds := by
  intro hE hP hD hL C₀ hC₀
  refine ⟨100 + 50 * C₀, by positivity, ?_⟩
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ v₀ hv₀ g₀ hg₀ hgn X hX hX1
  obtain ⟨hmapH, hmul, hcont, hinv, hcol, hstab, hlie, hexp, hsnH, hsnL, hcolle, hUJ, hsub⟩ := hE n e ε ε' hpar.signs
  haveI : CompleteSpace H := hπ.1
  have hU : IsURepOn (UJset ε) π := hπ.2.2.1
  have hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Jm ε)) π := hU
  have hJ : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, rfl⟩
  have hn3 := hpar.three_le
  have hgap : GapAtLeast ε lam (1000 * (((n + 1 : ℕ)) : ℝ) ^ 3) := by push_cast; exact hpar.gap
  have hDe := hD (n + 1) ε lam B (by omega) hpar.hlam hgap hpar.bound.1 H π hπ v₀ hv₀
  obtain ⟨hsm0, hLw⟩ := hL (n + 1) ε lam B (by omega) hpar.hlam hgap hpar.bound.1 H π hπ v₀ hv₀
  push_cast at hDe hLw

  set m : ℝ := (n : ℝ) + 1 with hm
  have hm4 : 4 ≤ m := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  set R := hsn g₀ with hR
  set X' := embL e X with hX'def
  have hX' : X' ∈ lieOf (Jm ε) := hlie X hX
  have hX'n : hsn X' ≤ 1 := by rw [hX'def, hsnL]; exact hX1
  set v := π g₀ v₀ with hv
  have hsmv : SmV (lieOf (Jm ε)) π v := GlobalTheory.SmLinSub.rep_mem hJ hU' hsm0 hg₀
  set d1 := dR π X' v with hd1
  have hsm1 : SmV (lieOf (Jm ε)) π d1 := GlobalTheory.SmLinSub.dR_mem hJ hU' hsmv hX'
  set d2 := dR π X' d1 with hd2
  have hv1 : ‖v‖ = 1 := by rw [hv, hU.2.1 g₀ hg₀]; exact hv₀.1
  have hR1 : 1 ≤ R := (hUJ g₀ hg₀).1.trans (hcolle g₀)
  have hRi : hsn g₀⁻¹ = R := (hUJ g₀ hg₀).2
  have hB : 500 * m ^ 3 ≤ B := by
    obtain ⟨i, hi⟩ := hpar.neg
    have h1 := hpar.gap (e none) (e (some i)) (by rw [hpar.signs.1, hpar.signs.2 i, hi]; decide)
    have ha := hpar.bound.1 (e none)
    have hb := hpar.bound.1 (e (some i))
    have := abs_sub (lam (e none)) (lam (e (some i)))
    linarith
  have hB1 : 1 ≤ B := by
    have : (4 : ℝ) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by norm_num) hm4 3
    linarith
  have hLm : m + 3 ≤ 8 * m * B := by nlinarith
  have hM2 : ‖d2‖ ≤ ((8 * m * B) ^ 2 * R ^ 2) ^ 2 := by
    set X'' := g₀⁻¹ * X' * g₀ with hX''def
    have hX'' : X'' ∈ lieOf (Jm ε) := GlobalTheory.SmLinSub.conj_mem_lie hJ hg₀ hX'
    have e1 : d1 = π g₀ (dR π X'' v₀) := GlobalTheory.SmLinSub.dR_rep hJ hU' hsm0 hg₀ hX'
    have hsm0' := GlobalTheory.SmLinSub.dR_mem hJ hU' hsm0 hX''
    have e2 : d2 = π g₀ (dR π X'' (dR π X'' v₀)) := by
      rw [hd2, e1]; exact GlobalTheory.SmLinSub.dR_rep hJ hU' hsm0' hg₀ hX'
    have hb := hLw [X'', X''] (by simp [hX'']) (by simp)
    have hX''n : hsn X'' ≤ R ^ 2 := by
      have h1 := hsub (g₀⁻¹ * X') g₀
      have h2 := hsub g₀⁻¹ X'
      rw [hRi] at h2
      have h0 : 0 ≤ hsn X' := Real.sqrt_nonneg _
      have h0' : 0 ≤ R := Real.sqrt_nonneg _
      calc hsn X'' ≤ hsn (g₀⁻¹ * X') * R := h1
        _ ≤ R * hsn X' * R := by gcongr
        _ ≤ R * 1 * R := by gcongr
        _ = R ^ 2 := by ring
    rw [e2, hU.2.1 g₀ hg₀]
    simp only [List.foldr, List.map, List.prod_cons, List.prod_nil, mul_one] at hb
    have h0 : 0 ≤ hsn X'' := Real.sqrt_nonneg _
    calc _ ≤ _ := hb
      _ ≤ ((8 * m * B) ^ 2 * R ^ 2) * ((8 * m * B) ^ 2 * R ^ 2) := by gcongr
      _ = _ := by ring

  set M2 := ((8 * m * B) ^ 2 * R ^ 2) ^ 2 with hM2def
  set K0 := (Real.sqrt m + 3) * R ^ 2 with hK0
  have hK0p : 0 < K0 := by positivity
  set A := 20 * m ^ 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  set K1 := (2 + M2) * (Real.exp (50 * m ^ 3) * K0 ^ A) with hK1
  have hK1p : 0 ≤ K1 := by positivity
  have hpt : ∀ h : UJ ε', ‖⟪d1, π (embH e (umat h)) v⟫_ℂ‖ ≤ K1 * hsn (umat h) ^ (-A) := by
    intro h
    set b := embH e (umat h) with hbdef
    have hh : umat h ∈ UJset ε' := h.2
    have hb : b ∈ UJset ε := hmapH _ hh
    have hhpos : 0 < hsn (umat h) := hsn_pos (by omega) _ (Units.isUnit _)
    have hbn : hsn (umat h) ≤ hsn b := by
      have := hsnH (umat h)
      have h0 : 0 ≤ hsn b := Real.sqrt_nonneg _
      nlinarith
    have hbpos : 0 < hsn b := hhpos.trans_le hbn
    set E := Real.exp (50 * m ^ 3) * (hsn b / K0) ^ (-A) with hEdef
    have hE0 : 0 < E := by positivity
    have hcoef : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ‖ ≤ E ^ 2 := by
      intro t ht
      have ha : NormedSpace.exp (t • X') ∈ UJset ε := GlobalTheory.SmLinSub.exp_mem hX' t
      have ha' : NormedSpace.exp ((-t) • X') ∈ UJset ε := GlobalTheory.SmLinSub.exp_mem hX' (-t)
      have hst : (-t) • X' = t • -X' := by rw [neg_smul, smul_neg]
      have haa : NormedSpace.exp ((-t) • X') * NormedSpace.exp (t • X') = 1 := by
        rw [hst]; exact GlobalTheory.SmLinSub.expS_neg_mul X' t
      have haa' : NormedSpace.exp (t • X') * NormedSpace.exp ((-t) • X') = 1 := by
        rw [hst]; exact GlobalTheory.SmLinSub.expS_mul_neg X' t
      have hd := (Matrix.isUnit_iff_isUnit_det g₀).1 (GlobalTheory.SmLinSub.isUnit_of_mem hJ hg₀)
      have hgi := mem_inv hg₀
      have hc : NormedSpace.exp ((-t) • X') * b ∈ UJset ε := mem_mul ha' hb
      have hc'' : g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀ ∈ UJset ε := mem_mul (mem_mul hgi hc) hg₀
      have e1 : ⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ = ⟪v, π (NormedSpace.exp ((-t) • X') * b) v⟫_ℂ := by
        rw [← inner_rep hU ha' (π _ v) (π b v), ← rep_mul_apply hU ha' ha, haa, hU.1.1, ← rep_mul_apply hU ha' hb]
        rfl
      have e2 : ⟪v, π (NormedSpace.exp ((-t) • X') * b) v⟫_ℂ =
          ⟪v₀, π (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀) v₀⟫_ℂ := by
        rw [hv, ← inner_rep hU hgi (π g₀ v₀), ← rep_mul_apply hU hgi hg₀, nonsing_inv_mul _ hd, hU.1.1,
          ← rep_mul_apply hU hc hg₀, ← rep_mul_apply hU hgi (mem_mul hc hg₀), ← Matrix.mul_assoc]
        rfl
      have hsa : hsn (NormedSpace.exp (t • X')) ≤ Real.sqrt m + 3 := by
        have := hsn_exp_le X' t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hX'n
        push_cast at this
        exact this
      have hbc : hsn b ≤ K0 * hsn (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀) := by
        set c := NormedSpace.exp ((-t) • X') * b
        set c'' := g₀⁻¹ * c * g₀
        have eb : b = NormedSpace.exp (t • X') * (g₀ * c'' * g₀⁻¹) := by
          have : g₀ * c'' * g₀⁻¹ = c := by
            simp only [c'', ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]
            rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
          rw [this, ← Matrix.mul_assoc, haa', Matrix.one_mul]
        have h0 : 0 ≤ hsn c'' := Real.sqrt_nonneg _
        have h0a : 0 ≤ hsn (NormedSpace.exp (t • X')) := Real.sqrt_nonneg _
        have h0R : 0 ≤ R := Real.sqrt_nonneg _
        calc hsn b ≤ hsn (NormedSpace.exp (t • X')) * hsn (g₀ * c'' * g₀⁻¹) := by rw [eb]; exact hsub _ _
          _ ≤ hsn (NormedSpace.exp (t • X')) * (R * hsn c'' * R) := by
              gcongr
              calc hsn (g₀ * c'' * g₀⁻¹) ≤ hsn (g₀ * c'') * hsn g₀⁻¹ := hsub _ _
                _ ≤ R * hsn c'' * R := by rw [hRi]; gcongr; exact hsub _ _
          _ ≤ (Real.sqrt m + 3) * (R * hsn c'' * R) := by gcongr
          _ = K0 * hsn c'' := by rw [hK0]; ring
      have hlow : hsn b / K0 ≤ hsn (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀) := by
        rw [div_le_iff₀ hK0p]; linarith
      have hE2 : E ^ 2 = Real.exp (100 * m ^ 3) * (hsn b / K0) ^ (-(40 * m ^ 2)) := by
        rw [hEdef, mul_pow, sq (Real.exp _), ← Real.exp_add, sq ((hsn b / K0) ^ (-A)),
          ← Real.rpow_add (div_pos hbpos hK0p), hAdef]
        congr 2 <;> ring
      rw [e1, e2, hE2]
      refine (hDe _ hc'').trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (div_pos hbpos hK0p) hlow (neg_nonpos.2 (by positivity)))
        (Real.exp_pos _).le
    have hone : ∀ t : ℝ, ‖⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ‖ ≤ 1 := by
      intro t
      have ha := GlobalTheory.SmLinSub.exp_mem hX' t
      calc _ ≤ ‖π (NormedSpace.exp (t • X')) v‖ * ‖π b v‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [hU.2.1 _ ha, hU.2.1 _ hb, hv1]; norm_num
    have hτ0 : 0 < min 1 E := lt_min one_pos hE0
    have key := taylor_der (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) v, π b v⟫_ℂ)
      (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) d1, π b v⟫_ℂ) (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) d2, π b v⟫_ℂ)
      (min 1 E) M2 (fun t => coef_hasDerivAt hU hX' hsmv _ t) (fun t => coef_hasDerivAt hU hX' hsm1 _ t)
      (fun t ht => by
        rcases le_total 1 E with h1 | h1
        · rw [min_eq_left h1]; simpa using hone t
        · rw [min_eq_right h1]; exact hcoef t ht)
      (fun t ht => by
        have ha := GlobalTheory.SmLinSub.exp_mem hX' t
        calc _ ≤ ‖π (NormedSpace.exp (t • X')) d2‖ * ‖π b v‖ := norm_inner_le_norm _ _
          _ = ‖d2‖ := by rw [hU.2.1 _ ha, hU.2.1 _ hb, hv1, mul_one]
          _ ≤ M2 := hM2)
      hτ0 (min_le_left _ _)
    simp only [zero_smul, NormedSpace.exp_zero, hU.1.1, ContinuousLinearMap.one_apply] at key
    have hsplit : (hsn b / K0) ^ (-A) = K0 ^ A * hsn b ^ (-A) := by
      rw [Real.rpow_neg (div_nonneg hbpos.le hK0p.le), Real.div_rpow hbpos.le hK0p.le, inv_div, div_eq_mul_inv,
        ← Real.rpow_neg hbpos.le]
    have hmono : hsn b ^ (-A) ≤ hsn (umat h) ^ (-A) := Real.rpow_le_rpow_of_nonpos hhpos hbn (by linarith)
    have hM20 : 0 ≤ M2 := by positivity
    calc _ ≤ (2 + M2) * min 1 E := key
      _ ≤ (2 + M2) * E := by gcongr; exact min_le_right _ _
      _ = K1 * hsn b ^ (-A) := by rw [hEdef, hsplit, hK1]; ring
      _ ≤ K1 * hsn (umat h) ^ (-A) := by gcongr

  have hcontF : Continuous (fun h : UJ ε' => ⟪d1, π (embH e (umat h)) v⟫_ℂ) := by
    have hum : Continuous (fun h : UJ ε' => umat h) := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous (fun h : UJ ε' => π (embH e (umat h)) v) :=
      (hU.2.2 v).comp_continuous (hcont.comp hum) (fun h => hmapH _ h.2)
    exact continuous_const.inner h1
  have hAn : 4 * (n : ℝ) ^ 2 + 1 ≤ A := by rw [hAdef, hm]; nlinarith
  obtain ⟨hInt, hIle⟩ := hP n ε' A (by omega) hAn
  have hIntK : Integrable (fun h : UJ ε' => K1 * hsn (umat h) ^ (-A)) (muG ε') := hInt.const_mul K1
  refine ⟨hIntK.mono' hcontF.aestronglyMeasurable (ae_of_all _ hpt), ?_⟩
  have hvol : 0 ≤ (muG ε' (nbh ε' (1 / 4))).toReal := ENNReal.toReal_nonneg
  have hcst := const_le C₀ hC₀ m (8 * m * B) R hm4 hLm hR1 hgn
  have hmn : m - 1 = n := by rw [hm]; ring
  rw [hmn] at hcst
  calc ∫ h, ‖⟪d1, π (embH e (umat h)) v⟫_ℂ‖ ∂muG ε' ≤ ∫ h, K1 * hsn (umat h) ^ (-A) ∂muG ε' :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hIntK (ae_of_all _ hpt)
    _ = K1 * ∫ h, hsn (umat h) ^ (-A) ∂muG ε' := integral_const_mul _ _
    _ ≤ K1 * (Real.exp (10 * (n : ℝ) ^ 2) * (muG ε' (nbh ε' (1 / 4))).toReal) := by gcongr
    _ = (K1 * Real.exp (10 * (n : ℝ) ^ 2)) * (muG ε' (nbh ε' (1 / 4))).toReal := by ring
    _ ≤ big (100 + 50 * C₀) n B * (muG ε' (nbh ε' (1 / 4))).toReal := by
        gcongr
        rw [hK1, hM2def, hK0, hAdef]
        unfold big
        rw [← hm]
        exact hcst
    _ = _ := by ring

end GlobalTheory.SepReal.DerInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLaStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translateCoefficientDerivativeIntegralBounds_of_laws : EmbLaws → PowInt → DecPow → LieBound → DerBounds := by
  first | exact @GlobalTheory.SepReal.DerInt.derBounds_of | exact GlobalTheory.SepReal.DerInt.derBounds_of | (intros; apply GlobalTheory.SepReal.DerInt.derBounds_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLaws
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.IntBd

variable {m : ℕ} {ε : Fin m → Bool}

theorem isUnit_of_mem {x : Mat m} (hx : x ∈ UJset ε) : IsUnit x := by
  have hx' : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
  have h : (Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε) * x = 1 := by
    calc (Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε) * x = Formalism.REAL.Jm ε * (xᴴ * Formalism.REAL.Jm ε * x) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hx', Formalism.REAL.Jm_mul_self]
  exact (Matrix.isUnit_iff_isUnit_det x).2 (Matrix.isUnit_det_of_left_inverse h)

theorem exists_umat {x : Mat m} (hx : x ∈ UJset ε) : ∃ u : Formalism.REAL.UJ ε, umat u = x :=
  ⟨⟨(isUnit_of_mem hx).unit, hx⟩, rfl⟩

theorem mul_mem {x y : Mat m} (hx : x ∈ UJset ε) (hy : y ∈ UJset ε) : x * y ∈ UJset ε := by
  have hx' : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  show (x * y)ᴴ * Formalism.REAL.Jm ε * (x * y) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * Formalism.REAL.Jm ε * (x * y) = yᴴ * (xᴴ * Formalism.REAL.Jm ε * x) * y := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hx', hy']

theorem inv_facts {x : Mat m} (hx : x ∈ UJset ε) :
    x⁻¹ ∈ UJset ε ∧ x * x⁻¹ = 1 ∧ x⁻¹ * x = 1 ∧ x⁻¹⁻¹ = x := by
  have hd : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 (isUnit_of_mem hx)
  refine ⟨?_, Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_nonsing_inv _ hd⟩
  obtain ⟨u, rfl⟩ := exists_umat hx
  have hi : (umat u)⁻¹ = umat u⁻¹ := by simp [umat, Matrix.coe_units_inv]
  rw [hi]
  exact (u⁻¹).2

theorem hsn_nonneg (x : Mat m) : 0 ≤ hsn x := Real.sqrt_nonneg _

theorem hsn_pos (hm : 0 < m) {x : Mat m} (hx : x ∈ UJset ε) : 0 < hsn x := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hne : x ≠ 0 := (isUnit_of_mem hx).ne_zero
  obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  have h1 : ‖x i j‖ ^ 2 ≤ ∑ b, ‖x i b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ‖x i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ b, ‖x i b‖ ^ 2 ≤ ∑ a, ∑ b, ‖x a b‖ ^ 2 :=
    Finset.single_le_sum (f := fun a => ∑ b, ‖x a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h0 : 0 < ‖x i j‖ ^ 2 := pow_pos (norm_pos_iff.2 hij) 2
  unfold hsn
  exact Real.sqrt_pos.2 (by linarith)

theorem coef_conj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Mat m → (H →L[ℂ] H)}
    (hπ : IsURepOn (UJset ε) π) {g₀ g : Mat m} (hg₀ : g₀ ∈ UJset ε) (hg : g ∈ UJset ε) (v : H) :
    ⟪π g₀ v, π g (π g₀ v)⟫_ℂ = ⟪v, π (g₀⁻¹ * g * g₀) v⟫_ℂ := by
  obtain ⟨hi, hr, hl, -⟩ := inv_facts hg₀
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hπ
  have hw : ∀ w, π g₀ (π g₀⁻¹ w) = w := fun w => by
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hg₀ _ hi, hr, h1]; rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(π g₀ : H →ₗ[ℂ] H), fun x => hiso g₀ hg₀ x⟩
  have hL : ∀ x y, ⟪π g₀ x, π g₀ y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => L.inner_map_map x y
  rw [hmul _ (mul_mem hi hg) _ hg₀, hmul _ hi _ hg]
  conv_lhs => rw [← hw (π g (π g₀ v))]
  rw [hL]; rfl

theorem rpow_neg_anti {x y k : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hk : 0 ≤ k) : y ^ (-k) ≤ x ^ (-k) := by
  rw [Real.rpow_neg (hx.le.trans hxy), Real.rpow_neg hx.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx k) (Real.rpow_le_rpow hx.le hxy hk)

theorem decay_real {a y G k k2 : ℝ} (ha : 0 < a) (hy : 0 < y) (hG : 0 < G) (hya : y ≤ G ^ 2 * a) (hk : 0 ≤ k)
    (hk2 : k2 = 2 * k) : a ^ (-k) ≤ G ^ k2 * y ^ (-k) := by
  have hyG : y / G ^ 2 ≤ a := by rw [div_le_iff₀ (by positivity)]; linarith [mul_comm (G ^ 2) a]
  calc a ^ (-k) ≤ (y / G ^ 2) ^ (-k) := rpow_neg_anti (by positivity) hyG hk
    _ = (G ^ 2) ^ k * y ^ (-k) := by
      rw [div_eq_mul_inv, Real.mul_rpow hy.le (by positivity), Real.inv_rpow (by positivity),
        Real.rpow_neg (by positivity) (x := G ^ 2), inv_inv, mul_comm]
    _ = G ^ k2 * y ^ (-k) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hG.le, hk2]

theorem real_bound (n : ℕ) {x c s β : ℝ} (hc : 1 ≤ c) (hxc : c ≤ x) (hs : 0 < s) (hβ : 0 < β) (hsx : s ≤ β * x)
    (hβ2 : β ^ 2 ≤ (n : ℝ) + 1 + 2 * c ^ 2) :
    x ^ (-(40 * ((n : ℝ) + 1) ^ 2)) ≤
      (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * c ^ (-(2 * (n : ℝ) + 7)) * s ^ (-(4 * (n : ℝ) ^ 2 + 1)) := by
  set A : ℝ := 4 * (n : ℝ) ^ 2 + 1 with hA
  set R : ℝ := 40 * ((n : ℝ) + 1) ^ 2 - A with hR
  have hc0 : 0 < c := by linarith
  have hx0 : 0 < x := by linarith
  have hA0 : 0 ≤ A := by positivity
  have hR0 : 0 ≤ R := by rw [hR, hA]; nlinarith [sq_nonneg (n : ℝ)]
  have hsplit : x ^ (-(40 * ((n : ℝ) + 1) ^ 2)) = x ^ (-A) * x ^ (-R) := by
    rw [← Real.rpow_add hx0]; congr 1; rw [hR]; ring
  have h1 : x ^ (-A) ≤ s ^ (-A) * β ^ A := by
    have hsb : s / β ≤ x := by rw [div_le_iff₀ hβ]; linarith [mul_comm β x]
    calc x ^ (-A) ≤ (s / β) ^ (-A) := rpow_neg_anti (div_pos hs hβ) hsb hA0
      _ = s ^ (-A) * β ^ A := by
        rw [Real.div_rpow hs.le hβ.le, Real.rpow_neg hβ.le, div_inv_eq_mul]
  have h2 : x ^ (-R) ≤ c ^ (-R) := rpow_neg_anti hc0 hxc hR0
  have h3 : β ^ A ≤ (3 * ((n : ℝ) + 1)) ^ (A / 2) * c ^ A := by
    have e1 : β ^ A = (β ^ 2) ^ (A / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hβ.le]; congr 1; ring
    have e2 : c ^ A = (c ^ 2) ^ (A / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hc0.le]; congr 1; ring
    rw [e1, e2, ← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    have : 1 ≤ c ^ 2 := by nlinarith
    nlinarith
  have h4 : c ^ A * c ^ (-R) ≤ c ^ (-(2 * (n : ℝ) + 7)) := by
    rw [← Real.rpow_add hc0]
    apply Real.rpow_le_rpow_of_exponent_le hc
    rw [hR, hA]; nlinarith [sq_nonneg (n : ℝ)]
  have hsA : 0 ≤ s ^ (-A) := by positivity
  calc x ^ (-(40 * ((n : ℝ) + 1) ^ 2)) = x ^ (-A) * x ^ (-R) := hsplit
    _ ≤ (s ^ (-A) * β ^ A) * c ^ (-R) := by gcongr
    _ ≤ (s ^ (-A) * ((3 * ((n : ℝ) + 1)) ^ (A / 2) * c ^ A)) * c ^ (-R) := by gcongr
    _ = (3 * ((n : ℝ) + 1)) ^ (A / 2) * (c ^ A * c ^ (-R)) * s ^ (-A) := by ring
    _ ≤ (3 * ((n : ℝ) + 1)) ^ (A / 2) * c ^ (-(2 * (n : ℝ) + 7)) * s ^ (-A) := by gcongr

theorem const_bound (n : ℕ) {C₀ B G : ℝ} (hC₀ : 0 < C₀) (hB : 1 ≤ B) (hG1 : 1 ≤ G)
    (hG : G ≤ (8 * ((n : ℝ) + 1) * B) ^ (C₀ * ((n : ℝ) + 1))) :
    Real.exp (100 * ((n : ℝ) + 1) ^ 3) * G ^ (80 * ((n : ℝ) + 1) ^ 2) * (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) *
      Real.exp (10 * (n : ℝ) ^ 2) ≤ big (200 + 80 * C₀) n B := by
  unfold big
  set m : ℝ := (n : ℝ) + 1 with hmdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : 1 ≤ m := by rw [hmdef]; linarith
  set L := Real.log (8 * m * B) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have ha0 : 0 ≤ Real.log G := Real.log_nonneg hG1
  have haL : Real.log G ≤ C₀ * m * L := by
    calc Real.log G ≤ Real.log ((8 * m * B) ^ (C₀ * m)) := Real.log_le_log (by linarith) hG
      _ = C₀ * m * L := by rw [Real.log_rpow (by positivity)]
  have h3L : Real.log (3 * m) ≤ L := Real.log_le_log (by positivity) (by nlinarith)
  have h30 : 0 ≤ Real.log (3 * m) := Real.log_nonneg (by linarith)
  rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < G), Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 3 * m),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hm3 : m ^ 3 ≤ m ^ 4 := pow_le_pow_right₀ hm (by norm_num)
  have hm2 : m ^ 2 ≤ m ^ 4 := pow_le_pow_right₀ hm (by norm_num)
  have hm4L : m ^ 4 ≤ m ^ 4 * L := le_mul_of_one_le_right (by positivity) hL
  have t2 : Real.log G * (80 * m ^ 2) ≤ C₀ * m * L * (80 * m ^ 2) := mul_le_mul_of_nonneg_right haL (by positivity)
  have t2' : C₀ * L * m ^ 3 ≤ C₀ * L * m ^ 4 := mul_le_mul_of_nonneg_left hm3 (by positivity)
  have hA : (4 * (n : ℝ) ^ 2 + 1) / 2 ≤ 2 * m ^ 2 := by rw [hmdef]; nlinarith
  have t3 : Real.log (3 * m) * ((4 * (n : ℝ) ^ 2 + 1) / 2) ≤ L * (2 * m ^ 2) :=
    mul_le_mul h3L hA (by positivity) (by linarith)
  have t3' : L * m ^ 2 ≤ L * m ^ 4 := mul_le_mul_of_nonneg_left hm2 (by linarith)
  have hn2 : (n : ℝ) ^ 2 ≤ m ^ 2 := by rw [hmdef]; nlinarith
  nlinarith

end GlobalTheory.SepReal.IntBd

namespace GlobalTheory.SepReal


open GlobalTheory.SepReal.IntBd in
theorem intBounds_of (hE : EmbLaws) (hBo : Boost) (hP : PowInt) (hD : DecPow) : IntBounds := by
  intro C₀ hC₀
  refine ⟨200 + 80 * C₀, by positivity, ?_⟩
  intro n e ε lam ε' mu B hp H H' _ _ _ _ π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n
  obtain ⟨hEmb, hEmul, hEc, hEinv, hcol, -, -, -, hEsq, -, hcolle, hUJ, hsub⟩ := hE n e ε ε' hp.signs
  have hn3 := hp.three_le
  have hB1 : 1 ≤ B := by
    have h01 := hp.wide ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
    have b0 := abs_le.1 (hp.bound.1 ⟨0, by omega⟩)
    have b1 := abs_le.1 (hp.bound.1 ⟨1, by omega⟩)
    linarith
  have hURep := hπ.2.2.1
  have hone : ∀ x ∈ UJset ε, 1 ≤ hsn x := fun x hx => (hUJ x hx).1.trans (hcolle x)
  have hdec : ∀ X ∈ UJset ε, ‖⟪π g₀ v₀, π X (π g₀ v₀)⟫_ℂ‖ ≤
      Real.exp (100 * ((n : ℝ) + 1) ^ 3) * (hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) * hsn X ^ (-(40 * ((n : ℝ) + 1) ^ 2))) := by
    intro X hX
    obtain ⟨hi, hr, hl, -⟩ := inv_facts hg₀
    have hx : g₀⁻¹ * X * g₀ ∈ UJset ε := mul_mem (mul_mem hi hX) hg₀
    rw [coef_conj hURep hg₀ hX]
    have hd := hD (n + 1) ε lam B (by omega) hp.hlam (by have := hp.gap; push_cast; exact this) hp.bound.1 H π hπ v₀ hv₀ _ hx
    push_cast at hd
    refine hd.trans ?_
    gcongr
    have hX' : g₀ * (g₀⁻¹ * X * g₀) * g₀⁻¹ = X := by
      calc g₀ * (g₀⁻¹ * X * g₀) * g₀⁻¹ = (g₀ * g₀⁻¹) * X * (g₀ * g₀⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hr, Matrix.one_mul, Matrix.mul_one]
    have hle : hsn X ≤ hsn g₀ ^ 2 * hsn (g₀⁻¹ * X * g₀) := by
      calc hsn X = hsn (g₀ * (g₀⁻¹ * X * g₀) * g₀⁻¹) := by rw [hX']
        _ ≤ hsn (g₀ * (g₀⁻¹ * X * g₀)) * hsn g₀⁻¹ := hsub _ _
        _ ≤ (hsn g₀ * hsn (g₀⁻¹ * X * g₀)) * hsn g₀ := by
          rw [(hUJ g₀ hg₀).2]; exact mul_le_mul_of_nonneg_right (hsub _ _) (hsn_nonneg _)
        _ = hsn g₀ ^ 2 * hsn (g₀⁻¹ * X * g₀) := by ring
    exact decay_real (by linarith [hone _ hx]) (by linarith [hone _ hX]) (by linarith [hone _ hg₀]) hle (by positivity)
      (by ring)
  refine ⟨fun g hg => ?_, Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2), fun X hX => ?_⟩
  swap
  · refine (hdec X hX).trans ?_
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hsn_nonneg _) _))
    exact Real.rpow_le_rpow_of_exponent_le (hone X hX) (by nlinarith [sq_nonneg ((n : ℝ) + 1)])
  obtain ⟨hgi, hgr, hgl, hgii⟩ := inv_facts hg
  obtain ⟨h₁, hh₁, b, hb, hgb, hbn⟩ := hBo n e ε ε' hp.signs g⁻¹ hgi
  rw [hgii] at hbn
  obtain ⟨u₁, rfl⟩ := exists_umat hh₁
  obtain ⟨-, -, hl1, -⟩ := inv_facts hh₁
  have hb' : b = embH e (umat u₁)⁻¹ * g⁻¹ := by
    rw [hgb, ← Matrix.mul_assoc, ← hEmul, hl1, embH_one, Matrix.one_mul]
  have hbX : ∀ y : Mat n, b * (g * embH e y) = embH e ((umat u₁)⁻¹ * y) := by
    intro y
    rw [hb', hEmul]
    calc embH e (umat u₁)⁻¹ * g⁻¹ * (g * embH e y) = embH e (umat u₁)⁻¹ * (g⁻¹ * g) * embH e y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgl, Matrix.mul_one]
  have humul : ∀ y : Formalism.REAL.UJ ε', umat (u₁⁻¹ * y) = (umat u₁)⁻¹ * umat y := fun y => by
    simp [umat, Matrix.coe_units_inv]
  have hc1 : 1 ≤ colLen e g := (hUJ g hg).1
  have hβ1 : 1 ≤ hsn b := hone b hb
  obtain ⟨hPi, hPb⟩ := hP n ε' (4 * (n : ℝ) ^ 2 + 1) (by omega) le_rfl
  have hpt : ∀ y : Formalism.REAL.UJ ε', ‖⟪π g₀ v₀, π (g * embH e (umat y)) (π g₀ v₀)⟫_ℂ‖ ≤
      (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1)) := by
    intro y
    have hy : umat y ∈ UJset ε' := y.2
    have hX : g * embH e (umat y) ∈ UJset ε := mul_mem hg (hEmb _ hy)
    refine (hdec _ hX).trans ?_
    have hz : umat (u₁⁻¹ * y) ∈ UJset ε' := (u₁⁻¹ * y).2
    have e1 : hsn (embH e (umat (u₁⁻¹ * y))) ≤ hsn b * hsn (g * embH e (umat y)) := by
      rw [humul, ← hbX]; exact hsub _ _
    have e2 : hsn (umat (u₁⁻¹ * y)) ≤ hsn (embH e (umat (u₁⁻¹ * y))) := by
      have := hEsq (umat (u₁⁻¹ * y))
      nlinarith [hsn_nonneg (umat (u₁⁻¹ * y)), hsn_nonneg (embH e (umat (u₁⁻¹ * y)))]
    have hrb := real_bound n hc1 (by rw [← hcol g (umat y)]; exact hcolle _) (hsn_pos (by omega) hz)
      (by linarith : (0 : ℝ) < hsn b) (e2.trans e1) hbn
    calc Real.exp (100 * ((n : ℝ) + 1) ^ 3) * (hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
          hsn (g * embH e (umat y)) ^ (-(40 * ((n : ℝ) + 1) ^ 2)))
        ≤ Real.exp (100 * ((n : ℝ) + 1) ^ 3) * (hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
          ((3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7)) *
            hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrb (Real.rpow_nonneg (hsn_nonneg _) _)) (Real.exp_pos _).le
      _ = _ := by ring
  have hcont : Continuous (fun y : Formalism.REAL.UJ ε' => ⟪π g₀ v₀, π (g * embH e (umat y)) (π g₀ v₀)⟫_ℂ) := by
    have hcu : Continuous (fun y : Formalism.REAL.UJ ε' => umat y) := Units.continuous_val.comp continuous_subtype_val
    have hc1' : Continuous (fun y : Formalism.REAL.UJ ε' => g * embH e (umat y)) := continuous_const.mul (hEc.comp hcu)
    have hc2 : Continuous (fun y : Formalism.REAL.UJ ε' => π (g * embH e (umat y)) (π g₀ v₀)) :=
      (hURep.2.2 (π g₀ v₀)).comp_continuous hc1' (fun y => mul_mem hg (hEmb _ y.2))
    exact continuous_const.inner hc2
  have hDint : Integrable (fun y : Formalism.REAL.UJ ε' =>
      (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1))) (muG ε') :=
    (hPi.comp_mul_left u₁⁻¹).const_mul _
  have hfi := Integrable.mono' hDint hcont.aestronglyMeasurable (ae_of_all _ hpt)
  refine ⟨hfi, ?_⟩
  have hcb := const_bound n hC₀ hB1 (hone g₀ hg₀) hg₀n
  have hvol : 0 ≤ (muG ε' (nbh ε' (1 / 4))).toReal := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hsn_nonneg _) _)) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by linarith) _)
  have hcr : 0 ≤ colLen e g ^ (-(2 * (n : ℝ) + 7)) := Real.rpow_nonneg (by linarith) _
  calc ∫ y, ‖⟪π g₀ v₀, π (g * embH e (umat y)) (π g₀ v₀)⟫_ℂ‖ ∂muG ε'
      ≤ ∫ y, (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1)) ∂muG ε' := integral_mono hfi.norm hDint hpt
    _ = (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        ∫ y, hsn (umat y) ^ (-(4 * (n : ℝ) ^ 2 + 1)) ∂muG ε' := by
      rw [integral_const_mul, integral_mul_left_eq_self (fun y => hsn (umat y) ^ (-(4 * (n : ℝ) ^ 2 + 1))) u₁⁻¹]
    _ ≤ (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        (Real.exp (10 * (n : ℝ) ^ 2) * (muG ε' (nbh ε' (1 / 4))).toReal) :=
      mul_le_mul_of_nonneg_left hPb hK0
    _ = (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * Real.exp (10 * (n : ℝ) ^ 2)) *
        ((muG ε' (nbh ε' (1 / 4))).toReal * colLen e g ^ (-(2 * (n : ℝ) + 7))) := by ring
    _ ≤ big (200 + 80 * C₀) n B * ((muG ε' (nbh ε' (1 / 4))).toReal * colLen e g ^ (-(2 * (n : ℝ) + 7))) :=
      mul_le_mul_of_nonneg_right hcb (mul_nonneg hvol hcr)
    _ = _ := by ring

theorem intBounds_main : EmbLaws → Boost → PowInt → DecPow → IntBounds := intBounds_of

end GlobalTheory.SepReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLawsStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translateCoefficientIntegralBounds_of_unitary_laws : EmbLaws → Boost → PowInt → DecPow → IntBounds := by
  first | exact @GlobalTheory.SepReal.intBounds_main | exact GlobalTheory.SepReal.intBounds_main | (intros; apply GlobalTheory.SepReal.intBounds_main <;> assumption)
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.RealAsm

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isUnit_Jm' (ε : Fin m → Bool) : IsUnit (Jm ε) := by
  refine IsUnit.of_mul_eq_one (Jm ε) ?_
  simp only [Jm, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem umat_mem (ε : Fin m → Bool) (g : UJ ε) : umat g ∈ UJset ε := g.2

theorem one_mem (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := (1 : UJ ε).2

theorem continuous_umat (ε : Fin m → Bool) : Continuous (fun g : UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem smV_translate {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Mat m → (H →L[ℂ] H)} (hπ : IsDS ε lam π) {g : Mat m}
    (hg : g ∈ UJset ε) {v : H} (hv : SmV (lieOf (Jm ε)) π v) : SmV (lieOf (Jm ε)) π (π g v) :=
  GlobalTheory.SmLinSub.rep_mem (isUnit_Jm' ε) hπ.2.2.1 hv hg

theorem smV_const_smul {L : Set (Mat m)} {π : Mat m → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : SmV L π v) : SmV L π (a • v) :=
  fun k Xs hX => by simpa only [map_smul] using (hv k Xs hX).const_smul a

theorem integrable_low_coef (hD : DecPow) (hI : PowInt) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (B : ℝ) (hn : 3 ≤ n)
    (hl : IsHCParam lam) (hg : GapAtLeast ε lam (1000 * (n : ℝ) ^ 3)) (hB : ∀ a, |lam a| ≤ B)
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w) :
    Integrable (fun h : UJ ε => ⟪w, σ (umat h) w⟫_ℂ) (muG ε) := by
  have hdec := hD n ε lam B hn hl hg hB H σ hσ w hw
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hA : 4 * (n : ℝ) ^ 2 + 1 ≤ 40 * (n : ℝ) ^ 2 := by nlinarith
  have hpow := (hI n ε (40 * (n : ℝ) ^ 2) (by omega) hA).1
  refine (hpow.const_mul (Real.exp (100 * (n : ℝ) ^ 3))).mono' ?_ (Filter.Eventually.of_forall fun h => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.inner ((hσ.2.2.1.2.2 w).comp_continuous (continuous_umat ε) (umat_mem ε))
  · exact hdec _ (umat_mem ε h)

theorem big_mul (a b : ℝ) (n : ℕ) (B : ℝ) : big a n B * big b n B = big (a + b) n B := by
  unfold big
  rw [← Real.exp_add]
  ring_nf

theorem big_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : big a n B ≤ big b n B := by
  unfold big
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith)
  have h2 : 0 ≤ ((n : ℝ) + 1) ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_right hab h2
  exact mul_le_mul_of_nonneg_right this h1

theorem big_pos (a : ℝ) (n : ℕ) (B : ℝ) : 0 < big a n B := Real.exp_pos _

theorem one_le_B {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
    {mu : Fin n → ℝ} {B : ℝ} (hP : Par e ε lam ε' mu B) : 1 ≤ B := by
  have hn := hP.three_le
  have h := hP.wide ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h0 := abs_le.1 (hP.bound.1 ⟨0, by omega⟩)
  have h1 := abs_le.1 (hP.bound.1 ⟨1, by omega⟩)
  linarith [h0.1, h0.2, h1.1, h1.2]

theorem gap_mono {k : ℕ} {ε : Fin k → Bool} {lam : Fin k → ℝ} {a b : ℝ} (hab : a ≤ b) (h : GapAtLeast ε lam b) :
    GapAtLeast ε lam a := fun x y hxy => hab.trans (h x y hxy)

end GlobalTheory.SepReal.RealAsm

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.RealAsm

end GlobalTheory.SepReal

end
