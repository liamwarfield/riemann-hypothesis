module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrand

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumEqTsumOfKills
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumEqTsumOfKills
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem norm_trm_le (j : ℕ) (s : ℝ) (hj : j ≠ 0) (z : ℂ) : ‖trm j s z‖ ≤ ‖z‖ ^ (-((j : ℝ) + 2 * s)) := by
  by_cases hz : z = 0
  · subst hz
    simp only [trm, zero_pow hj, inv_zero, zero_mul, norm_zero]
    exact Real.rpow_nonneg le_rfl _
  · have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    unfold trm
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _),
      show -((j : ℝ) + 2 * s) = -(j : ℝ) + -2 * s by ring, Real.rpow_add h0, Real.rpow_neg h0.le,
      Real.rpow_natCast]

theorem lat_eq_tsum_of_kills : ∀ (j L : ℕ) (s : ℝ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖) ∧ lat j s L v Φ τ = ∑' x : ℤ × ℤ, Φ x * trm j s ((x.1 : ℂ) * τ + x.2) := by
  intro j L s v Φ τ hj hs hL hΦ hK
  have hk : (2 : ℝ) < j + 2 * s := by
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hG : Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖ := by
    have h1 := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
      ((EisensteinSeries.r τ) ^ (-((j : ℝ) + 2 * s)))
    have h2 : Summable (fun x : Fin 2 → ℤ => ‖trm j s ((x 0 : ℂ) * τ + x 1)‖) :=
      Summable.of_nonneg_of_le (fun x => norm_nonneg _)
        (fun x => (norm_trm_le j s (by omega) _).trans (EisensteinSeries.summand_bound τ (by linarith) x)) h1
    have h3 := ((finTwoArrowEquiv ℤ).symm.summable_iff).mpr h2
    exact h3.congr fun p => by simp
  obtain ⟨h1s, h1e⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L v Φ _ hL hΦ hK hG
  obtain ⟨_, h2e⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L v Φ _ hL hΦ hK h1s
  refine ⟨hG, ?_⟩
  unfold lat
  rw [h2e, h1e]

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumEqTsumOfKillsStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills : ∀ (j L : ℕ) (s : ℝ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖) ∧ lat j s L v Φ τ = ∑' x : ℤ × ℤ, Φ x * trm j s ((x.1 : ℂ) * τ + x.2) := by
  first | exact @GlobalTheory.EisM.lat_eq_tsum_of_kills | exact GlobalTheory.EisM.lat_eq_tsum_of_kills | (intros; apply GlobalTheory.EisM.lat_eq_tsum_of_kills <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCoprimeSumUnfoldToUnitStrip
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCoprimeSumUnfoldToUnitStrip
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem unfold_strip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  intro L ρ Ψ W hρ hΨ hΨm hW
  classical
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  haveI : Countable (Gamma0 L) := Subtype.countable
  have memΓ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L ↔ (L : ℤ) ∣ γ 1 0 := by
    intro γ
    rw [Gamma0_mem]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hs : MeasurableSet strip := by
    have : strip = (fun τ : ℍ => τ.re) ⁻¹' Set.Ico 0 1 := by
      ext τ; simp [strip]
    rw [this]
    exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico
  set f : ℍ → ℂ := strip.indicator Ψ with hf_def
  have hfi : Integrable f := (integrable_indicator_iff hs).2 hΨ
  have hfm : AEStronglyMeasurable f := hfi.aestronglyMeasurable
  have mp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun τ : ℍ => γ • τ) volume volume := fun γ =>
    measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have me : ∀ γ : SL(2, ℤ), MeasurableEmbedding (fun τ : ℍ => γ • τ) := fun γ =>
    (MeasurableEquiv.smul ((γ : GL (Fin 2) ℝ))).measurableEmbedding
  have rowEq : ∀ (γ : SL(2, ℤ)) (a b : ℤ), γ 1 0 = a → γ 1 1 = b → UpperTheory.V.Af.Rs.row γ = ![a, b] := by
    intro γ a b ha hb
    funext i
    fin_cases i
    · simpa [UpperTheory.V.Af.Rs.row] using ha
    · simpa [UpperTheory.V.Af.Rs.row] using hb
  have step1 : ∀ τ : ℍ, ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ =
      ∑' γ : Gamma0 L, f ((γ : SL(2, ℤ)) • τ) := by
    intro τ
    have key : ∀ x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, ∃ γ : Gamma0 L,
        ((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1) = x.1 ∧ (γ : SL(2, ℤ)) • τ ∈ strip := by
      intro x
      obtain ⟨γ, ⟨hr, hst⟩, -⟩ := UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩
      have h0 : γ 1 0 = x.1.1 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 0
      have h1 : γ 1 1 = x.1.2 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 1
      refine ⟨⟨γ, (memΓ γ).2 (h0 ▸ x.2.2)⟩, ?_, hst⟩
      simp [h0, h1]
    choose g hg using key
    have ginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← (hg x).1, ← (hg y).1, hxy]
    have hsupp : Function.support (fun γ : Gamma0 L => f ((γ : SL(2, ℤ)) • τ)) ⊆ Set.range g := by
      intro γ hγ
      have hin : (γ : SL(2, ℤ)) • τ ∈ strip := by
        by_contra h
        exact hγ (Set.indicator_of_notMem h _)
      have hL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := (memΓ γ).1 γ.2
      have hcop : IsCoprime ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := UpperTheory.V.Af.Rs.rowBij.1 γ
      refine ⟨⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩, ?_⟩
      set x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1} := ⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩
      have hx := hg x
      apply Subtype.ext
      exact (UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩).unique
        ⟨rowEq _ _ _ (congrArg Prod.fst hx.1) (congrArg Prod.snd hx.1), hx.2⟩ ⟨rowEq _ _ _ rfl rfl, hin⟩
    rw [← ginj.tsum_eq hsupp]
    refine tsum_congr fun x => ?_
    have hx := hg x
    have hL : (L : ℤ) ∣ (g x : SL(2, ℤ)) 1 0 := (memΓ _).1 (g x).2
    rw [hf_def, Set.indicator_of_mem hx.2, hW _ hL τ, hx.1]
  have hsum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ))⁻¹ • τ)) 1 := fun τ => by
    have := (Equiv.inv (Gamma0 L)).hasSum_iff.mpr (hρ.sum τ)
    simpa [Function.comp_def] using this
  set F : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ τ : ℂ) * f ((γ : SL(2, ℤ)) • τ) with hF
  set G : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℂ) * f τ with hG
  have hFG : ∀ γ, F γ = fun τ => G γ ((γ : SL(2, ℤ)) • τ) := by
    intro γ; funext τ; simp [hF, hG]
  have Gm : ∀ γ, AEStronglyMeasurable (G γ) := fun γ =>
    ((Complex.measurable_ofReal.comp (hρ.meas.comp (me ((γ : SL(2, ℤ))⁻¹)).measurable)).aestronglyMeasurable).mul hfm
  have Fm : ∀ γ, AEStronglyMeasurable (F γ) := fun γ => by
    rw [hFG γ]
    exact (Gm γ).comp_measurePreserving (mp γ)
  have tot : ∀ τ, ∑' γ : Gamma0 L, ‖G γ τ‖ₑ = ‖f τ‖ₑ := by
    intro τ
    simp only [hG, enorm_mul]
    rw [ENNReal.tsum_mul_right]
    have : ∑' γ : Gamma0 L, ‖((ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℝ) : ℂ)‖ₑ = 1 := by
      simp_rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hρ.nonneg _)]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => hρ.nonneg _) (hsum τ).summable, (hsum τ).tsum_eq,
        ENNReal.ofReal_one]
    rw [this, one_mul]
  have finG : ∑' γ, ∫⁻ τ, ‖G γ τ‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun γ => (Gm γ).enorm)]
    simp_rw [tot]
    exact hfi.hasFiniteIntegral.ne
  have finF : ∑' γ, ∫⁻ τ, ‖F γ τ‖ₑ ≠ ⊤ := by
    have : ∀ γ, ∫⁻ τ, ‖F γ τ‖ₑ = ∫⁻ τ, ‖G γ τ‖ₑ := fun γ => by
      rw [hFG γ]
      exact (mp γ).lintegral_comp_emb (me γ) (fun τ => ‖G γ τ‖ₑ)
    simp_rw [this]
    exact finG
  calc ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ
        = ∫ τ, ∑' γ, F γ τ := by
          congr 1; funext τ; rw [step1 τ, ← tsum_mul_left]
    _ = ∑' γ, ∫ τ, F γ τ := integral_tsum Fm finF
    _ = ∑' γ, ∫ τ, G γ τ := by
          refine tsum_congr fun γ => ?_
          rw [hFG γ]
          exact (mp γ).integral_comp (me γ) (G γ)
    _ = ∫ τ, ∑' γ, G γ τ := (integral_tsum Gm finG).symm
    _ = ∫ τ, f τ := by
          congr 1; funext τ
          simp only [hG]
          rw [tsum_mul_right, ← Complex.ofReal_tsum, (hsum τ).tsum_eq]
          simp
    _ = ∫ τ in strip, Ψ τ := integral_indicator hs

end GlobalTheory.EisM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCoprimeSumUnfoldToUnitStripStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coprime_sum_unfold_to_unitStrip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  first | exact @GlobalTheory.EisM.unfold_strip | exact GlobalTheory.EisM.unfold_strip | (intros; apply GlobalTheory.EisM.unfold_strip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeries
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem im_ofComplex_pt (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  simp [UpperHalfPlane.im]

theorem strip_eq_LSeries : ∀ (h b : ℕ → ℂ) (w : ℝ), 0 < w → PolyB h → PolyB b → h 0 = 0 →
    LSeriesSummable (fun n => conj (h n) * b n) w →
    IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) strip →
    ∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ) =
      ((Real.Gamma w / (4 * π) ^ w : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) w := by
  intro h b w hw hh hb h0 hL hint
  set a : ℕ → ℂ := fun n => conj (h n) * b n with ha
  set P : ℝ → ℂ := fun y => ∫ x in (0 : ℝ)..1,
    conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I)) with hPd
  have h4 : (0 : ℝ) < 4 * π := by positivity
  have ha0 : a 0 = 0 := by simp [ha, h0]
  have h1 : (∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) = mellin P (w : ℂ) := by
    rw [GlobalTheory.T.unitStrip_integral_eq_iterated.2 _ hint]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy : 0 < y := hy
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp only [im_ofComplex_pt _ _ hy, hPd, smul_eq_mul]
    rw [intervalIntegral.integral_mul_const]
    have e : ((y : ℂ) ^ ((w : ℂ) - 1)) = ((y ^ (w + 1) : ℝ) : ℂ) / (y : ℂ) ^ 2 := by
      have e1 : (w : ℂ) - 1 = ((w - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e1, ← Complex.ofReal_cpow hy.le]
      have e2 : y ^ (w - 1) = y ^ (w + 1) / y ^ 2 := by
        have : w - 1 = (w + 1) - ((2 : ℕ) : ℝ) := by push_cast; ring
        rw [this, Real.rpow_sub hy, Real.rpow_natCast]
      rw [e2]; push_cast; ring
    rw [e]; ring
  have hsum : Summable fun n : ℕ => ‖a n‖ / (4 * π * n) ^ ((w : ℂ).re) := by
    have hs2 := (hL.norm).div_const ((4 * π) ^ w)
    refine hs2.congr (fun n => ?_)
    rw [LSeries.norm_term_eq, Complex.ofReal_re]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · rw [if_neg hn.ne', Real.mul_rpow h4.le (Nat.cast_nonneg n), div_div, mul_comm ((n : ℝ) ^ w)]
  have h2 := hasSum_mellin (a := a) (p := fun n : ℕ => 4 * π * n) (F := P) (s := (w : ℂ))
    (fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · left; exact ha0
      · right; positivity)
    (by simpa using hw)
    (fun y hy => by
      have := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line h b y hh hb hy
      refine this.congr_fun (fun n => ?_)
      simp only [ha]
      congr 2
      ring_nf)
    hsum
  rw [h1, ← h2.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  rw [LSeries.term_of_ne_zero hn.ne', ← Complex.ofReal_cpow (by positivity), Real.mul_rpow h4.le (Nat.cast_nonneg n),
    Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.Gamma_ofReal]
  push_cast
  field_simp

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeriesStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries : ∀ (h b : ℕ → ℂ) (w : ℝ), 0 < w → PolyB h → PolyB b → h 0 = 0 → LSeriesSummable (fun n => conj (h n) * b n) w → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) strip → ∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ) = ((Real.Gamma w / (4 * π) ^ w : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) w := by
  first | exact @GlobalTheory.EisM.strip_eq_LSeries | exact GlobalTheory.EisM.strip_eq_LSeries | (intros; apply GlobalTheory.EisM.strip_eq_LSeries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOut
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOut
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.GcdOut

abbrev CopVec (L : ℕ) : Type := {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}

def scl (L : ℕ) (p : ℕ+ × CopVec L) : ℤ × ℤ := (((p.1 : ℕ) : ℤ) * p.2.1.1, ((p.1 : ℕ) : ℤ) * p.2.1.2)

lemma scl_injective (L : ℕ) : Function.Injective (scl L) := by
  rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩ ⟨δ', ⟨⟨a', b'⟩, hab', ha'⟩⟩ h
  simp only [scl, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have g1 : Int.gcd a b = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab
  have g2 : Int.gcd a' b' = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab'
  have hd : (δ : ℕ) = (δ' : ℕ) := by
    have e1 := Int.gcd_mul_left ((δ : ℕ) : ℤ) a b
    have e2 := Int.gcd_mul_left ((δ' : ℕ) : ℤ) a' b'
    rw [h1, h2, e2, g1, g2] at e1
    simpa using e1.symm
  have hδ : δ = δ' := PNat.coe_injective hd
  subst hδ
  have hne : ((δ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast δ.ne_zero
  have := mul_left_cancel₀ hne h1
  have := mul_left_cancel₀ hne h2
  subst_vars
  rfl

lemma trm_zero (j : ℕ) (s : ℝ) (hj : 2 ≤ j) : trm j s 0 = 0 := by
  simp [trm, zero_pow (by omega : j ≠ 0)]

lemma trm_smul (j : ℕ) (s : ℝ) (δ : ℕ) (z : ℂ) :
    trm j s ((δ : ℂ) * z) = (((δ : ℂ) ^ j)⁻¹ * ((((δ : ℝ) ^ (2 * s))⁻¹ : ℝ) : ℂ)) * trm j s z := by
  unfold trm
  rw [norm_mul, Complex.norm_natCast, Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _), neg_mul,
    Real.rpow_neg (Nat.cast_nonneg _), ← neg_mul, mul_pow, mul_inv]
  push_cast
  ring

lemma cpow_split (j : ℕ) (s : ℝ) (δ : ℕ) (hδ : 0 < δ) :
    (δ : ℂ) ^ ((j : ℂ) + 2 * (s : ℂ)) = (δ : ℂ) ^ j * ((((δ : ℝ) ^ (2 * s)) : ℝ) : ℂ) := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hδ.ne'), Complex.cpow_natCast,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.EisM.GcdOut

open GlobalTheory.EisM.GcdOut in
theorem GlobalTheory.EisM.lattice_sum_gcd_out (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ)
    (hj : 2 ≤ j) (hs : 0 < s) (hL : 0 < L) :
    ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) =
      LSeries (fun n => φ n) (j + 2 * s) *
        ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1},
          φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  let F : ℤ × ℤ → ℂ := fun x => latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2)
  let f : ℕ+ → ℂ := fun δ => LSeries.term (fun n => φ n) ((j : ℂ) + 2 * (s : ℂ)) (δ : ℕ)
  let g : CopVec L → ℂ := fun x => φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2)
  change ∑' x, F x = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) * ∑' x, g x
  have hsumT := (GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills j L s 0 0 τ hj hs hL ⟨0, by simp⟩ (fun x => by simp [Kills])).1
  have hgs : Summable fun x => ‖g x‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      (hsumT.comp_injective Subtype.val_injective)
    simp only [g, Function.comp, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hLS : LSeriesSummable (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    rw [DirichletCharacter.LSeriesSummable_iff hL.ne']
    have : (2:ℝ) ≤ j := by exact_mod_cast hj
    simp
    linarith
  have hfs : Summable fun δ => ‖f δ‖ :=
    (summable_norm_iff.2 hLS).comp_injective PNat.coe_injective
  have hterm : ∀ p : ℕ+ × CopVec L, F (scl L p) = f p.1 * g p.2 := by
    rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩
    have hδ : 0 < (δ : ℕ) := δ.pos
    simp only [F, f, g, scl, latF]
    rw [if_pos (dvd_mul_of_dvd_right ha _), LSeries.term_of_ne_zero hδ.ne', cpow_split j s _ hδ]
    have e : ((((δ : ℕ) : ℤ) * a : ℤ) : ℂ) * (τ : ℂ) + ((((δ : ℕ) : ℤ) * b : ℤ) : ℂ)
        = ((δ : ℕ) : ℂ) * ((a : ℂ) * τ + b) := by push_cast; ring
    rw [e, trm_smul]
    have e2 : (((((δ : ℕ) : ℤ) * b : ℤ)) : ZMod L) = ((δ : ℕ) : ZMod L) * (b : ZMod L) := by push_cast; ring
    rw [e2, map_mul]
    have h1 : ((δ:ℕ) : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hδ.ne')
    have h2 : ((((δ : ℕ) : ℝ) ^ (2 * s) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hδ) _).ne'
    push_cast
    field_simp
  have hsupp : Function.support F ⊆ Set.range (scl L) := by
    rintro ⟨x1, x2⟩ hx
    simp only [Function.mem_support, F, latF] at hx
    by_cases hL1 : (L : ℤ) ∣ x1
    swap
    · simp [hL1] at hx
    rw [if_pos hL1, one_mul] at hx
    have hφ : φ (x2 : ZMod L) ≠ 0 := left_ne_zero_of_mul hx
    have ht : trm j s ((x1 : ℂ) * τ + x2) ≠ 0 := right_ne_zero_of_mul hx
    have hgpos : 0 < Int.gcd x1 x2 := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [trm_zero j s hj] at ht
    obtain ⟨a, b, hab, h1, h2⟩ := Int.exists_gcd_one hgpos
    generalize Int.gcd x1 x2 = d at h1 h2 hgpos
    have hunit : IsUnit (x2 : ZMod L) := by
      by_contra h
      exact hφ (MulChar.map_nonunit φ h)
    have hdu : IsUnit ((d : ℕ) : ZMod L) := by
      rw [h2] at hunit
      push_cast at hunit
      exact isUnit_of_mul_isUnit_right hunit
    have hcop : Nat.Coprime d L := (ZMod.isUnit_iff_coprime d L).1 hdu
    have hLa : (L : ℤ) ∣ a := by
      have hc : IsCoprime (L : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
      rw [h1] at hL1
      exact hc.dvd_of_dvd_mul_right hL1
    refine ⟨(⟨d, hgpos⟩, ⟨(a, b), Int.isCoprime_iff_gcd_eq_one.2 hab, hLa⟩), ?_⟩
    simp only [scl, PNat.mk_coe]
    rw [h1, h2, mul_comm a, mul_comm b]
  have hLser : ∑' δ : ℕ+, f δ = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    unfold LSeries
    refine (PNat.coe_injective.tsum_eq (f := LSeries.term (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ))) ?_)
    intro n hn
    have : n ≠ 0 := by
      rintro rfl
      exact hn (LSeries.term_zero _ _)
    exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩
  calc ∑' x, F x = ∑' p, F (scl L p) := ((scl_injective L).tsum_eq hsupp).symm
    _ = ∑' p : ℕ+ × CopVec L, f p.1 * g p.2 := tsum_congr hterm
    _ = (∑' δ, f δ) * ∑' x, g x := (tsum_mul_tsum_of_summable_norm hfs hgs).symm
    _ = _ := by rw [hLser]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOutStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out : ∀ (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) = LSeries (fun n => φ n) (j + 2 * s) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  first | exact @GlobalTheory.EisM.lattice_sum_gcd_out | exact GlobalTheory.EisM.lattice_sum_gcd_out | (intros; apply GlobalTheory.EisM.lattice_sum_gcd_out <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinUnfoldingPeterssonEisensteinLatticeSum
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM

def rkPsi (k : ℕ) (s : ℝ) (h b : ℕ → ℂ) (τ : ℍ) : ℂ :=
  conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)

theorem rankin_transf (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ)
    (h b : ℕ → ℂ) (s : ℝ) (hNL : N ∣ L) (hh : CF (2 * e + 1) L (ch ε) h) (hb : MF e L χ b)
    (hχ : ∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    rkPsi (2 * e + 1) s h b (γ • τ) =
      φ ((γ 1 1 : ℤ) : ZMod L) * trm (e + 1) s (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * rkPsi (2 * e + 1) s h b τ := by
  set j : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hjdef
  have hdenom : UpperHalfPlane.denom γ τ = j := ModularGroup.denom_apply γ τ
  have hj : j ≠ 0 := by rw [← hdenom]; exact UpperHalfPlane.denom_ne_zero _ τ
  have him : (γ • τ).im = τ.im / Complex.normSq j := by rw [ModularGroup.im_smul_eq_div_normSq, hdenom]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨m, hm⟩ := hγ
  have hcop : IsCoprime (γ 1 1) (L : ℤ) := ⟨γ 0 0, -(γ 0 1 * m), by rw [hm] at hdet; linear_combination hdet⟩
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    obtain ⟨n, hn⟩ := hNL
    have h1 : ((γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) : ℤ) : ZMod N) = 1 := by
      rw [hm, hn] at hdet; push_cast at hdet
      have : γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) = 1 := by linear_combination hdet
      rw [this]; simp
    push_cast at h1; simp only [mul_neg, neg_mul, ZMod.natCast_self, mul_zero, neg_zero, add_zero] at h1
    exact ⟨⟨_, ((γ 0 0 : ℤ) : ZMod N), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hεε : conj (ch ε (γ 1 1)) * ch ε (γ 1 1) = 1 := by
    have hn : ‖ch ε (γ 1 1)‖ = 1 := by
      unfold ch; rw [← hunit.unit_spec]; exact DirichletCharacter.unit_norm_eq_one ε hunit.unit
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hH := hh.1.2 γ ⟨m, hm⟩ τ
  have hB := hb.2 γ ⟨m, hm⟩ τ
  rw [hχ _ hcop] at hB
  rw [← hjdef] at hH hB
  have hNpos : 0 < Complex.normSq j := Complex.normSq_pos.2 hj
  have hy := τ.im_pos
  unfold rkPsi trm
  rw [hH, hB, him, Real.div_rpow hy.le hNpos.le, Real.rpow_add hNpos, Real.rpow_natCast]
  have hn2 : ‖j‖ ^ (-2 * s) = (Complex.normSq j ^ s)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    congr 1; push_cast; ring
  rw [hn2]
  have hP : (Complex.normSq j ^ s) ≠ 0 := (Real.rpow_pos_of_pos hNpos s).ne'
  have hcj : conj j ≠ 0 := by simpa using hj
  have hNc : ((Complex.normSq j : ℝ) : ℂ) = j * conj j := (Complex.mul_conj j).symm
  simp only [ch] at hεε ⊢
  have hε0 : ε ((γ 1 1 : ℤ) : ZMod N) ≠ 0 := by intro h0; rw [h0, mul_zero] at hεε; exact zero_ne_one hεε
  have hεc : conj (ε ((γ 1 1 : ℤ) : ZMod N)) = (ε ((γ 1 1 : ℤ) : ZMod N))⁻¹ := eq_inv_of_mul_eq_one_left hεε
  push_cast
  rw [hNc]
  simp only [map_mul, map_pow, hεc]
  field_simp
  ring_nf

theorem latF_kills (L : ℕ) (φ : DirichletCharacter ℂ L) (hφ : φ ≠ 1) :
    Kills L (0, 1) (latF L (fun _ => 1) φ) := by
  intro x
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have h0 : ∑ z : ZMod (n + 1), φ z = 0 := MulChar.sum_eq_zero_of_ne_one hφ
  unfold latF
  have e1 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).1 = x.1 := by intro r; simp
  by_cases hx : ((n + 1 : ℕ) : ℤ) ∣ x.1
  · have e2 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).2 = x.2 - r := by intro r; simp
    simp only [e1, e2, hx, if_true, one_mul]
    rw [← h0]
    refine Finset.sum_nbij' (fun r : ℕ => (((x.2 - r : ℤ)) : ZMod (n + 1)))
      (fun z => ((x.2 : ZMod (n + 1)) - z).val) (fun _ _ => Finset.mem_univ _)
      (fun z _ => Finset.mem_range.2 (ZMod.val_lt _)) ?_ ?_ (fun _ _ => rfl)
    · intro r hr
      have hr' : r < n + 1 := Finset.mem_range.1 hr
      simp [ZMod.val_cast_of_lt hr']
    · intro z _
      simp
  · simp only [e1, hx, if_false, Finset.sum_const_zero]

theorem rankin_summ (e : ℕ) (h b : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (hs : 0 < s)
    (hb : ∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1))
    (hh : Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s)) :
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) ∧
      LSeriesSummable (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := hb
  have hb2 : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((GlobalTheory.T.summable_card_divisors_sq_div_one_add_rpow s hs).mul_left (C ^ 2))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : (2 * (e : ℝ) - 1 + s) ≠ 0 := by
        have : (1 : ℝ) ≤ e := by exact_mod_cast he
        linarith
      simp [Real.zero_rpow this]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have key : (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) = ((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hn0]
      congr 1; push_cast [Nat.cast_sub he]; ring
    have hA : 0 < (n : ℝ) ^ (e - 1) := by positivity
    have hB : 0 < (n : ℝ) ^ (1 + s) := Real.rpow_pos_of_pos hn0 _
    have hle := hC n hn.ne'
    rw [key, div_le_iff₀ (by positivity)]
    calc ‖b n‖ ^ 2 ≤ (C * n.divisors.card * (n : ℝ) ^ (e - 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C ^ 2 * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + s)) * (((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s)) := by
        field_simp
  refine ⟨hb2, ?_⟩
  unfold LSeriesSummable
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((hh.add hb2).div_const 2))
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [Complex.ofReal_re, norm_mul, Complex.norm_conj]
  have e1 : (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n * n := by
    rw [← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']; congr 1; push_cast; ring
  have e2 : (n : ℝ) ^ (2 * (e : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n := by
    rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
  rw [e1, e2]
  have hu : 0 < (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := Real.rpow_pos_of_pos hn0 _
  set u := (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)
  set A := ‖h n‖
  set B := ‖b n‖
  have : (A ^ 2 / (u * n * n) + B ^ 2 / u) / 2 - A * B / (u * n) = (A - B * n) ^ 2 / (2 * u * n ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ (A - B * n) ^ 2 / (2 * u * n ^ 2) := by positivity
  linarith

theorem rankin_unfold : ∀ (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → 0 < L → N ∣ L → Wt L ρ → φ ≠ 1 → CF (2 * e + 1) L (ch ε) h → MF e L χ b → (∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) → (∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1)) → pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) = LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) * (((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
  intro e L N ε φ χ ρ h b s he hs hL hNL hρ hφ hh hb hχ hbC
  have hcont := fun a (ha : PolyB a) => (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).2
  set Lφ := LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) with hLφ
  have hlat : ∀ τ : ℍ, lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ = Lφ *
      ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm (e + 1) s ((x.1.1 : ℂ) * τ + x.1.2) := by
    intro τ
    have hb1 : ∃ C : ℝ, ∀ x, ‖latF L (fun _ => 1) φ x‖ ≤ C := ⟨1, fun x => by
      unfold latF; split_ifs <;> simp [DirichletCharacter.norm_le_one]⟩
    rw [(GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills (e + 1) L s (0, 1) _ τ (by omega) hs hL hb1 (latF_kills L φ hφ)).2]
    exact GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out (e + 1) L s φ τ (by omega) hs hL
  set Ψ := rkPsi (2 * e + 1) s h b with hΨ
  set W : ℤ × ℤ → ℍ → ℂ := fun x τ => φ (x.2 : ZMod L) * trm (e + 1) s ((x.1 : ℂ) * τ + x.2) * Ψ τ with hW
  have hpt : ∀ τ : ℍ, (ρ τ : ℂ) * (conj (qs h τ) * (qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) * (τ.im : ℂ) ^ (2 * e + 1)) =
      Lφ * ((ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ) := by
    intro τ
    rw [hlat τ]
    simp only [hW]
    rw [tsum_mul_right]
    have hy : ((τ.im ^ (((2 * e + 1 : ℕ) : ℝ) + s) : ℝ) : ℂ) = (τ.im : ℂ) ^ (2 * e + 1) * ((τ.im ^ s : ℝ) : ℂ) := by
      rw [Real.rpow_add τ.im_pos, Real.rpow_natCast]; push_cast; ring
    simp only [hΨ, rkPsi, hy]
    ring
  have hmsq := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) L (ch ε) h (by omega) hh
  obtain ⟨hbsq, hLS⟩ := rankin_summ e h b s he hs hbC (by simpa using hmsq.2.2.1 s hs)
  have hint : IntegrableOn Ψ strip := by
    exact GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand (2 * e + 1) e L N ε h b s rfl he hs hL hNL hh hb.1 hbsq
  have hmeas : AEStronglyMeasurable Ψ := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hΨ, rkPsi]
    refine ((Complex.continuous_conj.comp (hcont h hh.1.1)).mul (hcont b hb.1)).mul (Complex.continuous_ofReal.comp ?_)
    exact (UpperHalfPlane.continuous_im).rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hunf := GlobalTheory.T.integral_coprime_sum_unfold_to_unitStrip L ρ Ψ W hρ hint hmeas (fun γ hγ τ => by
    simpa [hW] using rankin_transf e L N ε φ χ h b s hNL hh hb hχ γ hγ τ)
  have hmel := GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries h b (2 * (e : ℝ) + s) (by positivity) hh.1.1 hb.1 hmsq.1 hLS
  have hΨeq : (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((2 * (e : ℝ) + s) + 1) : ℝ) : ℂ)) = Ψ := by
    funext τ; simp only [hΨ, rkPsi]; congr 3; push_cast; ring
  rw [hΨeq] at hmel
  unfold pet
  simp_rw [hpt]
  rw [integral_const_mul, hunf, hmel hint]

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinUnfoldingPeterssonEisensteinLatticeSumStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum : ∀ (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → 0 < L → N ∣ L → Wt L ρ → φ ≠ 1 → CF (2 * e + 1) L (ch ε) h → MF e L χ b → (∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) → (∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1)) → pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) = LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) * (((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.EisM.rankin_unfold | exact GlobalTheory.EisM.rankin_unfold | (intros; apply GlobalTheory.EisM.rankin_unfold <;> assumption)
end
