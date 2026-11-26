module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberMulLeadingMinorLeTwoPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeNormalFormStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBound
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegSide

variable {k r : ℕ}

theorem measurableSet_GG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  simpa [Set.compl_setOf] using (WUnfold.measurableSet_not_GG (k := k) (r := r)).compl

theorem measurable_indicator_GG {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Zero β]
    {f : Mat k r → β} (hf : ContinuousOn f (GG k r)) :
    Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => f (Matrix.of x)) := by
  classical
  have h : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} := hf
  have := h.measurable_piecewise (g := fun _ => (0 : β)) continuousOn_const measurableSet_GG
  rwa [← Set.piecewise_eq_indicator]

theorem measurable_mulP : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := by
  have : Continuous fun p : Mat k r × Mat k r => p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
  have h : Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := this
  exact h.measurable

theorem measurable_conjM (h : Mat k r) : Measurable (conjM h : Mt k r → Mt k r) := by
  have : Continuous fun x : Mat k r => h * x * h⁻¹ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h' : Continuous (conjM h : Mt k r → Mt k r) := this
  exact h'.measurable

theorem null_of_fibres {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN ν : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muProd μW μN) ν)
    {A : Set (Mt k r)} (hA : MeasurableSet A) (h0 : ∀ g : Mat k r, μN (rmulM g ⁻¹' A) = 0) : μG A = 0 := by
  haveI := hN.1
  have hconj : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN :=
    (GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW μN hz hT hW hN).2.2.2.2
  have hm : Measurable (A.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, hq _ hm]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  have hx : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  show ∫⁻ s, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) ∂(muProd μW μN) = 0
  unfold muProd
  rw [lintegral_map hx measurable_mulP, lintegral_prod (fun p : Mt k r × Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of p.1) p.2)))
      (hx.comp measurable_mulP).aemeasurable]
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := hW.2.2.1
  refine (lintegral_congr_ae (haeW.mono fun h hh => ?_)).trans lintegral_zero
  have hg : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  have e : ∀ n : Mt k r, rmulM (Matrix.of x) (lmulM (Matrix.of h) n) =
      rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
    intro n
    show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
      Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
    rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n : Mat k r),
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hh.1)]
  show ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of h) n)) ∂μN = 0
  simp only [e]
  rw [← lintegral_map hg (measurable_conjM _), hconj _ hh, ← h0 (Matrix.of h * Matrix.of x),
    ← lintegral_indicator_one ((continuous_rmulM _).measurable hA)]
  rfl

theorem mem_Sset_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {s x : Mat k r}
    (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : Sg2 k r z (s * x) = Sg2 k r z x := by
  have := (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.1 x hx s hs 1 ⟨isClosedSub_GG.2.2.1, one_mem _⟩
  rwa [Matrix.mul_one] at this

theorem tail {Wq : Type} [NormedAddCommGroup Wq] {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {ν : Measure (Mt k r)} {Φ : Mat k r → Wq} {q : ℕ} {H₁ : ℝ} (hH : 1 ≤ H₁) (ht : TailBd z ν Φ q H₁) (i : ℕ)
    {Q : Set (Mt k r)} (hQ : MeasurableSet Q) (hsub : ∀ x ∈ Q, i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z (Matrix.of x)) :
    ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤
      ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG ν Φ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine (setLIntegral_le_lintegral _ _).trans (le_mul_of_one_le_left zero_le ?_)
    rw [ENNReal.one_le_ofReal]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one]
    linarith
  · have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have h := ht (2 ^ i) h2
    have e : 2 * (2 * r + 2 : ℝ) * (2 ^ i : ℝ) ^ (-(2 * (q : ℝ))) = (4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹ := by
      rw [Real.rpow_neg h2.le, ← Real.rpow_natCast (2 ^ i : ℝ) (2 * q)]
      push_cast
      ring
    rw [e] at h
    refine le_trans ?_ h
    rw [← lintegral_indicator hQ]
    refine lintegral_mono (Set.indicator_le_indicator_of_subset (fun x hx => ?_) fun _ => zero_le)
    have hx' := (hsub x hx).resolve_left hi.ne'
    have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    rcases ((GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.2.2 (Matrix.of x)).2.2.2 with h' | ⟨a, ha⟩
    · exfalso
      rw [h'] at hx'
      nlinarith
    · exact ⟨a, ha ▸ hx'.le⟩

theorem side_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  intro k r j hj z z' Wq _ _ _ π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hjk hκ hs hH hO ht hDe hNR hqR
  have hO' := hO
  obtain ⟨hz', hT', hnt, hπ, -, hG, hW, -, hN, hqS, hψ, hΦ, hΦc, hc, hl2⟩ := hO'
  have hz := hNR.1
  have hT := hNR.2.2.1
  obtain ⟨hγ, hRc, hRh, hRu, -⟩ := GlobalTheory.T.stabilizer_measure_normalisation_symm k r j hj z z' γ s μR hs hNR
  obtain ⟨hoff, hnull, φ, hφ, hcut⟩ := GlobalTheory.T.cutoff_computes_besselQuotientIntegral k r _ μG μR νR hRc hG hRh hRu hqR
  have hV := GlobalTheory.T.fibreVolume_normalFormStabiliser k r j hj z z' γ De s μR hj1 hjk hDe hs hNR
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' γ hz hz' hT hT' hγ
  have hYi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x :=
    fun ρ hρ x hx => (GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' γ hz hz' hγ x hx).2.2 ρ hρ
  have hmul : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := isClosedSub_GG.2.2.2.1
  refine ⟨?_, fun w hw i R₀ y hR hy => ?_⟩
  · set A : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) = 0} with hAdef
    have hA : MeasurableSet A := by
      have := measurableSet_GG.inter (hYm (measurableSet_singleton 0))
      convert this using 1
      ext x
      refine and_congr_right fun hx => ?_
      rw [Set.mem_preimage, Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
      rfl
    have hA0 : μG A = 0 := by
      refine null_of_fibres hz' hT' hW hN hqS hA fun g => ?_
      by_cases hg : g ∈ GG k r
      · rw [Measure.smul_apply, measure_mono_null (s := rmulM g ⁻¹' A) (t := {n | Yj k r hj z z' γ (Matrix.of n * g) = 0}) (fun n hn => hn.2)
          (hV g hg).1, smul_zero]
      · refine measure_mono_null (t := {x | Matrix.of x ∉ Nset k r}) (fun n hn hn' => hg ?_) hN.2.2.1
        exact (WUnfold.mul_mem_GG_iff hn'.1).1 hn.1
    have hA1 : νR A = 0 := by
      refine hnull A hA (fun ρ hρ x hx => ?_) hA0
      show (ρ * Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (ρ * Matrix.of x) = 0) ↔ (_ ∧ _)
      rw [hYi ρ hρ _ hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hoff hA1)
    by_cases hx' : Matrix.of x ∈ GG k r
    · exact Or.inr ⟨hx', hx.resolve_left (not_not.2 hx')⟩
    · exact Or.inl hx'
  · set E := Eset0 k r hj z z' γ R₀ y with hE
    set Q : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x))} with hQdef
    have hQ : MeasurableSet Q := by
      have h1 := measurable_indicator_GG (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' hz' hT').2.2.1
      have h2 := measurableSet_GG.inter ((MeasurableSet.const (i = 0)).union (measurableSet_lt
        (measurable_const (a := 2 ^ i * H₁)) h1))
      convert h2 using 1
      ext x
      refine and_congr_right fun hx => ?_
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rw [Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
    have hEQ : E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)} = E ∩ Q := by
      ext x
      exact and_congr_right fun hx => ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩
    have hQi : ∀ s ∈ Sset k r z', ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q) := by
      intro s hs x hx
      show (s * Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (s * Matrix.of x))) ↔ (_ ∧ _)
      rw [Sg2_left hz' hT' hs hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ (WUnfold.Sset_subset _ hs) _ hx, h.2⟩⟩
    have hEi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ E ↔ x ∈ E) := by
      intro ρ hρ x hx
      show (ρ * Matrix.of x ∈ GG k r ∧ Sg2 k r z' (ρ * Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * (ρ * Matrix.of x)) ≤ R₀ ∧
        y < Yj k r hj z z' γ (ρ * Matrix.of x) ∧ Yj k r hj z z' γ (ρ * Matrix.of x) ≤ 2 * y) ↔ (_ ∧ _)
      have e : γ * (ρ * Matrix.of x) = γ * ρ * γ⁻¹ * (γ * Matrix.of x) := by
        rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hγ), Matrix.mul_assoc]
      rw [hYi ρ hρ _ hx, Sg2_left hz' hT' (mem_Sset_of_mem_Nset _ hρ.1) hx, e,
        Sg2_left hz hT (mem_Sset_of_mem_Nset _ hρ.2) (hmul _ hγ _ hx)]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    set g : Mt k r → ℝ≥0∞ := fun x => (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 with hg
    have hgi : ∀ ρ ∈ Nset k r, ∀ x, Matrix.of x ∈ GG k r → g (lmulM ρ x) = g x := by
      intro ρ hρ x hx
      have h1 := hΦ 1 (isClosedSub_UWset z').2.2.1 ρ hρ _ hx
      rw [Matrix.one_mul, hπ.1.1] at h1
      have h2 : ‖ψ' ρ‖₊ = 1 := NNReal.eq (hψ ρ hρ)
      show (‖⟪w, Φ' (ρ * Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 = _
      rw [h1, inner_smul_right, nnnorm_mul, h2, one_mul]
      rfl
    have hFm : Measurable ((E ∩ Q).indicator g) := by
      have h1 : ContinuousOn (fun x : Mat k r => (‖⟪w, Φ' x⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) (GG k r) :=
        (ENNReal.continuous_pow 2).comp_continuousOn
          (ENNReal.continuous_coe.comp_continuousOn (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const hΦc).nnnorm)
      have h2 := (measurable_indicator_GG h1).indicator ((hEm R₀ y).inter hQ)
      rwa [Set.indicator_indicator, (Set.inter_eq_left (t := {x : Mt k r | Matrix.of x ∈ GG k r})).2
        (fun x (hx : x ∈ E ∩ Q) => hx.2.1)] at h2
    have hFi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r →
        (E ∩ Q).indicator g (lmulM ρ x) = (E ∩ Q).indicator g x := by
      intro ρ hρ x hx
      have hiff : lmulM ρ x ∈ E ∩ Q ↔ x ∈ E ∩ Q :=
        and_congr (hEi ρ hρ x hx) (hQi ρ (mem_Sset_of_mem_Nset _ hρ.1) x hx)
      by_cases h : x ∈ E ∩ Q
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h), hgi ρ hρ.1 x hx]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.1 h)]
    have hP := GlobalTheory.T.amplitude_one_side_unfolding k r z' π' ψ' μG μW' _ νS' Φ' c hO (fun x => φ x * E.indicator 1 x) Q
      (ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s))
      (hφ.1.mul (measurable_one.indicator (hEm R₀ y))) hQ hQi (fun g hg => by
        rw [lintegral_smul_measure, smul_eq_mul]
        exact mul_le_mul_right ((hV g hg).2 φ hφ R₀ y hR hy) _) w hw
    have hTl := tail hz' hT' hH ht i (Q := Q) hQ fun x hx => hx.2
    have hfib : 0 ≤ fibVol0 k r j R₀ De y := by
      have := hDe.1
      unfold fibVol0
      positivity
    have hd : (0 : ℝ) < Module.finrank ℂ Wq := Nat.cast_pos.2 Module.finrank_pos
    calc ∫⁻ x in E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)},
          ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR
        = ∫⁻ x, (E ∩ Q).indicator g x ∂νR := by
          rw [hEQ, lintegral_indicator ((hEm R₀ y).inter hQ)]
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          rfl
      _ = ∫⁻ x in Q, φ x * E.indicator 1 x * g x ∂μG := by
          rw [hcut _ hFm hFi, ← lintegral_indicator hQ]
          refine lintegral_congr fun x => ?_
          by_cases h1 : x ∈ E <;> by_cases h2 : x ∈ Q <;> simp [h1, h2]
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s) * (Module.finrank ℂ Wq : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS' Φ') :=
          hP.trans (mul_le_mul_right hTl _)
      _ = _ := by
          rw [hl2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hκ.le,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp

end GlobalTheory.Amp.DegSide
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationDegenerateSidePieceBoundStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplification_degenerate_side_piece_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  first | exact @GlobalTheory.Amp.DegSide.side_bound | exact GlobalTheory.Amp.DegSide.side_bound | (intros; apply GlobalTheory.Amp.DegSide.side_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsGramNumberLeMajorantLengths
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsGramNumberLeMajorantLengths
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.MinorBound

open GlobalTheory.PlueckerBound GlobalTheory.Amp.GramFlag

theorem norm_det_inner_le_pow {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : ℕ} (u v : Fin l → E)
    (s t : Matrix (Fin l) (Fin l) ℂ) (hs : s.det = 1) (ht : t.det = 1) {R R' : ℝ}
    (hu : ∀ a, ‖∑ i, s i a • u i‖ ≤ R) (hv : ∀ a, ‖∑ i, t i a • v i‖ ≤ R') :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ R ^ l * R' ^ l := by
  have h := norm_det_inner_le (fun a => ∑ i, s i a • u i) (fun a => ∑ i, t i a • v i)
  rw [det_inner_sum_smul, ht, mul_one] at h
  have e : (Matrix.of fun a a' => ⟪∑ i, s i a • u i, v a'⟫_ℂ) = sᴴ * Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ := by
    ext a a'
    simp [Matrix.mul_apply, sum_inner, inner_smul_left, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_conjTranspose, hs, star_one, one_mul] at h
  have h1 : ∀ {f : Fin l → E} {S : ℝ}, (∀ a, ‖f a‖ ≤ S) → ∏ a, ‖f a‖ ≤ S ^ l := fun {f S} hf => by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (fun a _ => norm_nonneg (f a)) (fun a _ => hf a)
    simpa using this
  have h0 : ∀ f : Fin l → E, 0 ≤ ∏ a, ‖f a‖ := fun f => Finset.prod_nonneg fun a _ => norm_nonneg _
  exact h.trans (mul_le_mul (h1 hu) (h1 hv) (h0 _) ((h0 _).trans (h1 hu)))

theorem exists_short (k r : ℕ) {l : ℕ} (hl : l ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r) :
    ∃ t : Matrix (Fin l) (Fin l) ℂ, t.det = 1 ∧
      ∀ a, eucl (∑ b, t b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b)))) ≤ Sg k r z x := by
  obtain ⟨u, hu, -⟩ := gramSchmidt_lengths k r z x hx
  refine ⟨(upper u).submatrix (Fin.castLE hl) (Fin.castLE hl), ?_, fun a => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · simp [upper]
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ a < b := not_lt.2 hab'.le
      simp [upper, h1, hab'.ne']
  · have e : ∑ b, (upper u).submatrix (Fin.castLE hl) (Fin.castLE hl) b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b))) =
        ∑ b, upper u b (Fin.castLE hl a) • (x⁻¹ *ᵥ bvec (eI k r b)) := by
      refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun b => rfl)
      intro b hb
      have hb' : l ≤ b.val := by
        by_contra h
        exact hb ⟨⟨b.val, by omega⟩, rfl⟩
      have ha := a.isLt
      have h1 : ¬ b < Fin.castLE hl a := by
        rw [Fin.lt_def, Fin.val_castLE]; omega
      have h2 : b ≠ Fin.castLE hl a := fun h => by
        rw [h, Fin.val_castLE] at hb'; omega
      simp [upper, h1, h2]
    rw [e, (hu _).1]
    exact (Finset.le_fold_max _).2 (Or.inr ⟨_, Finset.mem_univ _, le_rfl⟩)

theorem eucl_Hpk (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : eucl (Hpk k r *ᵥ v) = eucl v := by
  rw [eucl_eq, eucl_eq, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp, Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, (hpkFacts k r).1, (hpkFacts k r).2.1, Matrix.one_mulVec, dotProduct_comm]

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem one_le_Sg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : 1 ≤ Sg k r z x :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem norm_Dmin_le (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {γ x : Mat k r} (hγ : γ ∈ GG k r) (hx : x ∈ GG k r)
    (l : Fin (r + 1)) : ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ hH
  have hγx := hmul γ hγ x hx
  have hl : l.val ≤ r := Nat.le_of_lt_succ l.isLt
  obtain ⟨s, hs, hs'⟩ := exists_short k r hl z hγx
  obtain ⟨t, ht, ht'⟩ := exists_short k r hl z' hx
  have h := norm_det_inner_le_pow (E := EuclideanSpace ℂ (Fin (2 * r + k + 1)))
    (fun a => WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))
    (fun a => WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))) s t hs ht
    (R := Sg k r z (γ * x)) (R' := Sg k r z' x)
    (fun a => by
      have := hs' a
      rwa [eucl_eq, WithLp.toLp_sum] at this)
    (fun a => by
      have := ht' a
      rw [← eucl_Hpk, eucl_eq, Matrix.mulVec_sum, WithLp.toLp_sum] at this
      simpa only [Matrix.mulVec_smul, WithLp.toLp_smul] using this)
  have e : Dmin k r z z' γ l.castSucc = (Matrix.of fun a a' : Fin l.val =>
      ⟪(WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))) : EuclideanSpace ℂ (Fin (2 * r + k + 1))),
        WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a'))))⟫_ℂ).det := by
    unfold Dmin
    congr 1
    ext a b
    have ha : a.val < r := lt_of_lt_of_le a.isLt hl
    have hb : b.val < r := lt_of_lt_of_le b.isLt hl
    rw [Matrix.of_apply, EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.submatrix_apply]
    dsimp only [Formalism.QuantumDeterminants.Zhat]
    rw [← herm_mulVec (hinv _ hγx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (hinv _ hγ).1, Matrix.mul_one, fvec, fvec, dite_eq_left (by exact hb), dite_eq_left (by exact ha)]
    rfl
  rw [e]
  refine h.trans ?_
  rw [← mul_pow, mul_comm]
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_Sg ..) (one_le_Sg ..)) hl

theorem gramProj_le (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1)))) :
    gramProj P (fun a : Fin j => x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) ≤ Sg k r z x ^ r := by
  obtain ⟨s, hs, hs'⟩ := exists_short k r hj z hx
  have h1 : ∀ a, ‖∑ i, s i a • P.starProjection (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj i))))‖ ≤
      Sg k r z x := fun a => by
    have := hs' a
    rw [eucl_eq, WithLp.toLp_sum] at this
    refine le_trans (le_of_eq ?_) ((P.norm_starProjection_apply_le _).trans this)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, WithLp.toLp_smul, map_smul]
  have h := norm_det_inner_le_pow _ _ s s hs hs h1 h1
  have h0 := one_le_Sg k r z x
  refine le_trans ?_ (pow_le_pow_right₀ h0 hj)
  unfold gramProj
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [sq]
  exact h

theorem minor_gram_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ l : Fin (r + 1), ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r) ∧ 0 ≤ Yj k r hj z z' γ x ∧ Yj k r hj z z' γ x ≤ Sg k r z (γ * x) ^ r / Dj k r hj z z' γ ∧ ∀ H₁ : ℝ, 1 ≤ H₁ → sgV k r z z' γ H₁ ≤ max 1 ((Sg k r z' x * Sg k r z (γ * x)) ^ r / (2 * H₁) ^ (2 * r)) := by
  intro k r j hj z z' γ _ _ hγ x hx
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hγx := (uHGroup _ _ hH).2.1 γ hγ x hx
  refine ⟨norm_Dmin_le k r z z' hγ hx, div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_, fun H₁ hH₁ => ?_⟩
  · refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    have := gramProj_le k r hj z hγx (Ppos k r z z' γ x)
    simpa only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec] using this
  · refine (Finset.fold_max_le _).2 ⟨le_max_left _ _, fun l _ => le_max_of_le_right ?_⟩
    exact div_le_div_of_nonneg_right (norm_Dmin_le k r z z' hγ hx l) (by positivity)

end GlobalTheory.Amp.MinorBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsGramNumberLeMajorantLengthsStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ l : Fin (r + 1), ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r) ∧ 0 ≤ Yj k r hj z z' γ x ∧ Yj k r hj z z' γ x ≤ Sg k r z (γ * x) ^ r / Dj k r hj z z' γ ∧ ∀ H₁ : ℝ, 1 ≤ H₁ → sgV k r z z' γ H₁ ≤ max 1 ((Sg k r z' x * Sg k r z (γ * x)) ^ r / (2 * H₁) ^ (2 * r)) := by
  first | exact @GlobalTheory.Amp.MinorBound.minor_gram_bound | exact GlobalTheory.Amp.MinorBound.minor_gram_bound | (intros; apply GlobalTheory.Amp.MinorBound.minor_gram_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DyadicSummationWithDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DyadicSummationWithDecay
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem dyad_cauchySchwarz {X : Type} [MeasurableSpace X] (μ : Measure X) (A B : X → ℝ)
    (hA : Measurable A) (hB : Measurable B) (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (h1 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ ≤ ENNReal.ofReal (P ^ 2))
    (h2 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ ≤ ENNReal.ofReal (Q ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ ≤ ENNReal.ofReal (P * Q) := by
  have hc : 0 < Q / (2 * P) := by positivity
  have hd : 0 < P / (2 * Q) := by positivity
  have hpt : ∀ x, ENNReal.ofReal (A x * B x) ≤
      ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (A x ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (B x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : Q / (2 * P) * A x ^ 2 + P / (2 * Q) * B x ^ 2 - A x * B x
        = (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by
      field_simp; ring
    have h0 : 0 ≤ (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by positivity
    linarith
  have mA : Measurable fun x => ENNReal.ofReal (A x ^ 2) := by fun_prop
  have mB : Measurable fun x => ENNReal.ofReal (B x ^ 2) := by fun_prop
  calc _ ≤ _ := lintegral_mono hpt
    _ = ENNReal.ofReal (Q / (2 * P)) * ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ
        + ENNReal.ofReal (P / (2 * Q)) * ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ := by
      rw [lintegral_add_left (mA.const_mul _), lintegral_const_mul _ mA, lintegral_const_mul _ mB]
    _ ≤ ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (P ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (Q ^ 2) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp; ring

theorem dyad_exists_shell (H s : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H ∧ (i = 0 ∨ 2 ^ i * H < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hH] at hn
    have : (0:ℝ) < 2 ^ n * H := by positivity
    rw [pow_succ]; linarith
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := k) (by omega)
    exact not_le.mp this

theorem dyad_exists_down (M y : ℝ) (hy : 0 < y) (hM : y ≤ M) :
    ∃ a : ℕ, M / 2 ^ (a + 1) < y ∧ y ≤ 2 * (M / 2 ^ (a + 1)) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := M / y) (y := 2)
    (by rw [le_div_iff₀ hy]; linarith) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hy] at h2; linarith
  · rw [le_div_iff₀ hy] at h1
    have : 2 * (M / 2 ^ (n + 1)) = M / 2 ^ n := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]; linarith

theorem dyad_piece_real (r k e n : ℕ) (H De N sg u v w : ℝ) (hr : 1 ≤ r) (hH : 0 < H)
    (hDe : 0 < De) (hN : 0 < N) (hsg : 1 ≤ sg) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hwN : w ≤ N) (hwM : w ≤ ((u * (2 * H)) ^ r * De) ^ 2 * v)
    (hNR : 1 ≤ N * (u * (2 * H)) ^ (2 * r)) (hsu : sg ≤ u ^ r) :
    (u * (2 * H)) ^ e * w ^ (k + 1) * (u ^ (e + 4 * r + 1 + n))⁻¹ ≤
      (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * sg ^ (-((n : ℝ) / r)) * (u⁻¹ * v) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have h1 : (u ^ n)⁻¹ ≤ sg ^ (-((n : ℝ) / r)) := by
    rw [Real.rpow_neg (by linarith)]
    apply inv_anti₀ (by positivity)
    calc sg ^ ((n : ℝ) / r) ≤ (u ^ r) ^ ((n : ℝ) / r) := by gcongr
      _ = u ^ n := by
        rw [← Real.rpow_natCast u r, ← Real.rpow_mul hu.le, ← Real.rpow_natCast u n]
        congr 1; field_simp
  have h2 : w ^ (k + 1) ≤ N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v := by
    calc w ^ (k + 1) = w ^ k * w * 1 := by ring
      _ ≤ N ^ k * (((u * (2 * H)) ^ r * De) ^ 2 * v) * (N * (u * (2 * H)) ^ (2 * r)) := by
        gcongr
      _ = _ := by ring
  calc _ ≤ (u * (2 * H)) ^ e * (N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v)
        * (u ^ (e + 4 * r + 1 + n))⁻¹ := by gcongr
    _ = (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * (u ^ n)⁻¹ * (u⁻¹ * v) := by
      rw [mul_pow u, mul_pow u]
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem dyad_tsum_four (c : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, c * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = 16 * c := by
  have g : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
    rw [ENNReal.tsum_geometric]; simp
  rw [ENNReal.tsum_mul_left]
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, g]
  ring

theorem dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  intro X _ ν A B S S' Y Y' r j kk e q H₁ De D K K' sg hA hB _ _ _ _ hr hkk hq hH hDe hD hK hK'
    hsg hae h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, kk = k + 1 := ⟨kk - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = e + 4 * r + 1 + n := ⟨q - (e + 4 * r + 1), by omega⟩
  have hexp : ((e + 4 * r + 1 + n : ℕ) : ℝ) - e - 4 * r - 1 = n := by push_cast; ring
  rw [hexp]
  have hH0 : 0 < H₁ := by linarith
  have hDe0 : 0 < De := by linarith
  set C : ℝ := Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
    * sg ^ (-((n : ℝ) / r))) with hC
  have hC0 : 0 ≤ C := by positivity
  let M : ℕ → ℕ → ℝ := fun i i' => (2 ^ (i + i' + 1) * H₁) ^ r * De
  have hM0 : ∀ i i', 0 < M i i' := fun i i' => by positivity
  let P : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x |
    (0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) ∧
    (S x ≤ 2 ^ (p.1 + 1) * H₁ ∧ (p.1 = 0 ∨ 2 ^ p.1 * H₁ < S x)) ∧
    (S' x ≤ 2 ^ (p.2.1 + 1) * H₁ ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H₁ < S' x)) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, P p := by
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := dyad_exists_shell H₁ (S x) hH0
    obtain ⟨i', hi'⟩ := dyad_exists_shell H₁ (S' x) hH0
    have hmax : max (S x) (S' x) ^ r * De ≤ M i i' := by
      have a1 : (2:ℝ) ^ (i + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a2 : (2:ℝ) ^ (i' + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a3 : max (S x) (S' x) ≤ 2 ^ (i + i' + 1) * H₁ :=
        max_le (hi.1.trans (by gcongr)) (hi'.1.trans (by gcongr))
      have a4 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith [hx.2.2.1])
      show _ ≤ (2 ^ (i + i' + 1) * H₁) ^ r * De
      gcongr
    obtain ⟨a, ha⟩ := dyad_exists_down (M i i') (Y x) hx.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.1.trans hmax)
    obtain ⟨b, hb⟩ := dyad_exists_down (M i i') (Y' x) hx.2.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.2.1.trans hmax)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b), hx, hi, hi', ha, hb⟩
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in P p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (P (i, i', a, b)).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]; simp
    obtain ⟨⟨-, -, s1, s2, y1, y2, g1, g2, -, -, g3⟩, ⟨b1, -⟩, ⟨b2, -⟩, ⟨c1, -⟩, ⟨c2, -⟩⟩ := hx
    simp only at b1 b2 c1 c2 ⊢
    have hm := hM0 i i'
    set y : ℝ := M i i' / 2 ^ (a + 1) with hy
    set y' : ℝ := M i i' / 2 ^ (b + 1) with hy'
    have hy0 : 0 < y := by positivity
    have hy0' : 0 < y' := by positivity
    set R : ℝ := 2 ^ (i + i' + 1) * H₁ with hR
    have hR0 : 0 < R := by positivity
    set q := e + 4 * r + 1 + n with hqdef
    have i1 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (A x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K * Real.sqrt (R ^ e) * y ^ (k + 1) * (((2:ℝ) ^ i) ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h1 i i' y hy0).trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.1.1, hz.2.1.2, hz.2.2.1.1, hz.2.2.2.1.1, hz.2.2.2.1.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y, ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    have i2 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (B x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K' * Real.sqrt (R ^ e) * y' ^ (k + 1) * (((2:ℝ) ^ i') ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h2 i i' y' hy0').trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.2.1.1, hz.2.2.1.2, hz.2.1.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK'.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y', ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    refine (dyad_cauchySchwarz _ A B hA hB _ _ (by positivity) (by positivity) i1 i2).trans ?_
    have hrhs : ENNReal.ofReal C * (2⁻¹ ^ i * (2⁻¹ ^ i' * (2⁻¹ ^ a * 2⁻¹ ^ b))) =
        ENNReal.ofReal (C * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
      have e2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ : ℝ) := by
        rw [ENNReal.ofReal_inv_of_pos two_pos]; simp
      rw [ENNReal.ofReal_mul hC0, e2]
      congr 1
      simp only [← ENNReal.ofReal_pow (show (0:ℝ) ≤ 2⁻¹ by norm_num)]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_add, pow_add]; simp only [inv_pow]; field_simp
    rw [hrhs]
    apply ENNReal.ofReal_le_ofReal
    have hRu : R = 2 ^ (i + i') * (2 * H₁) := by rw [hR]; ring
    have hu1 : (1:ℝ) ≤ 2 ^ (i + i') := one_le_pow₀ one_le_two
    have hSS : S x * S' x ≤ 2 ^ (i + i') * (2 * H₁) ^ 2 := by
      calc S x * S' x ≤ (2 ^ (i + 1) * H₁) * (2 ^ (i' + 1) * H₁) := by
            apply mul_le_mul b1 b2 (by linarith) (by positivity)
        _ = _ := by ring
    have hSS0 : 0 ≤ S x * S' x := mul_nonneg (by linarith) (by linarith)
    have hSSr : (S x * S' x) ^ r ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := by
      rw [pow_mul, ← mul_pow]; gcongr
    have key := dyad_piece_real r k e n H₁ De (2 ^ j / D) sg (2 ^ (i + i')) ((2 ^ (a + b))⁻¹)
      (y * y') hr hH0 hDe0 (by positivity) hsg (by positivity) (by positivity) (by positivity)
      (by
        rw [le_div_iff₀ hD]
        refine le_trans ?_ g1
        gcongr)
      (by
        rw [← hRu]
        have : y * y' = (R ^ r * De) ^ 2 * (2 ^ (a + b))⁻¹ / 4 := by
          rw [hy, hy']
          show (R ^ r * De) / _ * ((R ^ r * De) / _) = _
          field_simp; ring
        rw [this]
        have : 0 ≤ (R ^ r * De) ^ 2 * ((2:ℝ) ^ (a + b))⁻¹ := by positivity
        linarith)
      (by
        rw [div_mul_eq_mul_div, le_div_iff₀ hD, one_mul]
        have j1 : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
        have : ((2:ℝ) ^ (i + i')) ^ r ≤ (2 ^ (i + i')) ^ (2 * r) :=
          pow_le_pow_right₀ hu1 (by omega)
        calc D ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := g2.trans hSSr
          _ ≤ (2 ^ (i + i')) ^ (2 * r) * (2 * H₁) ^ (2 * r) := by gcongr
          _ = 1 * (2 ^ (i + i') * (2 * H₁)) ^ (2 * r) := by rw [mul_pow _ (2 * H₁), one_mul]
          _ ≤ _ := by gcongr)
      (by
        refine g3.trans (max_le (one_le_pow₀ hu1) ?_)
        rw [div_le_iff₀ (by positivity)]
        exact hSSr)
    rw [← hRu, ← hqdef] at key
    have hsq : Real.sqrt (R ^ e) * Real.sqrt (R ^ e) = R ^ e := Real.mul_self_sqrt (by positivity)
    calc _ = Real.sqrt (K * K') * ((Real.sqrt (R ^ e) * Real.sqrt (R ^ e)) * (y * y') ^ (k + 1)
            * (((2:ℝ) ^ (i + i')) ^ q)⁻¹) := by
          rw [Real.sqrt_mul hK.le, mul_pow y, pow_add 2 i i', mul_pow _ _ q, mul_inv]; ring
      _ ≤ Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
            * sg ^ (-((n : ℝ) / r)) * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
          rw [hsq]; gcongr
      _ = _ := by rw [hC]; ring
  calc _ = ∫⁻ x in ⋃ p, P p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = 16 * ENNReal.ofReal C := dyad_tsum_four _
    _ = ENNReal.ofReal (16 * C) := by
        rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 16 by norm_num), ENNReal.ofReal_ofNat]
    _ = _ := by rw [hC]; congr 1; ring

end GlobalTheory.Amp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DyadicSummationWithDecayStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dyadic_summation_with_decay : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  first | exact @GlobalTheory.Amp.dyadic_summation | exact GlobalTheory.Amp.dyadic_summation | (intros; apply GlobalTheory.Amp.dyadic_summation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlace
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegConv

variable {k r : ℕ}

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem lmul_inv_lmul {γ : Mat k r} (hγ : γ ∈ GG k r) (x : Mt k r) : lmulM γ⁻¹ (lmulM γ x) = x :=
  Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)

def lmulEquiv {γ : Mat k r} (hγ : γ ∈ GG k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM γ
  invFun := lmulM γ⁻¹
  left_inv := lmul_inv_lmul hγ
  right_inv x := Matrix.mul_nonsing_inv_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)
  measurable_toFun := (continuous_lmul γ).measurable
  measurable_invFun := (continuous_lmul γ⁻¹).measurable

theorem quot_map {γ : Mat k r} (hγ : γ ∈ GG k r) {μG μR ν : Measure (Mt k r)} (hG : IsHaarOn (GG k r) μG)
    (h : IsQuotMeas μG μR ν) : IsQuotMeas μG (μR.map (conjM γ)) (ν.map (lmulEquiv hγ)) := by
  intro f hf
  rw [lintegral_map_equiv]
  have h1 := h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)
  rw [← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ] at h1
  rw [h1]
  refine lintegral_congr fun x => ?_
  have hm : Measurable fun s : Mt k r => f (rmulM (Matrix.of (lmulEquiv hγ x)) s) :=
    hf.comp (continuous_rmulM _).measurable
  refine Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm
  refine lintegral_congr fun s => ?_
  congr 1
  show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)
  rw [Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ),
    Matrix.mul_assoc]

def Gs (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

def ext0 (f : Mat k r → ℝ) : Mt k r → ℝ := Set.indicator (Gs k r) fun x => f (Matrix.of x)

theorem cochainExtendByZeroSubgroup_of_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∈ GG k r) : ext0 f x = f (Matrix.of x) :=
  Set.indicator_of_mem (s := Gs k r) hx _

theorem amplifierAbsConvExtendByZero_of_not_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∉ GG k r) : ext0 f x = 0 :=
  Set.indicator_of_notMem (s := Gs k r) hx _

theorem measurable_amplifierAbsConvExtendByZero {f : Mat k r → ℝ} (hf : ContinuousOn f (GG k r)) : Measurable (ext0 f) := by
  classical
  have hc : IsClosed (Gs k r) := isClosedSub_GG.2.1
  have h1 : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) (Gs k r) := hf
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h1 continuousOn_const hc.measurableSet
  convert this using 1
  exact (Set.piecewise_eq_indicator).symm

def Kc (k r j : ℕ) (De : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (4 * r ^ 2) * De ^ (8 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) *
    4 ^ (k - 1 - j) * (4 * r + 4)

theorem side {j : ℕ} {hj : j ≤ r} {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {z z' : Fin (2 * r + k + 1) → ℂ} {π' : Mat k r → (Wq →L[ℂ] Wq)} {ψ' : Mat k r → ℂ}
    {μG μW' νS' μR νR : Measure (Mt k r)} {Φ' : Mat k r → Wq} {γ : Mat k r} {c κ s H₁ De : ℝ} {q : ℕ}
    (hj1 : 1 ≤ j) (hk : j + 2 ≤ k) (hκ : 0 < κ) (hs : 0 < s) (hH : 1 ≤ H₁) (hγ : γ ∈ GG k r)
    (h1 : OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c) (h2 : TailBd z' νS' Φ' q H₁)
    (h4 : DeOK k r z z' γ De) (h5 : IsNormalFormStabilizerMeasure k r hj z z' γ s μR) (h6 : IsQuotMeas μG μR νR)
    (w : Wq) (hw : ‖w‖ = 1) (i i' : ℕ) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in {x | ext0 (Sg2 k r z') x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < ext0 (Sg2 k r z') x) ∧
        ext0 (Sg2 k r z) (lmulM γ x) ≤ 2 ^ (i + 1) * H₁ ∧ y < ext0 (Yj k r hj z z' γ) x ∧
        ext0 (Yj k r hj z z' γ) x ≤ 2 * y},
      ENNReal.ofReal (ext0 (fun g => ‖⟪w, Φ' g⟫_ℂ‖) x ^ 2) ∂νR ≤
    ENNReal.ofReal (κ / s * Kc k r j De * c * (2 ^ (i + i' + 1) * H₁) ^ (16 * r ^ 3) * y ^ (2 * (k - 1 - j)) *
      (((2 : ℝ) ^ i') ^ (2 * q))⁻¹) := by
  have hH0 : 0 ≤ H₁ := zero_le_one.trans hH
  have q1 : (2 : ℝ) ^ (i + 1) * H₁ ≤ 2 ^ (i + i' + 1) * H₁ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hH0
  have q2 : (2 : ℝ) ^ (i' + 1) * H₁ ≤ 2 ^ (i + i' + 1) * H₁ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hH0
  have hR : (1 : ℝ) ≤ 2 ^ (i + i' + 1) * H₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH
  have key := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hk hκ hs hH h1 h2 h4 h5 h6).2
    w hw i' _ y hR hy
  refine le_trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) fun x => ?_) (key.trans (le_of_eq ?_))
  · rintro x ⟨a1, a2, a3, a4, a5⟩
    have hx : Matrix.of x ∈ GG k r := by
      by_contra hx
      rw [amplifierAbsConvExtendByZero_of_not_mem _ hx] at a4
      exact lt_asymm hy a4
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx
    rw [cochainExtendByZeroSubgroup_of_mem _ hx] at a1 a2 a4 a5
    rw [cochainExtendByZeroSubgroup_of_mem _ hx'] at a3
    exact ⟨⟨hx, a1.trans q2, a3.trans q1, a4, a5⟩, a2⟩
  · by_cases hx : Matrix.of x ∈ GG k r
    · simp only [cochainExtendByZeroSubgroup_of_mem _ hx, le_refl]
    · simp [amplifierAbsConvExtendByZero_of_not_mem _ hx]
  · congr 1
    unfold fibVol0 Kc
    generalize (2 : ℝ) ^ (i + i' + 1) * H₁ = R
    rw [mul_pow 2 y, pow_mul (2 : ℝ) 2, mul_pow (R ^ (2 * r)), ← pow_mul R,
      show 2 * r * (8 * r ^ 2) = 16 * r ^ 3 by ring]
    norm_num only
    ring

theorem max_bounds {r : ℕ} {M D De Y T : ℝ} (hD0 : 0 < D) (hD : D⁻¹ ≤ De) (hT : 0 ≤ T) (hT' : T ≤ M)
    (hY : Y ≤ T ^ r / D) : Y ≤ M ^ r * De := by
  have hM : 0 ≤ M := hT.trans hT'
  refine hY.trans ?_
  rw [div_eq_mul_inv]
  gcongr

theorem one_le_Sg (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : 1 ≤ Sg k r z x := by
  unfold Sg; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem one_le_sgV (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (H₁ : ℝ) : 1 ≤ sgV k r z z' γ H₁ := by
  unfold sgV; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem arith (k r j q : ℕ) {H₁ De D sg : ℝ} (hj : 1 ≤ j) (hH : 1 ≤ H₁) (hDe : 1 ≤ De) (hD : 0 < D) (hsg : 1 ≤ sg) :
    16 * Kc k r j De * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k - 1 - j) *
      sg ^ (-(((q : ℝ) - (16 * r ^ 3 : ℕ) - 4 * r - 1) / r)) ≤ degBd k r j q H₁ De D sg := by
  unfold degBd Kc
  generalize k - 1 - j = m
  have e : (((16 * r ^ 3 : ℕ) : ℝ)) = 16 * (r : ℝ) ^ 3 := by push_cast; ring
  rw [e]
  have hs0 : 0 ≤ sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) := Real.rpow_nonneg (zero_le_one.trans hsg) _
  generalize sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) = t at hs0
  have h8 : (4 : ℝ) ^ m * (2 ^ j) ^ m ≤ 8 ^ (j * m) := by
    have : (4 : ℝ) ^ m ≤ 4 ^ (j * m) := pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left m hj)
    rw [← pow_mul, show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
    gcongr
  have hP : 0 ≤ Real.pi * Real.exp 1 / (m : ℝ) := by positivity
  rw [show 8 * Real.pi * Real.exp 1 / (m : ℝ) = 8 * (Real.pi * Real.exp 1 / m) by ring, mul_pow (8 : ℝ), div_pow _ D,
    pow_add De]
  generalize Real.pi * Real.exp 1 / (m : ℝ) = P at hP ⊢
  have hH0 : 0 ≤ H₁ := zero_le_one.trans hH
  have hDe0 : 0 ≤ De := zero_le_one.trans hDe
  have hc : 0 ≤ 16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) *
      (De ^ (8 * r ^ 2) * De ^ 2) * P ^ (j * m) * (D ^ m)⁻¹ * t := by positivity
  have := mul_le_mul_of_nonneg_left h8 hc
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · rw [div_eq_mul_inv]
    generalize (2 * H₁) ^ (16 * r ^ 3 + 4 * r) = A
    generalize (4 * r : ℝ) ^ (4 * r ^ 2) = B
    generalize ((2 : ℝ) ^ j) ^ m = C
    ring
  · generalize (2 * H₁) ^ (16 * r ^ 3 + 4 * r) = A
    generalize (4 * r : ℝ) ^ (4 * r ^ 2) = B
    ring

theorem deg_core : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 16 * r ^ 3 + 4 * r + 2 ≤ q → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z νS Φ q H₁ → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * degBd k r j q H₁ De (Dj k r hj z z' γ) (sgV k r z z' γ H₁) := by
  intro k r j hj z z' Wp _ _ _ Wq _ _ _ π π' ψ ψ' μG μW μW' νS νS' μR νR Φ Φ' γ c κ s H₁ De q hj1 hk hq hκ hs hH o1 o2
    m1 m2 de nr qm
  obtain ⟨hγ, -, -, -, nr', hD, hDD, hde⟩ := GlobalTheory.T.stabilizer_measure_normalisation_symm k r j hj z z' γ s μR hs nr
  have hr : 1 ≤ r := hj1.trans hj
  have hγ' : γ⁻¹ ∈ GG k r := isClosedSub_GG.2.2.2.2 _ hγ
  have hG : IsHaarOn (GG k r) μG := o1.2.2.2.2.2.1
  have hc : 0 < c := o1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ : ContinuousOn Φ (GG k r) := o1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ' : ContinuousOn Φ' (GG k r) := o2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have de' := hde De de
  have qm' := quot_map hγ hG qm
  have hDe : (Dj k r hj z z' γ)⁻¹ ≤ De := de.2 ⟨j, by omega⟩ hj (norm_ne_zero_iff.1 hD.ne')
  have hDe1 : 1 ≤ De := de.1
  have n1 := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hk hκ hs hH o2 m2 de nr qm).1
  have n2 := (GlobalTheory.T.amplification_degenerate_side_piece_bound k r j hj z' z π ψ μG μW νS _ _ Φ γ⁻¹ c κ s H₁ De q hj1 hk hκ hs hH o1 m1 de' nr' qm').1
  rw [MeasurableEquiv.map_apply] at n2
  have a1 : ∀ᵐ x ∂νR, Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n1] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] using hx
  have a2 : ∀ᵐ x ∂νR, Yj k r hj z' z γ⁻¹ (γ * Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n2] with x hx
    exact fun h => hx (Or.inr h)
  have n0 : νR {x | Matrix.of x ∉ GG k r} = 0 := measure_mono_null (fun x hx => Or.inl hx) n1
  have hkk : 1 ≤ k - 1 - j := by omega
  have hK : 0 < κ / s * Kc k r j De * c := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) < ((k - 1 - j : ℕ) : ℝ) := by exact_mod_cast hkk
    unfold Kc
    positivity
  have hsg := one_le_sgV z z' γ H₁
  have me : Measurable (lmulM γ : Mt k r → Mt k r) := (continuous_lmul γ).measurable
  have g1 := GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z o1.1 o1.2.1
  have g2 := GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' o2.1 o2.2.1
  have main := GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings k r νR Φ Φ' γ c (16 * (κ / s * Kc k r j De * c) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ 2 *
    (2 ^ j / Dj k r hj z z' γ) ^ (k - 1 - j) *
    sgV k r z z' γ H₁ ^ (-(((q : ℝ) - (16 * r ^ 3 : ℕ) - 4 * r - 1) / r))) hγ n0 cΦ cΦ' hc (by positivity) ?_
  · refine ⟨main.1, main.2.trans ?_⟩
    have := arith k r j q hj1 hH hDe1 hD hsg
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ / s))
    field_simp
  intro v w hv hw
  have mA : Measurable (ext0 fun g => ‖⟪v, Φ g⟫_ℂ‖) :=
    measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ).norm
  have mB : Measurable (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) :=
    measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ').norm
  have mS : Measurable (ext0 (Sg2 k r z)) := measurable_amplifierAbsConvExtendByZero g1.2.2.1
  have mS' : Measurable (ext0 (Sg2 k r z')) := measurable_amplifierAbsConvExtendByZero g2.2.2.1
  have mY : Measurable (ext0 (Yj k r hj z' z γ⁻¹)) :=
    (GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z' z γ⁻¹ o2.1 o1.1 o2.2.1 o1.2.1 hγ').1
  have mY' : Measurable (ext0 (Yj k r hj z z' γ)) := (GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' γ o1.1 o2.1 o1.2.1 o2.2.1 hγ).1
  have dy := GlobalTheory.T.dyadic_summation_with_decay (Mt k r) νR (fun x => ext0 (fun g => ‖⟪v, Φ g⟫_ℂ‖) (lmulM γ x))
    (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) (fun x => ext0 (Sg2 k r z) (lmulM γ x)) (ext0 (Sg2 k r z'))
    (fun x => ext0 (Yj k r hj z' z γ⁻¹) (lmulM γ x)) (ext0 (Yj k r hj z z' γ)) r j (k - 1 - j) (16 * r ^ 3) q H₁ De
    (Dj k r hj z z' γ) _ _ _
    (mA.comp me) mB (mS.comp me) mS' (mY.comp me) mY' hr hkk hq hH hDe1 hD hK hK hsg ?_ ?_
    (fun i i' y hy => side hj1 hk hκ hs hH hγ o2 m2 de nr qm w hw i i' y hy)
  · rw [Real.sqrt_mul_self hK.le] at dy
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) dy
    filter_upwards [a1] with x hx
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    rw [cochainExtendByZeroSubgroup_of_mem _ hx.1, cochainExtendByZeroSubgroup_of_mem _ hx']
    rfl
  · filter_upwards [a1, a2] with x hx hx2
    have hx' : γ * Matrix.of x ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    have e1 : ∀ f : Mat k r → ℝ, ext0 f (lmulM γ x) = f (γ * Matrix.of x) := fun f => cochainExtendByZeroSubgroup_of_mem f hx'
    simp only [e1, cochainExtendByZeroSubgroup_of_mem _ hx.1]
    obtain ⟨s1, t1, -⟩ := g1.2.2.2 (γ * Matrix.of x)
    obtain ⟨s2, t2, -⟩ := g2.2.2.2 (Matrix.of x)
    have u1 : 0 ≤ Sg k r z (γ * Matrix.of x) := zero_le_one.trans (one_le_Sg _ _)
    have u2 : 0 ≤ Sg k r z' (Matrix.of x) := zero_le_one.trans (one_le_Sg _ _)
    obtain ⟨b1, b2, b3, b4⟩ := GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths k r j hj z z' γ o1.1 o2.1 hγ _ hx.1
    obtain ⟨-, b5, b6, -⟩ := GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths k r j hj z' z γ⁻¹ o2.1 o1.1 hγ' _ hx'
    rw [Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), hDD] at b6
    have pw : (Sg k r z' (Matrix.of x) * Sg k r z (γ * Matrix.of x)) ^ r ≤
        (Sg2 k r z (γ * Matrix.of x) * Sg2 k r z' (Matrix.of x)) ^ r := by
      rw [mul_comm]
      exact pow_le_pow_left₀ (mul_nonneg u1 u2) (mul_le_mul t1 t2 u2 (u1.trans t1)) _
    refine ⟨norm_nonneg _, norm_nonneg _, s1, s2, lt_of_le_of_ne b5 hx2.symm, lt_of_le_of_ne b2 hx.2.symm, ?_,
      (b1 ⟨j, by omega⟩).trans pw,
      max_bounds hD hDe u2 (t2.trans (le_max_right _ _)) b6,
      max_bounds hD hDe u1 (t1.trans (le_max_left _ _)) b3, ?_⟩
    · rw [mul_comm (Yj k r hj z' z γ⁻¹ _)]
      exact GlobalTheory.T.flagGramNumber_mul_leadingMinor_le_two_pow k r j hj z z' γ s μR nr _ hx.1
    · exact (b4 H₁ hH).trans (max_le_max le_rfl (div_le_div_of_nonneg_right pw (by positivity)))
  · intro i i' y hy
    have h := side hj1 hk hκ hs hH hγ' o1 m1 de' nr' qm' v hv i' i y hy
    rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, add_comm i' i] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [show lmulEquiv hγ x = lmulM γ x from rfl, lmul_inv_lmul hγ]

end GlobalTheory.Amp.DegConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlaceStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 16 * r ^ 3 + 4 * r + 2 ≤ q → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z νS Φ q H₁ → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * degBd k r j q H₁ De (Dj k r hj z z' γ) (sgV k r z z' γ H₁) := by
  first | exact @GlobalTheory.Amp.DegConv.deg_core | exact GlobalTheory.Amp.DegConv.deg_core | (intros; apply GlobalTheory.Amp.DegConv.deg_core <;> assumption)
end
