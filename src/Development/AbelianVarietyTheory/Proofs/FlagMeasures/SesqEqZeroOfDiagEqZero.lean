module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integrable_matrixCoeff_mul_star
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ) (x y x' y' : H) :
    Integrable (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) μ := by
  refine Integrable.mono' ((hsq x y).add (hsq x' y'))
    ((hmeas x y).mul (hmeas x' y').star) (Filter.Eventually.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, Pi.add_apply]
  nlinarith [sq_nonneg (‖⟪y, σ g x⟫_ℂ‖ - ‖⟪y', σ g x'⟫_ℂ‖),
    mul_nonneg (norm_nonneg ⟪y, σ g x⟫_ℂ) (norm_nonneg ⟪y', σ g x'⟫_ℂ)]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_self
    (hsq : ∀ x y : H, ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ ∂μ = ⟪x, x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have h : (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ) =
      fun g => ((‖⟪y, σ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, integral_complex_ofReal, hsq x y, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  push_cast; rfl

open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization (a b : ℂ) :
    a * conj b = 1 / 4 * ((a + b) * conj (a + b) - (a - b) * conj (a - b)
      + Complex.I * ((a + Complex.I * b) * conj (a + Complex.I * b))
      - Complex.I * ((a - Complex.I * b) * conj (a - Complex.I * b))) := by
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_swap_eq_polarization (x x' : H) :
    ⟪x', x⟫_ℂ = 1 / 4 * (⟪x + x', x + x'⟫_ℂ - ⟪x - x', x - x'⟫_ℂ
      + Complex.I * ⟪x + Complex.I • x', x + Complex.I • x'⟫_ℂ
      - Complex.I * ⟪x - Complex.I • x', x - Complex.I • x'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_same_left
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x x' y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ ∂μ = ⟪x', x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hdiag := integral_matrixCoeff_mul_star_self (fun x y => (hsq x y).2)
  have hpt : ∀ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪y, σ g (x + x')⟫_ℂ * star ⟪y, σ g (x + x')⟫_ℂ
        - ⟪y, σ g (x - x')⟫_ℂ * star ⟪y, σ g (x - x')⟫_ℂ
        + Complex.I * (⟪y, σ g (x + Complex.I • x')⟫_ℂ * star ⟪y, σ g (x + Complex.I • x')⟫_ℂ)
        - Complex.I * (⟪y, σ g (x - Complex.I • x')⟫_ℂ * star ⟪y, σ g (x - Complex.I • x')⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization ⟪y, σ g x⟫_ℂ ⟪y, σ g x'⟫_ℂ]
    simp only [map_add (f := _), map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      Complex.star_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    hdiag, hdiag, hdiag, hdiag, inner_swap_eq_polarization x x']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).add ((hint _ _ _ _).const_mul _)

open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization_four (a a' b b' : ℂ) :
    a * conj b' = 1 / 4 * ((a + a') * conj (b + b') - (a - a') * conj (b - b')
      - Complex.I * ((a - Complex.I * a') * conj (b - Complex.I * b'))
      + Complex.I * ((a + Complex.I * a') * conj (b + Complex.I * b'))) := by
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_eq_polarization (w w' : H) :
    ⟪w, w'⟫_ℂ = 1 / 4 * (⟪w + w', w + w'⟫_ℂ - ⟪w - w', w - w'⟫_ℂ
      - Complex.I * ⟪w + Complex.I • w', w + Complex.I • w'⟫_ℂ
      + Complex.I * ⟪w - Complex.I • w', w - Complex.I • w'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

theorem _root_.GlobalTheory.polarised_schur_relations :
    ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), (∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ) → (∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) → ∀ v w v' w' : H, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧ ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  intro G _ _ μ H _ _ _ σ d hmeas hsq v w v' w'
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hone := integral_matrixCoeff_mul_star_same_left hmeas hsq
  refine ⟨hint v w v' w', ?_⟩
  have hpt : ∀ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪w + w', σ g v⟫_ℂ * star ⟪w + w', σ g v'⟫_ℂ
        - ⟪w - w', σ g v⟫_ℂ * star ⟪w - w', σ g v'⟫_ℂ
        - Complex.I * (⟪w + Complex.I • w', σ g v⟫_ℂ * star ⟪w + Complex.I • w', σ g v'⟫_ℂ)
        + Complex.I * (⟪w - Complex.I • w', σ g v⟫_ℂ * star ⟪w - Complex.I • w', σ g v'⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization_four ⟪w, σ g v⟫_ℂ ⟪w', σ g v⟫_ℂ
      ⟪w, σ g v'⟫_ℂ ⟪w', σ g v'⟫_ℂ]
    simp only [inner_add_left, inner_sub_left, inner_smul_left, Complex.conj_I, Complex.star_def,
      neg_mul, ← sub_eq_add_neg, sub_neg_eq_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    hone, hone, hone, hone, inner_eq_polarization w w']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).sub ((hint _ _ _ _).const_mul _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
open NumberField

namespace GlobalTheory

theorem _root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ↔ differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact (dvd_differentIdeal_iff (P := M)).1 (Ideal.dvd_iff_le.2 hle) (h ⟨M, hM.isPrime⟩)
  · intro h P
    show Algebra.IsUnramifiedAt _ P.asIdeal
    rw [← not_dvd_differentIdeal_iff, h, Ideal.dvd_iff_le, top_le_iff]
    exact P.isPrime.ne_top

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntervalIntegralLeMulIntervalIntegralSq
open MeasureTheory

namespace GlobalTheory

theorem sq_intervalIntegral_le_mul_intervalIntegral_sq (g : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hg : ContinuousOn g (Set.Icc 0 s)) :
    (∫ t in (0 : ℝ)..s, g t) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, g t ^ 2 := by
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hg1 : IntervalIntegrable g volume 0 s := (hg.mono hIcc.subset).intervalIntegrable
  have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 s :=
    ((hg.pow 2).mono hIcc.subset).intervalIntegrable
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t in (0 : ℝ)..s, g t) / s := ⟨_, rfl⟩
  have hcs : c * s = ∫ t in (0 : ℝ)..s, g t := by rw [hc]; exact div_mul_cancel₀ _ hs.ne'
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..s, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hs.le (fun t _ => sq_nonneg _)
  have hexp : (fun t => (g t - c) ^ 2) = fun t => (g t ^ 2 - (2 * c) * g t) + c ^ 2 := by
    funext t; ring
  rw [hexp, intervalIntegral.integral_add (hg2.sub (hg1.const_mul (2 * c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hg2 (hg1.const_mul (2 * c)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [sub_zero, smul_eq_mul] at h0
  have hsq : s * c ^ 2 = c * ∫ t in (0 : ℝ)..s, g t := by rw [← hcs]; ring
  have h1 : c * (∫ t in (0 : ℝ)..s, g t) ≤ ∫ t in (0 : ℝ)..s, g t ^ 2 := by linarith
  have h2 : (∫ t in (0 : ℝ)..s, g t) ^ 2 = s * (c * ∫ t in (0 : ℝ)..s, g t) := by
    rw [← hcs]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 hs.le

theorem sobolev_endpoint_one_variable : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ φ' : ℝ → H) (s : ℝ), 0 < s → (∀ t ∈ Set.Icc 0 s, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc 0 s) → ‖φ 0‖ ^ 2 ≤ 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
  intro H _ _ _ φ φ' s hs hd hc
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hφc : ContinuousOn φ (Set.Icc 0 s) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hn' : ContinuousOn (fun t => ‖φ' t‖) (Set.Icc 0 s) := hc.norm
  have hn'i : IntervalIntegrable (fun t => ‖φ' t‖) volume 0 s :=
    (hn'.mono hIcc.subset).intervalIntegrable
  have hA : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume 0 s :=
    ((hφc.norm.pow 2).mono hIcc.subset).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ‖φ 0‖ ^ 2 ≤ 2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 := by
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 s := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hint : IntervalIntegrable φ' volume 0 t := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..t, φ' y = φ t - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx)) hint
    have h1 : ‖φ 0‖ ≤ ‖φ t‖ + ‖∫ y in (0 : ℝ)..t, φ' y‖ := by
      rw [hftc]
      have := norm_sub_le (φ t) (φ t - φ 0)
      rwa [sub_sub_cancel] at this
    have h2 : ‖∫ y in (0 : ℝ)..t, φ' y‖ ≤ ∫ y in (0 : ℝ)..t, ‖φ' y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have h3 : ∫ y in (0 : ℝ)..t, ‖φ' y‖ ≤ ∫ y in (0 : ℝ)..s, ‖φ' y‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun y => norm_nonneg _) hn'i
    have h4 : ‖φ 0‖ ≤ ‖φ t‖ + ∫ y in (0 : ℝ)..s, ‖φ' y‖ := by linarith
    nlinarith [norm_nonneg (φ 0), mul_nonneg (norm_nonneg (φ 0)) (sub_nonneg.2 h4),
      sq_nonneg (‖φ t‖ - ∫ y in (0 : ℝ)..s, ‖φ' y‖),
      sq_nonneg (‖φ t‖ + (∫ y in (0 : ℝ)..s, ‖φ' y‖) - ‖φ 0‖)]
  have hmono : ∫ _ in (0 : ℝ)..s, ‖φ 0‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..s, (2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2) :=
    intervalIntegral.integral_mono_on hs.le intervalIntegrable_const
      ((hA.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hA.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  have hCS : (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 :=
    sq_intervalIntegral_le_mul_intervalIntegral_sq (fun t => ‖φ' t‖) s hs hn'
  have key : ‖φ 0‖ ^ 2 * s ≤
      2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hCS hs.le]
  calc ‖φ 0‖ ^ 2 = ‖φ 0‖ ^ 2 * s / s := by field_simp
    _ ≤ (2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2) / s := by
      gcongr
    _ = 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
      field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise

namespace GlobalTheory.RightRegFund

variable {G : Type} [Group G]

def Good (Γ : Subgroup G) (D : Set G) (y : G) : Prop :=
  ∀ γ γ' : Γ, (γ : G) * y ∈ D → (γ' : G) * y ∈ D → γ = γ'

theorem Good.mul {Γ : Subgroup G} {D : Set G} {y : G} (h : Good Γ D y) (δ : Γ) :
    Good Γ D ((δ : G) * y) := by
  intro γ γ' h1 h2
  have := h (γ * δ) (γ' * δ) (by simpa [mul_assoc] using h1) (by simpa [mul_assoc] using h2)
  exact mul_right_cancel this

theorem good_mul_iff {Γ : Subgroup G} {D : Set G} {y : G} (δ : Γ) :
    Good Γ D ((δ : G) * y) ↔ Good Γ D y :=
  ⟨fun h => by simpa using h.mul δ⁻¹, fun h => h.mul δ⟩

variable {Γ : Subgroup G} {D : Set G} {r : G → G}

theorem rep_eq (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    {γ : Γ} (hγ : (γ : G) * y ∈ D) : r y = γ * y := by
  obtain ⟨δ, h1, h2⟩ := hr y
  rw [h1, h δ γ (h1 ▸ h2) hγ]

theorem rep_mul (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    (δ : Γ) : r ((δ : G) * y) = r y := by
  obtain ⟨γ, h1, h2⟩ := hr ((δ : G) * y)
  have : r y = ((γ * δ : Γ) : G) * y :=
    rep_eq hr h (by simpa [mul_assoc, ← h1] using h2)
  rw [this, h1]; simp [mul_assoc]

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]

theorem ae_good (hD : IsFundamentalDomain Γ D μ) : ∀ᵐ y ∂μ, Good Γ D y := by
  unfold Good
  refine ae_all_iff.2 fun γ => ae_all_iff.2 fun γ' => ?_
  by_cases h : γ = γ'
  · exact Eventually.of_forall fun _ _ _ => h
  · have h' : γ⁻¹ ≠ γ'⁻¹ := fun e => h (inv_injective e)
    have := hD.aedisjoint h'
    refine (measure_eq_zero_iff_ae_notMem.1 this).mono fun y hy h1 h2 => absurd ?_ hy
    refine ⟨?_, ?_⟩
    · exact mem_inv_smul_set_iff.2 h1
    · exact mem_inv_smul_set_iff.2 h2

theorem ae_rep (hDm : MeasurableSet D) (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    {p : G → Prop} (hp : ∀ᵐ x ∂(μ.restrict D), p x) : ∀ᵐ y ∂μ, p (r y) := by
  rw [ae_restrict_iff' hDm] at hp
  have : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ D → p (γ * y) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae hp
  refine this.mono fun y hy => ?_
  obtain ⟨γ, h1, h2⟩ := hr y
  rw [h1] at h2 ⊢
  exact hy γ h2

theorem aestronglyMeasurable_comp_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {f : G → ℂ} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable (fun y => f (r y)) μ := by
  have hU : (⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D) = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨γ, h1, h2⟩ := hr y
    exact mem_iUnion.2 ⟨γ, by simpa [← h1] using h2⟩
  rw [← Measure.restrict_univ (μ := μ), ← hU, aestronglyMeasurable_iUnion_iff]
  intro γ
  have hm : Measurable fun y => (γ : G) * y := measurable_const_mul _
  refine ((hf.comp_measurable hm).aestronglyMeasurable).congr ?_
  refine (ae_restrict_iff' (hm hDm)).2 ((ae_good hD).mono fun y hy h => ?_)
  simp only [Function.comp]
  rw [rep_eq hr hy h]

theorem ae_rep_eq_self (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) : ∀ᵐ x ∂(μ.restrict D), r x = x := by
  refine (ae_restrict_iff' hDm).2 ((ae_good hD).mono fun y hy h => ?_)
  simpa using rep_eq hr hy (γ := 1) (by simpa using h)

variable [μ.IsMulRightInvariant]

theorem ae_good_mul (hD : IsFundamentalDomain Γ D μ) (g : G) : ∀ᵐ y ∂μ, Good Γ D (y * g) :=
  (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae (ae_good hD)

theorem lintegral_comp_rep_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (φ : G → ℝ≥0∞) (g : G) :
    ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, φ x ∂μ := by
  classical
  let ψ : G → ℝ≥0∞ := fun y => if Good Γ D y then φ (r y) else 0
  have hψ : ∀ (γ : Γ) (y : G), ψ (γ • y) = ψ y := by
    intro γ y
    change ψ ((γ : G) * y) = ψ y
    by_cases h : Good Γ D y
    · simp only [ψ, if_pos h, if_pos (h.mul γ), rep_mul hr h]
    · simp only [ψ, if_neg h, if_neg (mt (good_mul_iff γ).1 h)]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have h1 := (measurePreserving_mul_right μ g⁻¹).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight g⁻¹) (fun x => ψ (x * g)) D
  simp only [inv_mul_cancel_right] at h1
  calc ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, ψ (x * g) ∂μ :=
        lintegral_congr_ae (ae_restrict_of_ae ((ae_good_mul hD g).mono fun y hy => by
          simp only [ψ, if_pos hy]))
    _ = ∫⁻ x in D, ψ x ∂μ := by rw [← h1]; exact hD'.setLIntegral_eq hD ψ hψ
    _ = ∫⁻ x in D, φ x ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (ae_good hD), ae_rep_eq_self hD hDm hr] with y hy h2
        simp only [ψ, if_pos hy, h2]

variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}

theorem map_one (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) : R 1 = 1 := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [hR 1 F, ae_rep_eq_self hD hDm hr] with x h1 h2
  rw [h1, mul_one, h2]; rfl

theorem map_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) (g h : G) :
    R (g * h) = R g * R h := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  have h1 : ∀ᵐ y ∂μ, (R h F : G → ℂ) (r y) = F (r (y * h)) := by
    filter_upwards [ae_rep hDm hr (hR h F), ae_good_mul hD h] with y e1 e2
    obtain ⟨γ, e3, -⟩ := hr y
    rw [e1, e3, mul_assoc, rep_mul hr e2]
  have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1
  filter_upwards [hR (g * h) F, hR g (R h F), ae_restrict_of_ae h2] with x e1 e2 e3
  rw [e1, ContinuousLinearMap.mul_apply, e2, e3, mul_assoc]

theorem norm_map (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) (g : G)
    (F : Lp ℂ 2 (μ.restrict D)) : ‖R g F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hR g F),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      ((Lp.aestronglyMeasurable (R g F)).congr (hR g F)),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable F),
    lintegral_comp_rep_mul hD hDm hr (fun x => ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal) g]

theorem edist_indicator_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (c : ℂ) {s : Set G} (hs : MeasurableSet s) (hμs : μ.restrict D s ≠ ∞) (g g₀ : G) :
    edist (R g (indicatorConstLp 2 hs hμs c)) (R g₀ (indicatorConstLp 2 hs hμs c)) ≤
      ‖c‖ₑ * μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D))) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  set F := indicatorConstLp 2 hs hμs c with hF
  set S := ((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D)) with hS
  have h1 : ∀ᵐ y ∂μ, (F : G → ℂ) (r y) = s.indicator (fun _ => c) (r y) :=
    ae_rep hDm hr (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c))
  have key : ∀ a b x : G, Good Γ D (x * b) → r (x * a) ∈ s → r (x * b) ∉ s →
      ∃ γ : Γ, (γ : G) * x * a ∈ s ∩ D ∧ (γ : G) * x * b ∉ s ∩ D := by
    intro a b x hb h2 h3
    obtain ⟨γ, e1, e2⟩ := hr (x * a)
    refine ⟨γ, by rw [mul_assoc, ← e1]; exact ⟨h2, e2⟩, fun h => h3 ?_⟩
    rw [mul_assoc] at h
    rw [rep_eq hr hb h.2]; exact h.1
  have hU : μ.restrict D (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [hD.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply' hDm]
  have hSm : MeasurableSet S := by
    apply MeasurableSet.symmDiff <;> exact (hs.inter hDm).preimage (by fun_prop)
  have hUm : NullMeasurableSet (⋃ γ : Γ, γ • S) (μ.restrict D) := by
    apply MeasurableSet.nullMeasurableSet
    exact MeasurableSet.iUnion fun γ => hSm.const_smul γ
  rw [Lp.edist_def]
  calc eLpNorm (⇑(R g F) - ⇑(R g₀ F)) 2 (μ.restrict D)
      ≤ eLpNorm ((⋃ γ : Γ, γ • S).indicator fun _ => c) 2 (μ.restrict D) := by
        refine eLpNorm_mono_eNorm_ae ((Lp.aestronglyMeasurable (R g F)).sub
          (Lp.aestronglyMeasurable (R g₀ F))) ?_
        filter_upwards [hR g F, hR g₀ F,
          ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae (ae_good_mul hD g), ae_restrict_of_ae (ae_good_mul hD g₀)]
          with x e1 e2 e3 e4 e5 e6
        rw [Pi.sub_apply, e1, e2, e3, e4]
        by_cases a : r (x * g) ∈ s <;> by_cases b : r (x * g₀) ∈ s
        · simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g g₀ x e6 a b
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g₀ g x e5 b a
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · simp [a, b]
    _ ≤ _ := eLpNorm_indicator_const_le c 2 hUm
    _ ≤ _ := by gcongr

theorem continuous_map [LocallyCompactSpace G] [SecondCountableTopology G]
    [IsFiniteMeasureOnCompacts μ]
    (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (F : Lp ℂ 2 (μ.restrict D)) : Continuous fun g => R g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => R g F)
    ?_ ?_ ?_ F
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine continuous_iff_continuousAt.2 fun g₀ => tendsto_iff_edist_tendsto_0.2 ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆
        ((fun x => x * g₀) ⁻¹' (s ∩ D)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀) (hs.inter hDm).nullMeasurableSet
        (by rw [← Measure.restrict_apply hs]; exact hμs.ne)
    have ht2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at ht2
    have ht3 := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) ht2 (Or.inr enorm_ne_top)
    rw [mul_zero] at ht3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht3 (fun _ => zero_le)
      fun g => edist_indicator_le hD hDm hr hR c hs hμs.ne g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add (f := _)]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => R g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_map hD hDm hr hR, ← dist_eq_norm, dist_comm]
    exact h

end GlobalTheory.RightRegFund
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqSumEqSumSqAddTwoMulSumLt
open Matrix Finset Real

namespace GlobalTheory

theorem _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt (a : ℕ) (j : Fin a → ℤ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k, if i < k then j i * j k else 0 := by
  have h : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if k < i then j k * j i else 0) + (if i = k then j i ^ 2 else 0) := by
    intro i k
    rcases lt_trichotomy i k with hik | hik | hik
    · simp [hik, hik.ne, not_lt.mpr hik.le]
    · subst hik; simp [sq]
    · simp [hik, hik.ne', not_lt.mpr hik.le, mul_comm]
  calc (∑ i, j i) ^ 2 = ∑ i, ∑ k, j i * j k := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ((if i < k then j i * j k else 0) + (if k < i then j k * j i else 0) +
          (if i = k then j i ^ 2 else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h i k
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

theorem _root_.GlobalTheory.dim_unipotent_radical_identities :
    ∀ (a : ℕ) (j : Fin a → ℤ) (n : ℤ), let J := ∑ i, j i; let n₀ := n - 2 * J; let dimN := 4 * (∑ i, ∑ k, if i < k then j i * j k else 0) + 2 * J * n₀ + ∑ i, j i ^ 2; dimN = 2 * J ^ 2 - ∑ i, j i ^ 2 + 2 * J * n₀ ∧ n ^ 2 = n₀ ^ 2 + 2 * ∑ i, j i ^ 2 + 2 * dimN ∧ dimN ≤ 2 * J * n := by
  intro a j n
  dsimp only
  have key := _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt a j
  have hQ : 0 ≤ ∑ i, j i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (j i)
  generalize (∑ i, ∑ k, if i < k then j i * j k else 0) = S at key ⊢
  generalize (∑ i, j i ^ 2) = Q at key hQ ⊢
  generalize (∑ i, j i) = J at key ⊢
  refine ⟨by linear_combination (-2) * key, by linear_combination 4 * key, ?_⟩
  nlinarith [key, sq_nonneg J, hQ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumTransversalEqTsumOrbitQuotientGeneral
open scoped ENNReal Classical

namespace GlobalTheory

theorem tsum_transversal_eq_tsum_orbitQuotient_general {G X A M : Type} [Group G] [MulAction G X]
    [AddCommMonoid M] [TopologicalSpace M] (ι : A → X) (T : X → Prop)
    (hT : ∀ g : G, ∀ x, T x → T (g • x)) (hι : ∀ a, T (ι a))
    (hsurj : ∀ x, T x → ∃ a, ∃ g : G, g • ι a = x)
    (hinj : ∀ a b, (∃ g : G, g • ι a = ι b) → a = b)
    (φ : X → M) (hφ : ∀ g : G, ∀ x, T x → φ (g • x) = φ x) :
    ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  let c : A → MulAction.orbitRel.Quotient G X := fun a => Quotient.mk (MulAction.orbitRel G X) (ι a)
  have hc : Function.Injective c := by
    intro a b hab
    have h : (MulAction.orbitRel G X) (ι a) (ι b) := Quotient.exact hab
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    exact (hinj b a ⟨g, hg⟩).symm
  have hout : ∀ a, ∃ g : G, g • ι a = (c a).out := by
    intro a
    have h : (MulAction.orbitRel G X) ((c a).out) (ι a) := Quotient.exact (Quotient.out_eq (c a))
    rw [MulAction.orbitRel_apply] at h
    exact h
  have hsupp : Function.support
      (fun o : MulAction.orbitRel.Quotient G X => if T o.out then φ o.out else 0) ⊆ Set.range c := by
    intro o ho
    have hTo : T o.out := by
      by_contra hn
      exact ho (if_neg hn)
    obtain ⟨a, g, hg⟩ := hsurj _ hTo
    refine ⟨a, ?_⟩
    rw [← Quotient.out_eq o]
    apply Quotient.sound
    have h : (MulAction.orbitRel G X) o.out (ι a) := by
      rw [MulAction.orbitRel_apply]
      exact ⟨g, hg⟩
    exact (MulAction.orbitRel G X).symm h
  rw [← hc.tsum_eq hsupp]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg⟩ := hout a
  rw [← hg, if_pos (hT g _ (hι a)), hφ g _ (hι a)]

theorem tsum_transversal_eq_tsum_orbitQuotient : ∀ {G X A : Type} [Group G] [MulAction G X] (ι : A → X) (T : X → Prop), (∀ g : G, ∀ x, T x → T (g • x)) → (∀ a, T (ι a)) → (∀ x, T x → ∃ a, ∃ g : G, g • ι a = x) → (∀ a b, (∃ g : G, g • ι a = ι b) → a = b) → (∀ φ : X → ℂ, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0) ∧ ∀ φ : X → ℝ≥0∞, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  intro G X A _ _ ι T hT hι hsurj hinj
  exact ⟨fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ,
    fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank
open NumberField UniqueFactorizationMonoid

namespace GlobalTheory.SplitRadical

theorem isRadical_of_squarefree {S : Type} [CommRing S] [IsDedekindDomain S] {I : Ideal S}
    (hI : Squarefree I) : I.IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h1 : I ∣ Ideal.span {x} ^ n := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 : I ∣ Ideal.span {x} := hI.isRadical n _ h1
  exact (Ideal.span_singleton_le_iff_mem I).1 (Ideal.dvd_iff_le.1 h2)

theorem isRadical_span_of_ncard_primesOver : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E →
    (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  intro E _ _ p hp hcard
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P ≠ ⊥ := by
    rw [hP, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.span {(p : 𝓞 E)} = P.map (algebraMap ℤ (𝓞 E)) := by
    rw [hP, Ideal.map_span, Set.image_singleton, map_natCast]
  have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank, ← hcard, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    ← Finset.card_univ, Finset.card_eq_sum_ones] at hsum

  have hge : ∀ q ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    haveI : q.1.IsPrime := q.2.1
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := ℤ) q.1).ne'
      (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ = 1 := by
    intro q
    have := (Finset.sum_eq_sum_iff_of_le hge).1 hsum.symm q (Finset.mem_univ q)
    exact Nat.eq_one_of_mul_eq_one_right this.symm

  rw [hmap]
  apply isRadical_of_squarefree
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmap0,
    Multiset.nodup_iff_count_le_one]
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors (P.map (algebraMap ℤ (𝓞 E)))
  · have hqprime : q.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor q hq)
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ q :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq)
    have hlo : q.LiesOver P :=
      ⟨hPmax.eq_of_le (Ideal.comap_ne_top _ hqprime.ne_top) (Ideal.map_le_iff_le_comap.1 hle)⟩
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count P q hmap0]
    exact (hone ⟨q, hqprime, hlo⟩).le
  · rw [Multiset.count_eq_zero.2 hq]
    exact zero_le_one

end GlobalTheory.SplitRadical
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen
open MeasureTheory Set TopologicalSpace

namespace GlobalTheory

theorem discreteSubgroup_countable_and_exists_strict_fundamentalDomain : ∀ {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ],
    Countable Γ ∧ ∃ D : Set G, MeasurableSet D ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ D := by
  intro G _ _ _ _ _ _ Γ _
  refine ⟨TopologicalSpace.separableSpace_iff_countable.1 inferInstance, ?_⟩

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have hU1 : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU]; rfl
    simpa using this
  have hUΓ : ∀ x : G, x ∈ U → x ∈ Γ → x = 1 := by
    intro x hx hxΓ
    have : (⟨x, hxΓ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hx
    rw [hU] at this
    simpa using congrArg Subtype.val (show (⟨x, hxΓ⟩ : Γ) = 1 from this)
  obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split (hUo.mem_nhds hU1)

  let P : Set G → Prop := fun W => ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ Γ → x = y
  let S : Set (Set G) := {W | W ∈ countableBasis G ∧ P W}
  have hcover : ∀ g : G, ∃ W ∈ S, g ∈ W := by
    intro g
    let N : Set G := (fun x => x * g⁻¹) ⁻¹' (V ∩ (fun x => x⁻¹) ⁻¹' V)
    have hNo : IsOpen N :=
      (hVo.inter (hVo.preimage continuous_inv)).preimage (continuous_mul_const g⁻¹)
    have hgN : g ∈ N := by simp [N, hV1]
    obtain ⟨W, hWb, hgW, hWN⟩ := (isBasis_countableBasis G).exists_subset_of_mem_open hgN hNo
    refine ⟨W, ⟨hWb, ?_⟩, hgW⟩
    intro x hx y hy hxy
    have hx' := hWN hx
    have hy' := hWN hy
    simp only [N, mem_preimage, mem_inter_iff] at hx' hy'
    have h1 : (x * g⁻¹) * (y * g⁻¹)⁻¹ ∈ U := hVU _ hx'.1 _ hy'.2
    have h2 : (x * g⁻¹) * (y * g⁻¹)⁻¹ = x * y⁻¹ := by group
    rw [h2] at h1
    have := hUΓ _ h1 hxy
    exact mul_inv_eq_one.1 this
  have hSc : S.Countable := (countable_countableBasis G).mono fun W hW => hW.1
  have hSne : S.Nonempty := by
    obtain ⟨W, hW, -⟩ := hcover 1
    exact ⟨W, hW⟩
  obtain ⟨f, hf⟩ := hSc.exists_eq_range hSne
  have hfS : ∀ n, f n ∈ S := fun n => hf ▸ mem_range_self n

  let Sat : ℕ → Set G := fun m => {x | ∃ γ : Γ, (γ : G) * x ∈ f m}
  have hSat : ∀ m, IsOpen (Sat m) := by
    intro m
    have : Sat m = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' f m := by
      ext x; simp [Sat]
    rw [this]
    exact isOpen_iUnion fun γ => ((isBasis_countableBasis G).isOpen (hfS m).1).preimage
      (continuous_const_mul _)
  let D : Set G := ⋃ n, (f n ∩ ⋂ m ∈ Finset.range n, (Sat m)ᶜ)
  refine ⟨D, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => ?_
    refine (((isBasis_countableBasis G).isOpen (hfS n).1).measurableSet).inter ?_
    exact Finset.measurableSet_biInter _ fun m _ => (hSat m).measurableSet.compl
  · intro g
    have hex : ∃ n, ∃ γ : Γ, (γ : G) * g ∈ f n := by
      obtain ⟨W, hW, hgW⟩ := hcover g
      rw [hf] at hW
      obtain ⟨n, rfl⟩ := hW
      exact ⟨n, 1, by simpa using hgW⟩
    classical
    obtain ⟨γ, hγ⟩ := Nat.find_spec hex
    have hmem : ∀ (δ : Γ) n, (δ : G) * g ∈ f n → (∀ m < n, (δ : G) * g ∉ Sat m) → (δ : G) * g ∈ D := by
      intro δ n h1 h2
      refine mem_iUnion.2 ⟨n, h1, ?_⟩
      simp only [mem_iInter, Finset.mem_range, mem_compl_iff]
      exact h2
    refine ⟨γ, hmem γ _ hγ fun m hm hS => ?_, ?_⟩
    · obtain ⟨δ, hδ⟩ := hS
      refine Nat.find_min hex hm ⟨δ * γ, ?_⟩
      simpa [mul_assoc] using hδ
    · intro δ hδ
      have hD : ∀ (ε : Γ), (ε : G) * g ∈ D → ∃ n, (ε : G) * g ∈ f n ∧ ∀ m < n, (ε : G) * g ∉ Sat m := by
        intro ε hε
        obtain ⟨n, h1, h2⟩ := mem_iUnion.1 hε
        refine ⟨n, h1, fun m hm => ?_⟩
        simp only [mem_iInter, Finset.mem_range, mem_compl_iff] at h2
        exact h2 m hm
      obtain ⟨n1, h11, h12⟩ := hD δ hδ
      obtain ⟨n2, h21, h22⟩ := hD γ (hmem γ _ hγ fun m hm hS => by
        obtain ⟨δ', hδ'⟩ := hS
        exact Nat.find_min hex hm ⟨δ' * γ, by simpa [mul_assoc] using hδ'⟩)
      have hn : n1 = n2 := by
        rcases lt_trichotomy n1 n2 with h | h | h
        · exact absurd ⟨δ * γ⁻¹, by simpa [mul_assoc] using h11⟩ (h22 n1 h)
        · exact h
        · exact absurd ⟨γ * δ⁻¹, by simpa [mul_assoc] using h21⟩ (h12 n2 h)
      subst hn
      have hP := (hfS n1).2 _ h11 _ h21 (by
        have : ((δ : G) * g) * ((γ : G) * g)⁻¹ = ((δ * γ⁻¹ : Γ) : G) := by simp [mul_assoc]
        rw [this]; exact (δ * γ⁻¹).2)
      exact Subtype.ext (mul_right_cancel hP)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsOpIntIntegrable
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem absOpInt_integrable {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => π g x) (φ : G → ℂ) (hφ : Integrable φ μ) (y : Hp) :
    Integrable (fun g => φ g • π g y) μ := by
  refine Integrable.mono' (hφ.norm.mul_const ‖y‖) ?_ (ae_of_all _ fun g => ?_)
  · exact hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable
  · rw [norm_smul, hn]

theorem absOpInt : ∀ (G : Type) [Group G] [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ φ : G → ℂ, Integrable φ μ → ∃ P : Hp →L[ℂ] Hp, (∀ y, P y = ∫ g, φ g • π g y ∂μ) ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ := by
  intro G _ _ _ _ _ μ Hp _ _ _ π hn hc φ hφ
  let L : Hp →ₗ[ℂ] Hp :=
    { toFun := fun y => ∫ g, φ g • π g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (absOpInt_integrable μ π hn hc φ hφ y)
          (absOpInt_integrable μ π hn hc φ hφ z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (φ _) c]
        exact integral_smul c _ }
  refine ⟨L.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun y => rfl, fun x y => ?_⟩
  · calc ‖L y‖ = ‖∫ g, φ g • π g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • π g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by simp_rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · change ⟪x, ∫ g, φ g • π g y ∂μ⟫_ℂ = _
    rw [← integral_inner (absOpInt_integrable μ π hn hc φ hφ y)]
    simp_rw [inner_smul_right]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
open NumberField

namespace GlobalTheory

theorem ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) →
        Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) →
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  intro E _ _ p hp h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(p : ℤ)}) hp0
  rw [← hsum, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    simp [Ideal.map_span]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hmem : (p : 𝓞 E) ∈ P := by
    rw [hmap, Ideal.span_singleton_le_iff_mem] at hle
    exact hle
  have hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  obtain ⟨hN, hsq⟩ := h P hPm hmem
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff hle).mp hne
    rw [hmap, Ideal.span_singleton_le_iff_mem] at this
    exact hsq this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hp
    rw [hN] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSqStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  first | exact @GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | exact GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | (intros; apply GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq <;> assumption)
end
end
