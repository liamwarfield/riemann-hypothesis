module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.AbsoluteL2Bound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeometricStatement
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.KrDom
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPath
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFinal

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBisStatement
theorem _root_.GlobalTheory.T.rgExh_pack : CompanionTheory.RgExh.Dec.L.Pack :=
  GlobalTheory.CompanionTheory.PackEmb.pack
end

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.HasCharPath
section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.EnormAddSqLe
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem absorb {M α : Type*} (S : Submodule ℂ (M → ℂ)) (I : Finset α) (h : α → (M → ℂ))
    (hS : ∀ i ∈ I, h i ∈ S) (e : ℕ) (he : 1 ≤ e) :
    ∃ T : Finset (M → ℂ), (∀ f ∈ T, f ∈ S) ∧ ∀ x, ∑ i ∈ I, ‖h i x‖ ^ e ≤ ∑ f ∈ T, ‖f x‖ ^ e := by
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · exact ⟨∅, by simp, fun x => by simp [hI]⟩
  set N : ℝ := (I.card : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Finset.card_pos.mpr hI
  refine ⟨I.image (fun i => (N : ℂ) • h i), ?_, fun x => ?_⟩
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact S.smul_mem _ (hS i hi)
  have key : ∀ i ∈ I, N * ‖h i x‖ ^ e ≤ ∑ f ∈ I.image (fun i => (N : ℂ) • h i), ‖f x‖ ^ e := by
    intro i hi
    have h1 : N * ‖h i x‖ ^ e ≤ ‖((N : ℂ) • h i) x‖ ^ e := by
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ e := pow_le_pow_right₀ hN1 he
    exact h1.trans (Finset.single_le_sum (f := fun f : M → ℂ => ‖f x‖ ^ e) (fun _ _ => by positivity)
      (Finset.mem_image_of_mem _ hi))
  have hsum := Finset.sum_le_sum key
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < N := by linarith
  rw [← hN] at hsum
  exact le_of_mul_le_mul_left hsum hpos

section
variable {M ι : Type*} (G : ι → (M → ℂ))

theorem cont_span {Y : Type*} [TopologicalSpace Y] (φ : Y → M) (hG : ∀ p, Continuous fun y => G p (φ y)) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), Continuous fun y => f (φ y) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

theorem dom_span {β : Type*} (L R : β → M)
    (hG : ∀ p, ∃ (T : Finset ι) (Cf : ℝ), ∀ b, ‖G p (L b)‖ ^ 2 ≤ Cf * ∑ q ∈ T, ‖G q (R b)‖ ^ 2) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ∃ (T : Finset (M → ℂ)) (Cf : ℝ),
      (∀ h ∈ T, h ∈ Submodule.span ℂ (Set.range G)) ∧ ∀ b, ‖f (L b)‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (R b)‖ ^ 2 := by
  classical
  set S := Submodule.span ℂ (Set.range G)
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨T, Cf, hT⟩ := hG p
    obtain ⟨T', hT'S, hT'⟩ := absorb S T G (fun q _ => Submodule.subset_span ⟨q, rfl⟩) 2 (by norm_num)
    refine ⟨T', max Cf 0, hT'S, fun b => ?_⟩
    have h0 : 0 ≤ ∑ q ∈ T, ‖G q (R b)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    calc ‖G p (L b)‖ ^ 2 ≤ Cf * ∑ q ∈ T, ‖G q (R b)‖ ^ 2 := hT b
      _ ≤ max Cf 0 * ∑ q ∈ T, ‖G q (R b)‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ max Cf 0 * ∑ h ∈ T', ‖h (R b)‖ ^ 2 := mul_le_mul_of_nonneg_left (hT' _) (le_max_right _ _)
  | zero => exact ⟨∅, 0, by simp, fun b => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, C₁, h₁S, h₁⟩ := hx
    obtain ⟨T₂, C₂, h₂S, h₂⟩ := hy
    set c : ℝ := Real.sqrt (2 * max (max C₁ C₂) 0)
    have hc2 : c ^ 2 = 2 * max (max C₁ C₂) 0 := Real.sq_sqrt (by positivity)
    obtain ⟨T, hTS, hT⟩ := absorb S (T₁.disjSum T₂) (fun s => (c : ℂ) • Sum.elim id id s)
      (fun s hs => by
        rcases s with s | s
        · exact S.smul_mem _ (h₁S s (Finset.inl_mem_disjSum.mp hs))
        · exact S.smul_mem _ (h₂S s (Finset.inr_mem_disjSum.mp hs))) 2 (by norm_num)
    refine ⟨T, 1, hTS, fun b => ?_⟩
    have e1 := h₁ b
    have e2 := h₂ b
    have s1 : 0 ≤ ∑ h ∈ T₁, ‖h (R b)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have s2 : 0 ≤ ∑ h ∈ T₂, ‖h (R b)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hK := hT (R b)
    rw [Finset.sum_disjSum] at hK
    simp only [Sum.elim_inl, Sum.elim_inr, id, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hc2, ← Finset.mul_sum] at hK
    have hm : ‖x (L b) + y (L b)‖ ^ 2 ≤ 2 * ‖x (L b)‖ ^ 2 + 2 * ‖y (L b)‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (x (L b)) (y (L b))) 2
      nlinarith [sq_nonneg (‖x (L b)‖ - ‖y (L b)‖)]
    have q1 : ‖x (L b)‖ ^ 2 ≤ max (max C₁ C₂) 0 * ∑ h ∈ T₁, ‖h (R b)‖ ^ 2 :=
      e1.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) s1)
    have q2 : ‖y (L b)‖ ^ 2 ≤ max (max C₁ C₂) 0 * ∑ h ∈ T₂, ‖h (R b)‖ ^ 2 :=
      e2.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) s2)
    show ‖x (L b) + y (L b)‖ ^ 2 ≤ 1 * ∑ h ∈ T, ‖h (R b)‖ ^ 2
    nlinarith
  | smul a x _ hx =>
    obtain ⟨T₁, C₁, h₁S, h₁⟩ := hx
    refine ⟨T₁, ‖a‖ ^ 2 * C₁, h₁S, fun b => ?_⟩
    show ‖a * x (L b)‖ ^ 2 ≤ _
    rw [norm_mul, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h₁ b) (by positivity)
end

theorem enorm_add_sq_le (a b : ℂ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem lint_add_lt {α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : α → ℂ) (w : α → ℝ≥0∞)
    (hf : AEMeasurable (fun a => ‖f a‖ₑ ^ 2 * w a) μ)
    (hF : ∫⁻ a, ‖f a‖ₑ ^ 2 * w a ∂μ < ⊤) (hG : ∫⁻ a, ‖g a‖ₑ ^ 2 * w a ∂μ < ⊤) :
    ∫⁻ a, ‖f a + g a‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  calc ∫⁻ a, ‖f a + g a‖ₑ ^ 2 * w a ∂μ ≤ ∫⁻ a, 2 * (‖f a‖ₑ ^ 2 * w a) + 2 * (‖g a‖ₑ ^ 2 * w a) ∂μ := by
        apply lintegral_mono
        intro a
        calc ‖f a + g a‖ₑ ^ 2 * w a ≤ (2 * ‖f a‖ₑ ^ 2 + 2 * ‖g a‖ₑ ^ 2) * w a := by
              gcongr; exact enorm_add_sq_le _ _
          _ = 2 * (‖f a‖ₑ ^ 2 * w a) + 2 * (‖g a‖ₑ ^ 2 * w a) := by ring
    _ = 2 * ∫⁻ a, ‖f a‖ₑ ^ 2 * w a ∂μ + 2 * ∫⁻ a, ‖g a‖ₑ ^ 2 * w a ∂μ := by
        rw [lintegral_add_left' (hf.const_mul 2), lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
    _ < ⊤ := by
        apply ENNReal.add_lt_top.mpr
        exact ⟨ENNReal.mul_lt_top (by simp) hF, ENNReal.mul_lt_top (by simp) hG⟩

theorem lint_smul_lt {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℂ) (f : α → ℂ) (w : α → ℝ≥0∞)
    (hF : ∫⁻ a, ‖f a‖ₑ ^ 2 * w a ∂μ < ⊤) : ∫⁻ a, ‖c * f a‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  have : ∀ a, ‖c * f a‖ₑ ^ 2 * w a = ‖c‖ₑ ^ 2 * (‖f a‖ₑ ^ 2 * w a) := fun a => by
    rw [eNorm_mul, mul_pow, mul_assoc]
  simp_rw [this]
  rw [lintegral_const_mul' _ _ (by simp)]
  exact ENNReal.mul_lt_top (by simp) hF

section
variable {M ι : Type*} (G : ι → (M → ℂ))

theorem lint_span {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ : α → M) (w : α → ℝ≥0∞)
    (hm : ∀ f ∈ Submodule.span ℂ (Set.range G), AEMeasurable (fun a => ‖f (φ a)‖ₑ ^ 2 * w a) μ)
    (hG : ∀ p, ∫⁻ a, ‖G p (φ a)‖ₑ ^ 2 * w a ∂μ < ⊤) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ∫⁻ a, ‖f (φ a)‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero => simp
  | add x y hx' _ hx hy => exact lint_add_lt (fun a => x (φ a)) (fun a => y (φ a)) w (hm x hx') hx hy
  | smul a x _ hx => exact lint_smul_lt a (fun b => x (φ b)) w hx

theorem ae_lint_span {β α : Type*} [MeasurableSpace β] [MeasurableSpace α] (ν : Measure β) (μ : Measure α)
    (φ : β → α → M) (w : α → ℝ≥0∞)
    (hm : ∀ f ∈ Submodule.span ℂ (Set.range G), ∀ x, AEMeasurable (fun a => ‖f (φ x a)‖ₑ ^ 2 * w a) μ)
    (hG : ∀ p, ∀ᵐ x ∂ν, ∫⁻ a, ‖G p (φ x a)‖ₑ ^ 2 * w a ∂μ < ⊤) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ∀ᵐ x ∂ν, ∫⁻ a, ‖f (φ x a)‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero => exact Filter.Eventually.of_forall fun x => by simp
  | add x y hx' _ hx hy =>
    filter_upwards [hx, hy] with b h1 h2
    exact lint_add_lt (fun a => x (φ b a)) (fun a => y (φ b a)) w (hm x hx' b) h1 h2
  | smul a x _ hx =>
    filter_upwards [hx] with b h1
    exact lint_smul_lt a (fun c => x (φ b c)) w h1
end

def ChainQ {n : ℕ} (ε : Fin n → Bool) (S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : S7.UJ ε → ℝ) (m : ℕ) (z : Fin m → ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ F : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ k, F k ∈ S) ∧ F (Fin.last m) = f ∧
    (∀ (k : Fin m) (g : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), ReciprocityTheory.ChartRestriction.DS.inUJ ε g →
      HasDerivAt (fun s : ℝ => F k.succ (g * NormedSpace.exp ((s : ℂ) • A)))
        (z k * F k.succ (g * NormedSpace.exp ((t : ℂ) • A)) +
          F k.castSucc (g * NormedSpace.exp ((t : ℂ) • A))) t) ∧
    ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ h ∈ T, h ∈ S) ∧
      ∀ x : PSub ε A, 0 ≤ τ x → ‖F 0 (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖

theorem chain_span {n : ℕ} {ι : Type*} (G : ι → (Matrix (Fin n) (Fin n) ℂ → ℂ)) (ε : Fin n → Bool)
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : S7.UJ ε → ℝ) (m : ℕ) (z : Fin m → ℂ)
    (hG : ∀ p, ChainQ ε (Submodule.span ℂ (Set.range G)) A τ m z (G p)) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ChainQ ε (Submodule.span ℂ (Set.range G)) A τ m z f := by
  classical
  set S := Submodule.span ℂ (Set.range G)
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero =>
    refine ⟨fun _ => 0, fun _ => S.zero_mem, rfl, fun k g t _ => ?_, ∅, by simp, fun x _ => by simp⟩
    simpa using hasDerivAt_const t (0 : ℂ)
  | add x y _ _ hx hy =>
    obtain ⟨F₁, h₁S, h₁l, h₁d, T₁, hT₁S, hT₁⟩ := hx
    obtain ⟨F₂, h₂S, h₂l, h₂d, T₂, hT₂S, hT₂⟩ := hy
    obtain ⟨T, hTS, hT⟩ := absorb S (T₁.disjSum T₂) (fun s => Sum.elim id id s)
      (fun s hs => by
        rcases s with s | s
        · exact hT₁S s (Finset.inl_mem_disjSum.mp hs)
        · exact hT₂S s (Finset.inr_mem_disjSum.mp hs)) 1 le_rfl
    refine ⟨F₁ + F₂, fun k => S.add_mem (h₁S k) (h₂S k), by rw [Pi.add_apply, h₁l, h₂l], fun k g t hg => ?_,
      T, hTS, fun x hx => ?_⟩
    · exact ((h₁d k g t hg).add (h₂d k g t hg)).congr_deriv (by simp only [Pi.add_apply]; ring)
    · have hK := hT (S7.toM (x : S7.UJ ε))
      rw [Finset.sum_disjSum] at hK
      simp only [Sum.elim_inl, Sum.elim_inr, id, pow_one] at hK
      have e1 := hT₁ x hx
      have e2 := hT₂ x hx
      have hp : 0 < Real.exp (-τ x) := Real.exp_pos _
      calc ‖(F₁ + F₂) 0 (S7.toM (x : S7.UJ ε))‖
          ≤ ‖F₁ 0 (S7.toM (x : S7.UJ ε))‖ + ‖F₂ 0 (S7.toM (x : S7.UJ ε))‖ := by
            rw [Pi.add_apply, Pi.add_apply]; exact norm_add_le _ _
        _ ≤ Real.exp (-τ x) * (∑ h ∈ T₁, ‖h (S7.toM (x : S7.UJ ε))‖ + ∑ h ∈ T₂, ‖h (S7.toM (x : S7.UJ ε))‖) := by
            rw [mul_add]; exact add_le_add e1 e2
        _ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := mul_le_mul_of_nonneg_left hK hp.le
  | smul a x _ hx =>
    obtain ⟨F₁, h₁S, h₁l, h₁d, T₁, hT₁S, hT₁⟩ := hx
    obtain ⟨T, hTS, hT⟩ := absorb S T₁ (fun h => a • h) (fun h hh => S.smul_mem _ (hT₁S h hh)) 1 le_rfl
    refine ⟨a • F₁, fun k => S.smul_mem _ (h₁S k), by rw [Pi.smul_apply, h₁l], fun k g t hg => ?_,
      T, hTS, fun x hx => ?_⟩
    · exact ((h₁d k g t hg).const_mul a).congr_deriv (by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    · have hK := hT (S7.toM (x : S7.UJ ε))
      simp only [pow_one, Pi.smul_apply, smul_eq_mul, norm_mul] at hK
      have e1 := hT₁ x hx
      have hp : 0 < Real.exp (-τ x) := Real.exp_pos _
      calc ‖(a • F₁) 0 (S7.toM (x : S7.UJ ε))‖ = ‖a‖ * ‖F₁ 0 (S7.toM (x : S7.UJ ε))‖ := by
            rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
        _ ≤ ‖a‖ * (Real.exp (-τ x) * ∑ h ∈ T₁, ‖h (S7.toM (x : S7.UJ ε))‖) :=
            mul_le_mul_of_nonneg_left e1 (norm_nonneg _)
        _ = Real.exp (-τ x) * ∑ h ∈ T₁, ‖a‖ * ‖h (S7.toM (x : S7.UJ ε))‖ := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := mul_le_mul_of_nonneg_left hK hp.le

end CompanionTheory.RgExh.Dec.L.SA
end
end

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Source
section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Imports
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

def gen {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (ss : List (Fin n)) :
    (D × List (Fin n)) × (path ⟨D, E, hE⟩ χ ss).V → (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  fun p => famP σ D E hE χ ss p.1 p.2

def SS {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (ss : List (Fin n)) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  Submodule.span ℂ (Set.range (gen σ D E hE χ ss))

theorem gen_mem {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (ss : List (Fin n)) (i : D × List (Fin n))
    (u : (path ⟨D, E, hE⟩ χ ss).V) : famP σ D E hE χ ss i u ∈ SS σ D E hE χ ss :=
  Submodule.subset_span ⟨(i, u), rfl⟩

end CompanionTheory.RgExh.Dec.L.SA
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem source_gen (hL : N.LeftRule) {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (A : Matrix (Fin n) (Fin n) ℂ) (τ : S7.UJ ε → ℝ) (C : ℝ)
    (hC : ∀ (x : PSub ε A) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilpC A → 0 ≤ τ x →
      Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Y * (S7.toM (x : S7.UJ ε))⁻¹) ≤ C * Real.exp (-2 * τ x) * Formalism.REAL.hs Y)
    (i : D × List (Fin n)) (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin m → (path ⟨D, E, hK.gl⟩ χ ss).V) (hY : ∀ k, Y k ∈ nilpC A) :
    ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧
      ∀ x : PSub ε A, 0 ≤ τ x →
        ‖famP σ D E hK.gl χ ss i (∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k)) (S7.toM (x : S7.UJ ε))‖ ≤
          Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := by
  classical
  obtain ⟨l, hl⟩ := hL n ε H σ D E hK χ ss hU i
  let Lf : Fin n → Fin n → (path ⟨D, E, hK.gl⟩ χ ss).V → (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
    fun c d w => (l c d).sum (fun i' r => r • famP σ D E hK.gl χ ss i' w)
  have hLf_mem : ∀ c d w, Lf c d w ∈ SS σ D E hK.gl χ ss := fun c d w =>
    Submodule.sum_mem _ (fun i' _ => Submodule.smul_mem _ _ (gen_mem σ D E hK.gl χ ss i' w))
  have hLf_apply : ∀ c d w g, Lf c d w g = (l c d).sum (fun i' r => r * famP σ D E hK.gl χ ss i' w g) := by
    intro c d w g
    simp only [Lf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hmat : ∀ (g Y' : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n),
      (g * Y' * g⁻¹) c d = ∑ a, ∑ b, Y' a b * (g * Matrix.single a b (1 : ℂ) * g⁻¹) c d := by
    intro g Y' c d
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y']
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y' a b) = Y' a b • Matrix.single a b (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hcomm : ∀ (F : Fin n → Fin n → Fin n → Fin n → ℂ),
      ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
    intro F
    have h := Finset.sum_comm (s := (Finset.univ : Finset (Fin n × Fin n))) (t := (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun p q => F p.1 p.2 q.1 q.2)
    simpa only [Fintype.sum_prod_type] using h

  have hid : ∀ g, Formalism.REAL.inUJ ε g → famP σ D E hK.gl χ ss i (∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k)) g =
      ∑ k, ∑ c, ∑ d, (g * Y k * g⁻¹) c d * Lf c d (v k) g := by
    intro g hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hact : actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k) = ∑ a, ∑ b, Y k a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b (v k) := by
      delta actM
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hact]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hl _ _ _ g hg, ← hLf_apply]
    simp only [hmat g (Y k), Finset.mul_sum, Finset.sum_mul]
    rw [hcomm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring

  have hent : ∀ (x : PSub ε A) (k : Fin m) (c d : Fin n), 0 ≤ τ x →
      ‖(S7.toM (x : S7.UJ ε) * Y k * (S7.toM (x : S7.UJ ε))⁻¹) c d‖ ≤
        Real.exp (-τ x) * Real.sqrt (C * Formalism.REAL.hs (Y k)) := by
    intro x k c d hx
    set M := S7.toM (x : S7.UJ ε) * Y k * (S7.toM (x : S7.UJ ε))⁻¹
    have e1 : ‖M c d‖ ^ 2 ≤ Formalism.REAL.hs M := by
      unfold Formalism.REAL.hs
      exact (Finset.single_le_sum (f := fun j => ‖M c j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ d)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ c))
    have hexp2 : Real.exp (-τ x) ^ 2 = Real.exp (-2 * τ x) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Formalism.REAL.hs M ≤ (C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) ^ 2 := by
      rw [hexp2]
      calc Formalism.REAL.hs M ≤ C * Real.exp (-2 * τ x) * Formalism.REAL.hs (Y k) := hC x (Y k) (hY k) hx
        _ = (C * Formalism.REAL.hs (Y k)) * Real.exp (-2 * τ x) := by ring
    calc ‖M c d‖ = Real.sqrt (‖M c d‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) ^ 2) := Real.sqrt_le_sqrt (e1.trans e2)
      _ = Real.sqrt (C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
      _ = Real.exp (-τ x) * Real.sqrt (C * Formalism.REAL.hs (Y k)) := mul_comm _ _

  let hq : Fin m × Fin n × Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) := fun q =>
    ((Real.sqrt (C * Formalism.REAL.hs (Y q.1)) : ℝ) : ℂ) • Lf q.2.1 q.2.2 (v q.1)
  obtain ⟨T, hTS, hT⟩ := absorb (SS σ D E hK.gl χ ss) (Finset.univ : Finset (Fin m × Fin n × Fin n)) hq
    (fun q _ => Submodule.smul_mem _ _ (hLf_mem _ _ _)) 1 le_rfl
  refine ⟨T, hTS, fun x hx => ?_⟩
  have hg : Formalism.REAL.inUJ ε (S7.toM (x : S7.UJ ε)) := (x : S7.UJ ε).2
  rw [hid _ hg]
  set g := S7.toM (x : S7.UJ ε)
  have hq_norm : ∀ q : Fin m × Fin n × Fin n, ‖hq q g‖ =
      Real.sqrt (C * Formalism.REAL.hs (Y q.1)) * ‖Lf q.2.1 q.2.2 (v q.1) g‖ := by
    intro q
    simp only [hq, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc ‖∑ k, ∑ c, ∑ d, (g * Y k * g⁻¹) c d * Lf c d (v k) g‖
      ≤ ∑ k, ∑ c, ∑ d, ‖(g * Y k * g⁻¹) c d‖ * ‖Lf c d (v k) g‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        rw [norm_mul]
    _ ≤ ∑ k, ∑ c, ∑ d, Real.exp (-τ x) * (Real.sqrt (C * Formalism.REAL.hs (Y k)) * ‖Lf c d (v k) g‖) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hent x k c d hx) (norm_nonneg _)
    _ = Real.exp (-τ x) * ∑ q : Fin m × Fin n × Fin n, ‖hq q g‖ ^ 1 := by
        simp only [pow_one, hq_norm, Finset.mul_sum, Fintype.sum_prod_type]
    _ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h g‖ ^ 1 :=
        mul_le_mul_of_nonneg_left (hT g) (Real.exp_pos _).le
    _ = Real.exp (-τ x) * ∑ h ∈ T, ‖h g‖ := by simp only [pow_one]

end CompanionTheory.RgExh.Dec.L.SA
end
end

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.ChainGen
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem line_deriv (hR : N.RightRule) {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : Formalism.REAL.inG ε A)
    (hexp : ∀ t, ReciprocityTheory.ChartRestriction.DS.inUJ ε (aT A t)) (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : ReciprocityTheory.ChartRestriction.DS.inUJ ε g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => famP σ D E hK.gl χ ss i u (g * aT A s))
      (famP σ D E hK.gl χ ss i (actM (path ⟨D, E, hK.gl⟩ χ ss) A u) (g * aT A t)) t := by
  have hgt : ReciprocityTheory.ChartRestriction.DS.inUJ ε (g * aT A t) := by
    have h2 := hexp t
    unfold ReciprocityTheory.ChartRestriction.DS.inUJ at hg h2 ⊢
    rw [Matrix.conjTranspose_mul]
    calc (aT A t)ᴴ * gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * (g * aT A t)
        = (aT A t)ᴴ * (gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * g) * aT A t := by simp only [Matrix.mul_assoc]
      _ = ReciprocityTheory.ChartRestriction.DS.Jm ε := by rw [hg, h2]
  have h0 := hR n ε H σ D E hK χ ss hU i u A hA (g * aT A t) hgt
  have h1 := HasDerivAt.comp_sub_const (f := fun s : ℝ => (famP σ D E hK.gl χ ss i u)
    (g * aT A t * NormedSpace.exp ((s : ℂ) • A))) t t (by rw [sub_self]; exact h0)
  have hfun : (fun s : ℝ => (famP σ D E hK.gl χ ss i u) (g * aT A t * NormedSpace.exp (((s - t : ℝ) : ℂ) • A))) =
      fun s : ℝ => famP σ D E hK.gl χ ss i u (g * aT A s) := by
    funext s
    unfold aT
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute]
    · rw [← add_smul, ← Complex.ofReal_add, add_comm t (s - t), sub_add_cancel]
    · exact ((Commute.refl A).smul_left _).smul_right _
  have hval : (∑ a, ∑ b, A a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b u) = actM (path ⟨D, E, hK.gl⟩ χ ss) A u := by
    simp [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hval] at h1
  simpa only [hfun] using h1

def wv {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) (k : ℕ) : X.V :=
  ((zs.drop k).map (fun z => actM X A - z • (1 : Module.End ℂ X.V))).prod u

theorem wv_succ {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) (k : ℕ)
    (hk : k < zs.length) :
    actM X A (wv X A zs u (k + 1)) = zs[k] • wv X A zs u (k + 1) + wv X A zs u k := by
  have h : wv X A zs u k = actM X A (wv X A zs u (k + 1)) - zs[k] • wv X A zs u (k + 1) := by
    simp only [wv]
    rw [List.drop_eq_getElem_cons hk, List.map_cons, List.prod_cons, mul_apply_eq_comp, LinearMap.sub_apply,
      LinearMap.smul_apply, one_apply_eq_self]
  rw [h]
  abel

theorem wv_length {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) :
    wv X A zs u zs.length = u := by
  simp [wv]

theorem wv_zero {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ) (hp : p.Monic) (u : X.V) :
    wv X A p.roots.toList u 0 = Polynomial.aeval (actM X A) p u := by
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
  have hl : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      ((p.roots.toList).map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    conv_lhs => rw [← Multiset.coe_toList p.roots]
    rw [Multiset.map_coe, Multiset.prod_coe]
  have key : (p.roots.toList.map (fun z => actM X A - z • (1 : Module.End ℂ X.V))).prod =
      Polynomial.aeval (actM X A) p := by
    conv_rhs => rw [hsplit, hl, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    simp [Algebra.algebraMap_eq_smul_one]
  unfold wv
  rw [List.drop_zero, key]

end CompanionTheory.RgExh.Dec.L.SA
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem hasChar_path (hS : StepChar) {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (h : HasChar X χ) : HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss generalizing X χ with
  | nil => exact h
  | cons s ss ih => exact ih _ _ (hS n X χ s h)

theorem assembly_of : Assembly := by
  intro hSC hAbs hGeo hLF hHaar hPoly hRR hLR hKR hGr hPk
  intro _ n ε H _ _ _ σ D E hK χ ss hU hSq hChar hN
  have hXc : HasChar (path ⟨D, E, hK.gl⟩ χ ss) (pathEnd χ ss) := hasChar_path hSC _ χ ss hChar
  obtain ⟨m, A, τ, c₁, R₀, C, hc₁, hgrad, hτc, hτK, hline, hτadd, hcover, hhs, hcontr⟩ := hGeo n ε
  choose ν hν using fun j => hHaar n ε (A j) (hgrad j)
  choose p hpm hp using fun j => hPoly n ε (path ⟨D, E, hK.gl⟩ χ ss) (pathEnd χ ss) (A j) hXc (hgrad j)
  obtain ⟨M, hM⟩ := hGr n ε H σ D E hK χ ss hU hSq
  apply hPk n ε H σ D E hK χ ss hU
  intro i u

  have hexp : ∀ j t, ReciprocityTheory.ChartRestriction.DS.inUJ ε (aT (A j) t) := fun j t => by
    obtain ⟨y, hy⟩ := hline j 1 t
    have hm : ReciprocityTheory.ChartRestriction.DS.inUJ ε (S7.toM (y : S7.UJ ε)) := (y : S7.UJ ε).2
    rw [hy] at hm
    simpa [show S7.toM (1 : S7.UJ ε) = 1 from rfl] using hm

  have hgline : ∀ j (q : (D × List (Fin n)) × (path ⟨D, E, hK.gl⟩ χ ss).V) (x : S7.UJ ε),
      Continuous fun t : ℝ => gen σ D E hK.gl χ ss q (S7.toM x * aT (A j) t) := fun j q x =>
    continuous_iff_continuousAt.mpr fun t =>
      (line_deriv hRR hK χ ss hU (A j) (hgrad j).1 (hexp j) q.1 q.2 (S7.toM x) x.2 t).continuousAt
  have hcontS : ∀ f ∈ SS σ D E hK.gl χ ss, Continuous fun g : S7.UJ ε => f (S7.toM g) :=
    cont_span (gen σ D E hK.gl χ ss) (fun g : S7.UJ ε => S7.toM g)
      (fun q => (hKR n ε H σ D E hK χ ss hU q.1 q.2).1)
  have hdomS : ∀ f ∈ SS σ D E hK.gl χ ss, ∃ (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ),
      (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧ ∀ (g : S7.UJ ε) (k k' : S7.KG ε),
        ‖f (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2 := by
    intro f hf
    obtain ⟨T, Cf, hTS, hb⟩ := dom_span (gen σ D E hK.gl χ ss)
      (fun b : S7.UJ ε × S7.KG ε × S7.KG ε => S7.toMK b.2.1 * S7.toM b.1 * S7.toMK b.2.2)
      (fun b : S7.UJ ε × S7.KG ε × S7.KG ε => S7.toM b.1)
      (fun q => by
        obtain ⟨T, Cf, h⟩ := (hKR n ε H σ D E hK χ ss hU q.1 q.2).2
        exact ⟨T, Cf, fun b => h b.1 b.2.1 b.2.2⟩) f hf
    exact ⟨T, Cf, hTS, fun g k k' => hb (g, k, k')⟩
  have hchainS : ∀ f ∈ SS σ D E hK.gl χ ss, ∀ j, ∃ (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)), Chain ε (SS σ D E hK.gl χ ss) (A j) ((p j).roots.toFinset) f f₀ ∧
        (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧ ∀ x : PSub ε (A j), 0 ≤ τ j x →
          ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := by
    intro f hf j
    set zs := (p j).roots.toList with hzs
    have hQ := chain_span (gen σ D E hK.gl χ ss) ε (A j) (τ j) zs.length (fun k => zs[(k : ℕ)]'k.isLt)
      (fun q => by
        refine ⟨fun k => famP σ D E hK.gl χ ss q.1 (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 (k : ℕ)),
          fun k => gen_mem σ D E hK.gl χ ss _ _, ?_, ?_, ?_⟩
        · show famP σ D E hK.gl χ ss q.1 (wv _ (A j) zs q.2 (Fin.last zs.length : ℕ)) = _
          rw [Fin.val_last, wv_length]
          rfl
        · intro k g t hg
          have hd := line_deriv hRR hK χ ss hU (A j) (hgrad j).1 (hexp j) q.1
            (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 ((k : ℕ) + 1)) g hg t
          rw [wv_succ _ (A j) zs q.2 k k.isLt, LinearMap.map_add, LinearMap.map_smul] at hd
          simpa only [aT, Fin.val_succ, Fin.val_castSucc, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul] using hd
        · obtain ⟨m', Y, v, hY, hpu⟩ := hp j q.2
          obtain ⟨T, hTS, hT⟩ := source_gen hLR hK χ ss hU (A j) (τ j) C (hcontr j) q.1 m' Y v hY
          refine ⟨T, hTS, fun x hx => ?_⟩
          have e : wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 ((0 : Fin (zs.length + 1)) : ℕ) =
              ∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k) := by
            rw [Fin.val_zero, hzs, wv_zero _ (A j) (p j) (hpm j) q.2, hpu]
          show ‖famP σ D E hK.gl χ ss q.1 (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2
            ((0 : Fin (zs.length + 1)) : ℕ)) (S7.toM (x : S7.UJ ε))‖ ≤ _
          rw [e]
          exact hT x hx) f hf
    obtain ⟨F, hFS, hFl, hFd, T, hTS, hT⟩ := hQ
    refine ⟨F 0, T, ⟨zs.length, fun k => zs[(k : ℕ)]'k.isLt, F, fun k => ?_, hFS, hFl, rfl, hFd⟩, hTS, hT⟩
    exact Multiset.mem_toFinset.mpr (Multiset.mem_toList.mp (List.getElem_mem _))
  have hqualS : ∀ f ∈ SS σ D E hK.gl χ ss, ∀ j, ∀ᵐ (x : PSub ε (A j)) ∂(ν j), (∫⁻ t in Set.Ioi (0 : ℝ),
      ‖f (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (rhoA (A j) + 1) * t))) < ⊤ := by
    intro f hf j
    refine ae_lint_span (gen σ D E hK.gl χ ss) (ν j) (volume.restrict (Set.Ioi (0 : ℝ)))
      (fun (x : PSub ε (A j)) (t : ℝ) => S7.toM (x : S7.UJ ε) * aT (A j) t)
      (fun t => ENNReal.ofReal (Real.exp (2 * (rhoA (A j) + 1) * t))) ?_ ?_ f hf
    · intro f' hf' x
      have hc := cont_span (gen σ D E hK.gl χ ss) (fun t : ℝ => S7.toM (x : S7.UJ ε) * aT (A j) t)
        (fun q => hgline j q (x : S7.UJ ε)) f' hf'
      exact ((continuous_enorm.comp hc).measurable.pow_const 2).mul
        (Measurable.ennreal_ofReal (by fun_prop)) |>.aemeasurable
    · intro q
      have h := hN (A j) (muPar ε (A j) (ν j)) (hgrad j) ⟨ν j, rfl, hν j⟩ q.2
      simp only [NSet, Set.mem_ofPred_eq] at h
      have h2 : ∀ᵐ y ∂((ν j).map Subtype.val), lineInt ε (famP σ D E hK.gl χ ss q.1 q.2) (A j) (-rhoA (A j) - 1) y < ⊤ :=
        h q.1
      have h3 := ae_of_ae_map measurable_subtype_coe.aemeasurable h2
      filter_upwards [h3] with x hx
      have e : ∀ t : ℝ, -2 * (-rhoA (A j) - 1) * t = 2 * (rhoA (A j) + 1) * t := fun t => by ring
      simp only [lineInt, e] at hx
      exact hx
  have hlevelS : ∀ f ∈ SS σ D E hK.gl χ ss, LevelF ε f (-M) := by
    intro f hf
    have hhs : Continuous fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) := by
      unfold Formalism.REAL.hs
      have := S7.continuous_toM ε
      fun_prop
    exact lint_span (gen σ D E hK.gl χ ss) Measure.haar (fun g : S7.UJ ε => S7.toM g)
      (fun g => ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-M)))
      (fun f' hf' => (((continuous_enorm.comp (hcontS f' hf')).measurable.pow_const 2).mul
        (hhs.measurable.pow_const (-M)).ennreal_ofReal).aemeasurable)
      (fun q => hM q.1 q.2) f hf
  have key := hAbs n ε (SS σ D E hK.gl χ ss) m A ν τ (fun j => rhoA (A j)) (fun j => (p j).roots.toFinset) M c₁ R₀ C
    hc₁ (fun j => hLF n ε (A j) (ν j) (τ j) (hgrad j) (hν j) (hτc j) (fun x t y hy => hτadd j x t y hy))
    hτc hτK (fun j x t => by obtain ⟨y, hy⟩ := hline j x t; exact ⟨y, hy, hτadd j x t y hy⟩)
    hcover hhs hcontS hdomS hchainS hqualS hlevelS
  exact key _ (gen_mem σ D E hK.gl χ ss i u)

end CompanionTheory.RgExh.Dec.L.SA
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatement
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.PathGrowth

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def Lev (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  (Continuous fun g : S7.UJ ε => f (S7.toM g)) ∧ LevelF ε f (-(m : ℝ))

theorem hs_nonneg (h : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem row_le_hs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ∑ i, ‖h j i‖ ^ 2 ≤ Formalism.REAL.hs h :=
  Finset.single_le_sum (f := fun a => ∑ i, ‖h a i‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

theorem row_cs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) :
    ‖∑ i, h j i * a i‖ ^ 2 ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, h j i * a i‖ ≤ ∑ i, ‖h j i‖ * ‖a i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
  have h2 : (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖∑ i, h j i * a i‖ ^ 2 ≤ (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 := h2
    _ ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (row_le_hs h j) (Finset.sum_nonneg fun _ _ => by positivity)

theorem row_bound (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) (m : ℕ) :
    ‖∑ i, h j i * a i‖ ^ 2 * Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) ≤
      ∑ i, ‖a i‖ ^ 2 * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
  have hs0 := hs_nonneg h
  have hT : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hcs := row_cs h j a
  rw [← Finset.sum_mul]
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul] at hcs
    have hz : ‖∑ i, h j i * a i‖ ^ 2 = 0 := le_antisymm hcs (by positivity)
    rw [hz, zero_mul]
    exact mul_nonneg hT (Real.rpow_nonneg hs0 _)
  · have e : Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) = Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹ := by
      rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add hpos, Real.rpow_neg_one]
    have hr := Real.rpow_nonneg hs0 (-(m : ℝ))
    rw [e]
    calc ‖∑ i, h j i * a i‖ ^ 2 * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹)
        ≤ (Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2) * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹) :=
          mul_le_mul_of_nonneg_right hcs (by positivity)
      _ = (∑ i, ‖a i‖ ^ 2) * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
          field_simp

theorem enorm_sq_mul (x : ℂ) (r : ℝ) :
    ‖x‖ₑ ^ 2 * ENNReal.ofReal r = ENNReal.ofReal (‖x‖ ^ 2 * r) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem continuous_hs (ε : Fin n → Bool) : Continuous fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) := by
  unfold Formalism.REAL.hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((S7.continuous_toM ε).matrix_elem i j).norm).pow 2

theorem measurable_term (ε : Fin n → Bool) {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (s : ℝ)
    (hf : Continuous fun g : S7.UJ ε => f (S7.toM g)) :
    Measurable fun g : S7.UJ ε => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) :=
  (hf.measurable.enorm.pow_const 2).mul
    (ENNReal.measurable_ofReal.comp ((continuous_hs ε).measurable.pow_const s))

theorem lev_row (ε : Fin n → Bool) (m : ℕ) (f : Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : ∀ i, Lev ε m (f i)) (j : Fin n) : Lev ε (m + 1) fun g => ∑ i, g j i * f i g := by
  refine ⟨continuous_finsetSum _ fun i _ =>
    ((S7.continuous_toM ε).matrix_elem j i).mul (hf i).1, ?_⟩
  unfold LevelF
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (b := ∫⁻ g : S7.UJ ε, ∑ i,
    ‖f i (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-(m : ℝ))) ∂Measure.haar) ?_
  · have hr := fun k : ℝ => Real.rpow_nonneg (hs_nonneg (S7.toM g)) k
    simp only [enorm_sq_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => mul_nonneg (by positivity) (hr _)]
    exact ENNReal.ofReal_le_ofReal (row_bound _ j _ m)
  · rw [lintegral_finsetSum _ fun i _ => measurable_term ε _ (hf i).1]
    exact ENNReal.sum_lt_top.2 fun i _ => (hf i).2

theorem level_zero_of_memLp (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂Measure.haar < ⊤ := by
  let μ : Measure (S7.UJ ε) := Formalism.REAL.muG ε
  haveI : μ.IsHaarMeasure := Formalism.REAL.instIsHaarMuG n ε
  have h' : MemLp (fun g : S7.UJ ε => F (S7.toM g)) 2 μ := h
  have h2 : ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂μ < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
        (p := 2) two_ne_zero ENNReal.ofNat_ne_top h'.eLpNorm_lt_top
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure (S7.UJ ε)) μ, lintegral_smul_measure]
  exact ENNReal.mul_lt_top (by simp) h2

theorem lev_base (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (ξ : H)
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hsq : Formalism.MainNotions.S.IsSqIntOn ε σ) (u : D) :
    Lev ε 0 (baseCoef σ D ξ u) := by
  constructor
  · have h1 : Continuous fun g : S7.UJ ε => σ (S7.toM g) (u : H) :=
      (hσ.2.2 (u : H)).comp_continuous (S7.continuous_toM ε) fun g => g.2
    exact continuous_const.inner h1
  · unfold LevelF
    have := level_zero_of_memLp ε (baseCoef σ D ξ u) (hsq (u : H) ξ)
    simpa using this

theorem lev_path (ε : Fin n → Bool) : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)) (m : ℕ),
    (∀ u, Lev ε m (c u)) → ∀ u, Lev ε (m + ss.length) (pathCoef X c χ ss js u)
  | [], _, _, _, _, _, h, u => h u
  | s :: ss, X, c, χ, js, m, h, u => by
    have key := lev_path ε ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail (m + 1)
      (fun w => lev_row ε m (fun i => c ((show stepSub X (χ s) from w).1 i)) (fun i => h _) (js.headD s)) u
    rw [show m + (s :: ss).length = m + 1 + ss.length by simp only [List.length_cons]; omega]
    exact key

theorem growth : Growth := by
  intro n ε H _ _ _ σ D E hK χ ss hσ hsq
  refine ⟨(ss.length : ℝ), fun i u => ?_⟩
  have key := lev_path ε ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 0
    (fun u => lev_base ε σ D _ hσ hsq u) u
  rw [zero_add] at key
  exact key.2

end GlobalTheory.CompanionTheory.PathGrowth
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatementStatement
theorem _root_.GlobalTheory.T.GrowthStatement : CompanionTheory.RgExh.Dec.L.Growth :=
  GlobalTheory.CompanionTheory.PathGrowth.growth
end
end

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.BackOf
namespace CompanionTheory.RgExh.Dec.L

open CompanionTheory.RgExh

theorem back_of (hA : Assembly) (h1 : AbsoluteL2Bound) (h2 : Geo) (h3 : LineFormula) (h4 : HaarExists) (h5 : PolyNilPath)
    (h6 : N.RightRule) (h7 : N.LeftRule) (h8 : KRight) (h9 : Growth) (h10 : Pack) : Back :=
  fun h0 => hA h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h0

end CompanionTheory.RgExh.Dec.L
end

namespace CompanionTheory.RgExh.Dec.L

theorem back_of_inputs (hLF : LineFormula) (hPN : PolyNilPath) : Back :=
  back_of CompanionTheory.RgExh.Dec.L.SA.assembly_of CompanionTheory.RgExh.Dec.L.AB.absolute_l2_bound GlobalTheory.T.GeometricStatement hLF GlobalTheory.T.HaarExistence hPN GlobalTheory.T.NilpotentRightRule GlobalTheory.T.NilpotentLeftRule
    CompanionTheory.RgExh.Dec.L.WyKR.kRight GlobalTheory.T.GrowthStatement GlobalTheory.T.rgExh_pack

theorem back_of_lineFormula (hLF : LineFormula) : Back := back_of_inputs hLF GlobalTheory.T.PolynomialNilpotentPath

theorem backward_of_line_formula : Back := back_of_lineFormula CompanionTheory.RgExh.Dec.N.S.line_formula

end CompanionTheory.RgExh.Dec.L
