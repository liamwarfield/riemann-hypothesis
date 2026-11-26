module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetReNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedSumDriftInequality
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem driftWeight_sq_le (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (r i j : ℕ) (hj : 0 < j) (hji : j ≤ i)
    (hr : i + j ≤ r) :
    (ε ^ (i * (r - i))) ^ 2 ≤
      ε ^ 2 * (ε ^ ((i - j) * (r - (i - j))) * ε ^ ((i + j) * (r - (i + j)))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hji
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  have e1 : j + m + j + k - (j + m) = j + k := by omega
  have e2 : j + m - j = m := by omega
  have e3 : j + m + j + k - m = j + j + k := by omega
  have e4 : j + m + j + k - (j + m + j) = k := by omega
  rw [e1, e2, e3, e4, ← pow_add, ← pow_add, ← pow_mul]
  apply pow_le_pow_of_le_one h0 h1
  nlinarith [Nat.mul_le_mul hj hj]

theorem mul_sqrt_le_of_weights (x e₁ e₂ ε u v M : ℝ) (hx : 0 ≤ x) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : x ^ 2 ≤ ε ^ 2 * (e₁ * e₂))
    (h₁ : e₁ * u ≤ M) (h₂ : e₂ * v ≤ M) : x * Real.sqrt (u * v) ≤ ε * M := by
  have hM : 0 ≤ M := le_trans (mul_nonneg he₁ hu) h₁
  have hs0 := Real.sqrt_nonneg (u * v)
  have k3 : (x * Real.sqrt (u * v)) ^ 2 ≤ (ε * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hu hv)]
    calc x ^ 2 * (u * v) ≤ ε ^ 2 * (e₁ * e₂) * (u * v) :=
          mul_le_mul_of_nonneg_right h (mul_nonneg hu hv)
      _ = ε ^ 2 * ((e₁ * u) * (e₂ * v)) := by ring
      _ ≤ ε ^ 2 * (M * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (mul_nonneg he₂ hv) hM) (sq_nonneg ε)
      _ = (ε * M) ^ 2 := by ring
  nlinarith [mul_nonneg hx hs0, mul_nonneg hε hM]

theorem weighted_sum_drift_inequality : (∀ (Y σ : Type) [Fintype σ] (r : ℕ) (t : σ → Y → Y) (α : ℕ → Y → ℝ) (c C B : ℝ), 0 ≤ c → c < 1 → 0 ≤ C → (∀ i ≤ r, ∀ y, 0 ≤ α i y) → (∀ y, α 0 y ≤ B ∧ α r y ≤ B) → (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y)) → ∃ (e : ℕ → ℝ) (c' b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c' ∧ c' < 1 ∧ 0 ≤ b ∧ ∀ y, ∑ s, (∑ i ∈ Finset.Ioo 0 r, e i * α i (t s y)) ≤ Fintype.card σ * (c' * (∑ i ∈ Finset.Ioo 0 r, e i * α i y) + b)) := by
  intro Y σ _ r t α c C B hc0 hc1 hC hα hB halt
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  obtain ⟨ε, hε0, hε1, hkey⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (r : ℝ) * C * ε < 1 - c := by
    have hden : 0 < 2 * ((r : ℝ) * C + 1) := by linarith
    refine ⟨(1 - c) / (2 * ((r : ℝ) * C + 1)), div_pos (by linarith) hden, ?_, ?_⟩
    · rw [div_le_one hden]
      linarith
    · have hεe : (1 - c) / (2 * ((r : ℝ) * C + 1)) * (2 * ((r : ℝ) * C + 1)) = 1 - c :=
        div_mul_cancel₀ _ hden.ne'
      have hpos : 0 < (1 - c) / (2 * ((r : ℝ) * C + 1)) := div_pos (by linarith) hden
      nlinarith [mul_nonneg hrC hpos.le]
  refine ⟨fun i => ε ^ (i * (r - i)), c + (r : ℝ) * C * ε, 2 * (r : ℝ) * C * ε * max B 0,
    fun i => pow_pos hε0 _, add_nonneg hc0 (mul_nonneg hrC hε0.le), by linarith,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg r)) hC) hε0.le)
      (le_max_right _ _), ?_⟩
  intro y
  dsimp only
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = ∑ i ∈ Finset.Ioo 0 r, ε ^ (i * (r - i)) * α i y := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦ]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (pow_nonneg hε0.le _) (hα i (Finset.mem_Ioo.1 hi).2.le y)
  have hB0 : 0 ≤ B := le_trans (hα 0 (Nat.zero_le _) y) (hB y).1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Φ + 2 * B := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hbd : ∀ k ≤ r, ε ^ (k * (r - k)) * α k y ≤ M := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, zero_mul, pow_zero, one_mul]
      linarith [(hB y).1]
    rcases eq_or_lt_of_le hk with hkr | hkr
    · rw [hkr, Nat.sub_self, mul_zero, pow_zero, one_mul]
      linarith [(hB y).2]
    · have h1 : ε ^ (k * (r - k)) * α k y ≤ Φ := by
        rw [hΦ]
        exact Finset.single_le_sum (f := fun i => ε ^ (i * (r - i)) * α i y)
          (fun i hi => mul_nonneg (pow_nonneg hε0.le _) (hα i (Finset.mem_Ioo.1 hi).2.le y))
          (Finset.mem_Ioo.2 ⟨hk0, hkr⟩)
      linarith
  have hterm : ∀ i ∈ Finset.Ioo 0 r, ∑ s, ε ^ (i * (r - i)) * α i (t s y) ≤
      (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) + (Fintype.card σ : ℝ) * (C * ε * M) := by
    intro i hi
    obtain ⟨hi0, hir⟩ := Finset.mem_Ioo.1 hi
    have hA : 0 ≤ (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 (mul_nonneg (pow_nonneg hε0.le _) (hα i hir.le y)))
    have hB' : 0 ≤ (Fintype.card σ : ℝ) * (C * ε * M) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC hε0.le) hM0)
    rcases halt y i hi0 hir with hcon | ⟨j, hj0, hji, hjr, hint⟩
    · rw [← Finset.mul_sum]
      calc ε ^ (i * (r - i)) * ∑ s, α i (t s y)
          ≤ ε ^ (i * (r - i)) * ((Fintype.card σ : ℝ) * (c * α i y)) :=
            mul_le_mul_of_nonneg_left hcon (pow_nonneg hε0.le _)
        _ = (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) := by ring
        _ ≤ _ := le_add_of_nonneg_right hB'
    · have hs : ∀ s, ε ^ (i * (r - i)) * α i (t s y) ≤ C * ε * M := by
        intro s
        have h1 := driftWeight_sq_le ε hε0.le hε1 r i j hj0 hji hjr
        have h2 := mul_sqrt_le_of_weights (ε ^ (i * (r - i))) (ε ^ ((i - j) * (r - (i - j))))
          (ε ^ ((i + j) * (r - (i + j)))) ε (α (i - j) y) (α (i + j) y) M (pow_nonneg hε0.le _)
          (pow_nonneg hε0.le _) (pow_nonneg hε0.le _) hε0.le (hα _ (by omega) y) (hα _ hjr y) h1
          (hbd _ (by omega)) (hbd _ hjr)
        calc ε ^ (i * (r - i)) * α i (t s y)
            ≤ ε ^ (i * (r - i)) * (C * Real.sqrt (α (i - j) y * α (i + j) y)) :=
              mul_le_mul_of_nonneg_left (hint s) (pow_nonneg hε0.le _)
          _ = C * (ε ^ (i * (r - i)) * Real.sqrt (α (i - j) y * α (i + j) y)) := by ring
          _ ≤ C * (ε * M) := mul_le_mul_of_nonneg_left h2 hC
          _ = C * ε * M := by ring
      calc ∑ s, ε ^ (i * (r - i)) * α i (t s y) ≤ ∑ _s : σ, C * ε * M :=
            Finset.sum_le_sum fun s _ => hs s
        _ = (Fintype.card σ : ℝ) * (C * ε * M) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ _ := le_add_of_nonneg_left hA
  have hcard : ((Finset.Ioo 0 r).card : ℝ) ≤ r := by
    exact_mod_cast (by rw [Nat.card_Ioo]; omega)
  rw [Finset.sum_comm]
  calc ∑ i ∈ Finset.Ioo 0 r, ∑ s, ε ^ (i * (r - i)) * α i (t s y)
      ≤ ∑ i ∈ Finset.Ioo 0 r, ((Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) +
          (Fintype.card σ : ℝ) * (C * ε * M)) := Finset.sum_le_sum hterm
    _ = (Fintype.card σ : ℝ) * (c * Φ) + ((Finset.Ioo 0 r).card : ℝ) * ((Fintype.card σ : ℝ) * (C * ε * M)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, hΦ]
    _ ≤ (Fintype.card σ : ℝ) * (c * Φ) + (r : ℝ) * ((Fintype.card σ : ℝ) * (C * ε * M)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC hε0.le) hM0)))
    _ = (Fintype.card σ : ℝ) * ((c + (r : ℝ) * C * ε) * Φ + 2 * (r : ℝ) * C * ε * max B 0) := by
        rw [max_eq_left hB0, hM]
        ring
    _ = _ := by rw [hΦ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SubspaceSupAlternative
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem subspace_sup_alternative :
    (∀ (K V Y σ : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype σ] (r : ℕ) (t : σ → Y → Y) (D : Y → Submodule K V → ℝ) (α : ℕ → Y → ℝ) (c Ω : ℝ), Module.finrank K V = r → 1 ≤ Ω → (∀ y W, 0 < D y W) → (∀ i ≤ r, ∀ y, IsLUB (D y '' {W | Module.finrank K W = i}) (α i y)) → (∀ y W₁ W₂, D y W₁ * D y W₂ ≤ D y (W₁ ⊓ W₂) * D y (W₁ ⊔ W₂)) → (∀ s y W, D (t s y) W ≤ Ω * D y W ∧ D y W ≤ Ω * D (t s y) W) → (∀ y W, W ≠ ⊥ → W ≠ ⊤ → ∑ s, D (t s y) W ≤ Fintype.card σ * (c * D y W)) → ∃ C : ℝ, 0 ≤ C ∧ (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y))) := by
  intro K V Y σ _ _ _ _ _ r t D α c Ω hr hΩ hpos hlub hsub hmove hcon
  have hΩ0 : 0 < Ω := by linarith
  refine ⟨2 * Ω ^ 3, by positivity, fun y i hi0 hir => ?_⟩
  have hle : ∀ k ≤ r, ∀ z (W : Submodule K V), Module.finrank K W = k → D z W ≤ α k z :=
    fun k hk z W hW => (hlub k hk z).1 ⟨W, hW, rfl⟩
  have hub : ∀ k ≤ r, ∀ z (b : ℝ), (∀ W : Submodule K V, Module.finrank K W = k → D z W ≤ b) →
      α k z ≤ b := fun k hk z b hb => (hlub k hk z).2 (by
        rintro _ ⟨W, hW, rfl⟩
        exact hb W hW)
  have hex : ∀ b < α i y, ∃ W : Submodule K V, Module.finrank K W = i ∧ b < D y W := by
    intro b hb
    by_contra h
    push Not at h
    exact absurd (hub i hir.le y b h) (not_le.2 hb)
  have hA : 0 < α i y := by
    obtain ⟨W, hW, -⟩ := hex (α i y - 1) (by linarith)
    exact (hpos y W).trans_le (hle i hir.le y W hW)
  set A := α i y with hAdef
  set B := A / (2 * Ω ^ 2) with hBdef
  have hB0 : 0 < B := by positivity
  have hAB : A = 2 * Ω ^ 2 * B := by rw [hBdef]; field_simp
  have hBA : B < A := by
    have : 1 ≤ Ω ^ 2 := one_le_pow₀ hΩ
    nlinarith
  obtain ⟨W₀, hW₀, hBW₀⟩ := hex B hBA
  by_cases hcase : ∀ W : Submodule K V, Module.finrank K W = i → B < D y W → W = W₀
  · left
    have h0 : A = D y W₀ := by
      refine le_antisymm (hub i hir.le y _ fun W hW => ?_) (hle i hir.le y W₀ hW₀)
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · exact (not_lt.1 h).trans hBW₀.le
    have h1 : ∀ s, α i (t s y) ≤ D (t s y) W₀ := by
      intro s
      refine hub i hir.le _ _ fun W hW => ?_
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · have a1 := (hmove s y W).1
        have a2 := (hmove s y W₀).2
        have a3 : Ω * D y W ≤ Ω * B := mul_le_mul_of_nonneg_left (not_lt.1 h) hΩ0.le
        have a4 : Ω * (Ω * B) ≤ Ω * D (t s y) W₀ := by
          have : 0 < Ω ^ 2 * B := by positivity
          nlinarith
        have a5 := le_of_mul_le_mul_left a4 hΩ0
        linarith
    have hb : W₀ ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hW₀
      omega
    have ht : W₀ ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hW₀
      omega
    rw [h0]
    exact (Finset.sum_le_sum fun s _ => h1 s).trans (hcon y W₀ hb ht)
  · right
    push Not at hcase
    obtain ⟨W₁, hW₁, hBW₁, hne⟩ := hcase
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₀
    have hlt : Module.finrank K ↥(W₁ ⊓ W₀) < i := by
      rw [← hW₁]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hne ?_)
      exact Submodule.eq_of_le_of_finrank_eq (inf_eq_left.1 h) (hW₁.trans hW₀.symm)
    have hsr : Module.finrank K ↥(W₁ ⊔ W₀) ≤ r := hr ▸ Submodule.finrank_le _
    refine ⟨i - Module.finrank K ↥(W₁ ⊓ W₀), by omega, by omega, by omega, fun s => ?_⟩
    set j := i - Module.finrank K ↥(W₁ ⊓ W₀) with hj
    have e1 : D y (W₁ ⊓ W₀) ≤ α (i - j) y := hle _ (by omega) y _ (by omega)
    have e2 : D y (W₁ ⊔ W₀) ≤ α (i + j) y := hle _ (by omega) y _ (by omega)
    have e3 : B ^ 2 ≤ α (i - j) y * α (i + j) y := by
      calc B ^ 2 = B * B := sq B
        _ ≤ D y W₁ * D y W₀ := mul_le_mul hBW₁.le hBW₀.le hB0.le (hpos _ _).le
        _ ≤ _ := hsub y W₁ W₀
        _ ≤ _ := mul_le_mul e1 e2 (hpos _ _).le ((hpos _ _).le.trans e1)
    have e4 : B ≤ Real.sqrt (α (i - j) y * α (i + j) y) := Real.le_sqrt_of_sq_le e3
    have e5 : α i (t s y) ≤ Ω * A := hub i hir.le _ _ fun W hW =>
      (hmove s y W).1.trans (mul_le_mul_of_nonneg_left (hle i hir.le y W hW) hΩ0.le)
    calc α i (t s y) ≤ Ω * A := e5
      _ = 2 * Ω ^ 3 * B := by rw [hAB]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedHeightSupDriftOrthonormalFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma nonneg_of_isLUB_image {β : Type} {f : β → ℝ} {s : Set β} {a : ℝ} (hf : ∀ b, 0 ≤ f b)
    (h : IsLUB (f '' s) a) : 0 ≤ a := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · have : a ≤ a - 1 := h.2 (by simp)
    linarith
  · exact (hf b).trans (h.1 ⟨b, hb, rfl⟩)

theorem weighted_sup_drift_on_orthonormal_frames :
    (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∃ (e : ℕ → ℝ) (c b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ ∀ x, IsOrth X x → ∑ a ∈ S, (∑ i ∈ Finset.Ioo 0 r, e i * α i (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) ≤ S.card * (c * (∑ i ∈ Finset.Ioo 0 r, e i * α i x) + b)) := by
  intro r X d hd τ0 S hS hirr hU
  obtain ⟨δ, c, Ω, hδ, hc0, hc1, hΩ, hw⟩ := GlobalTheory.height_rpow_neg_distortion_contraction r X d hd τ0 S hS hirr
  refine ⟨δ, hδ, fun α hα => ?_⟩
  have hdet : ∀ y : {x // IsOrth X x}, ∀ τ : X.Ψ, (mat y.1 τ).det ≠ 0 :=
    fun y => (GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X y.1 y.2).1
  have hpos : ∀ y : {x // IsOrth X x}, ∀ W, 0 < d y.1 W := fun y W => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.HeightLower.exists_pos_le_height r X d hd y.1 (hdet y)
    exact hm.trans_le (h W)
  let t : S → {x // IsOrth X x} → {x // IsOrth X x} := fun a y =>
    ⟨_, isOrth_update_mul_inv r X τ0 y.1 a.1 y.2 (hU a.1 a.2)⟩
  have hfr : Module.finrank E (Fin r → E) = r := by simp
  obtain ⟨C, hC, halt⟩ := GlobalTheory.subspace_sup_alternative E (Fin r → E) {x // IsOrth X x} S r t
    (fun y W => d y.1 W ^ (-δ)) (fun i y => α i y.1) c Ω hfr hΩ
    (fun y W => Real.rpow_pos_of_pos (hpos y W) _)
    (fun i hi y => hα i hi y.1 (hdet y))
    (fun y W₁ W₂ => by
      have h := GlobalTheory.HeightSubmodular.height_submodular r X d hd y.1 (hdet y) W₁ W₂
      rw [← Real.mul_rpow (hpos y _).le (hpos y _).le, ← Real.mul_rpow (hpos y _).le (hpos y _).le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos (hpos y _) (hpos y _)) h (by linarith))
    (fun s y W => (hw y.1 (hdet y) W).1 s.1 s.2)
    (fun y W h0 h1 => by
      have h := (hw y.1 (hdet y) W).2 h0 h1
      rw [← Finset.sum_coe_sort] at h
      rw [Fintype.card_coe]
      exact h)
  obtain ⟨m, hm, htop⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_bot_top r X d hd
  obtain ⟨e, c', b, he, hc'0, hc'1, hb, hdr⟩ := GlobalTheory.weighted_sum_drift_inequality
    {x // IsOrth X x} S r t (fun i y => α i y.1) c C (m ^ (-δ)) hc0 hc1 hC
    (fun i hi y => nonneg_of_isLUB_image (fun W => (Real.rpow_pos_of_pos (hpos y W) _).le)
      (hα i hi y.1 (hdet y)))
    (fun y => by
      constructor
      · refine (hα 0 (Nat.zero_le r) y.1 (hdet y)).2 ?_
        rintro _ ⟨W, hW, rfl⟩
        have hW' : W = ⊥ := Submodule.finrank_eq_zero.1 hW
        subst hW'
        exact Real.rpow_le_rpow_of_nonpos hm (htop y.1 y.2).1 (by linarith)
      · refine (hα r le_rfl y.1 (hdet y)).2 ?_
        rintro _ ⟨W, hW, rfl⟩
        have hW' : W = ⊤ := Submodule.eq_top_of_finrank_eq (hW.trans hfr.symm)
        subst hW'
        exact Real.rpow_le_rpow_of_nonpos hm (htop y.1 y.2).2 (by linarith))
    halt
  refine ⟨e, c', b, he, hc'0, hc'1, hb, fun x hx => ?_⟩
  have h := hdr ⟨x, hx⟩
  rw [Fintype.card_coe] at h
  rw [← Finset.sum_coe_sort]
  exact h

end GlobalTheory.FiniteCovolume
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedHeightSupDriftOrthonormalFramesStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.weighted_height_sup_drift_orthonormal_frames : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∃ (e : ℕ → ℝ) (c b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ ∀ x, IsOrth X x → ∑ a ∈ S, (∑ i ∈ Finset.Ioo 0 r, e i * α i (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) ≤ S.card * (c * (∑ i ∈ Finset.Ioo 0 r, e i * α i x) + b)) := by
  first | exact @GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames | exact GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames | (intros; apply GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames <;> assumption)
end
