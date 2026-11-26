module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IntegrableOfLtTop

@[expose] public section

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.AbsoluteL2OfLineChain
section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.LineCurve
section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.ContinuousHs
section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.HsConjTranspose
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem one_le_hs (hn : 0 < n) (g : S7.UJ ε) : 1 ≤ Formalism.REAL.hs (S7.toM g) := by
  have hU : (S7.toM g)ᴴ * Jm ε * S7.toM g = Jm ε := g.2
  have hs1 : ∀ a : Fin n, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := by
    intro a
    split <;> simp
  have h00 := congrFun (congrFun hU ⟨0, hn⟩) ⟨0, hn⟩
  rw [Matrix.mul_apply] at h00
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h00
  calc (1 : ℝ) = ‖(if ε ⟨0, hn⟩ = true then (1 : ℂ) else -1)‖ := (hs1 _).symm
    _ = ‖∑ j, star (S7.toM g j ⟨0, hn⟩) * (if ε j = true then (1 : ℂ) else -1) *
          S7.toM g j ⟨0, hn⟩‖ := by rw [h00]
    _ ≤ ∑ j, ‖star (S7.toM g j ⟨0, hn⟩) * (if ε j = true then (1 : ℂ) else -1) *
          S7.toM g j ⟨0, hn⟩‖ := norm_sum_le _ _
    _ = ∑ j, ‖S7.toM g j ⟨0, hn⟩‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, norm_mul, norm_star, hs1]
        ring
    _ ≤ ∑ j, ∑ k, ‖S7.toM g j k‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => Finset.single_le_sum (f := fun k => ‖S7.toM g j k‖ ^ 2)
          (fun k _ => by positivity) (Finset.mem_univ _)
    _ = Formalism.REAL.hs (S7.toM g) := rfl

private theorem hs_eq_re_trace_conjTranspose_mul' (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs X = (Matrix.trace (X * Xᴴ)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.re_sum, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.ofReal_re]

theorem hs_mul_K (X : Matrix (Fin n) (Fin n) ℂ) (k : S7.KG ε) : Formalism.REAL.hs (X * S7.toMK k) = Formalism.REAL.hs X := by
  have hk : S7.toM (k : S7.UJ ε) ∈ Kset ε := k.2
  obtain ⟨hu, -⟩ : S7.toM (k : S7.UJ ε) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      S7.toM (k : S7.UJ ε) * Jm ε = Jm ε * S7.toM (k : S7.UJ ε) := hk
  have hUU : S7.toMK k * (S7.toMK k)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (S7.toMK k), hUU, Matrix.one_mul]

theorem continuous_aT (A : Matrix (Fin n) (Fin n) ℂ) : Continuous (fun t : ℝ => aT A t) := by
  have h1 : Continuous fun t : ℝ => (t : ℂ) • A := by fun_prop
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  show Continuous fun t : ℝ => NormedSpace.exp ((t : ℂ) • A)
  exact NormedSpace.exp_continuous.comp h1

end CompanionTheory.RgExh.Dec.L.AB
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

structure Hyp {n : ℕ} (ε : Fin n → Bool) (S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (m : ℕ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (ν : ∀ j, Measure (PSub ε (A j))) (τ : Fin m → S7.UJ ε → ℝ)
    (r : Fin m → ℝ) (Z : Fin m → Finset ℂ) (M c₁ R₀ C : ℝ) : Prop where
  c1pos : 0 < c₁
  formula : ∀ j, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable (fun g : S7.UJ ε => F (S7.toM g)) → (∀ (g : S7.UJ ε) (k : S7.KG ε), F (S7.toM g * S7.toMK k) = F (S7.toM g)) →
      ∫⁻ g : S7.UJ ε, F (S7.toM g) ∂Measure.haar = κ * ∫⁻ x in {x : PSub ε (A j) | τ j x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j)
  tauCont : ∀ j, Continuous (τ j)
  tauInv : ∀ j (x y : PSub ε (A j)) (k : S7.KG ε), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * S7.toMK k → τ j y = τ j x
  lines : ∀ j (x : PSub ε (A j)) (t : ℝ), ∃ y : PSub ε (A j), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT (A j) t ∧
      τ j y = τ j x + t
  cover : ∃ U : Fin m → Set (S7.UJ ε), (∀ j, MeasurableSet (U j)) ∧ (∀ j g (k : S7.KG ε), g ∈ U j → g * (k : S7.UJ ε) ∈ U j) ∧
      (∀ g : S7.UJ ε, R₀ < Formalism.REAL.hs (S7.toM g) → ∃ j, g ∈ U j) ∧
      ∀ j (x : PSub ε (A j)), (x : S7.UJ ε) ∈ U j → c₁ * Real.log (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) ≤ τ j x
  hsLine : ∀ j (x : PSub ε (A j)) (t : ℝ), 0 ≤ τ j x → 0 ≤ t →
      C⁻¹ * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ≤ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ∧
        Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ≤ C * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε))
  cont : ∀ f ∈ S, Continuous fun g : S7.UJ ε => f (S7.toM g)
  dom : ∀ f ∈ S, ∃ (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ), (∀ h ∈ T, h ∈ S) ∧
      ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖f (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2
  chain : ∀ f ∈ S, ∀ j, ∃ (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)), Chain ε S (A j) (Z j) f f₀ ∧ (∀ h ∈ T, h ∈ S) ∧
      ∀ x : PSub ε (A j), 0 ≤ τ j x →
        ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖
  qual : ∀ f ∈ S, ∀ j, ∀ᵐ (x : PSub ε (A j)) ∂(ν j), (∫⁻ t in Set.Ioi (0 : ℝ),
      ‖f (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + 1) * t))) < ⊤
  level : ∀ f ∈ S, LevelF ε f (-M)

variable {n : ℕ}

def PsiK (ε : Fin n → Bool) (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  (⨆ k : S7.KG ε, ‖q (X * S7.toMK k)‖ₑ ^ 2) * ENNReal.ofReal (Formalism.REAL.hs X ^ w)

variable {ε : Fin n → Bool}

theorem psiK_inv (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (g : S7.UJ ε) (k : S7.KG ε) :
    PsiK ε q w (S7.toM g * S7.toMK k) = PsiK ε q w (S7.toM g) := by
  unfold PsiK
  rw [hs_mul_K]
  congr 1
  have e : ∀ k' : S7.KG ε, S7.toM g * S7.toMK k * S7.toMK k' = S7.toM g * S7.toMK (k * k') := by
    intro k'
    rw [Matrix.mul_assoc]
    rfl
  simp_rw [e]
  exact (Equiv.mulLeft k).iSup_comp (g := fun k' => ‖q (S7.toM g * S7.toMK k')‖ₑ ^ 2)

theorem continuous_hs : Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => Formalism.REAL.hs X) := by
  unfold Formalism.REAL.hs
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_id.matrix_elem i j).norm).pow 2

theorem psiK_meas (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (hq : Continuous fun g : S7.UJ ε => q (S7.toM g)) :
    Measurable fun g : S7.UJ ε => PsiK ε q w (S7.toM g) := by
  have h1 : ∀ k : S7.KG ε, Continuous fun g : S7.UJ ε => ‖q (S7.toM g * S7.toMK k)‖ₑ ^ 2 := by
    intro k
    have hc : Continuous fun g : S7.UJ ε => q (S7.toM (g * (k : S7.UJ ε))) :=
      hq.comp (continuous_mul_const (k : S7.UJ ε))
    exact (ENNReal.continuous_pow 2).comp hc.eNorm
  have hsup : Measurable fun g : S7.UJ ε => ⨆ k : S7.KG ε, ‖q (S7.toM g * S7.toMK k)‖ₑ ^ 2 :=
    (lowerSemicontinuous_iSup fun k => (h1 k).lowerSemicontinuous).measurable
  have hw : Measurable fun g : S7.UJ ε => ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) :=
    ENNReal.measurable_ofReal.comp ((continuous_hs.comp (S7.continuous_toM ε)).measurable.pow_const w)
  exact hsup.mul hw

theorem psiK_ge (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (g : S7.UJ ε) :
    ‖q (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ≤ PsiK ε q w (S7.toM g) := by
  unfold PsiK
  gcongr
  refine le_iSup_of_le (1 : S7.KG ε) ?_
  have : S7.toMK (1 : S7.KG ε) = 1 := rfl
  rw [this, Matrix.mul_one]

theorem psiK_le (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ)
    (hd : ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖q (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2)
    (g : S7.UJ ε) :
    PsiK ε q w (S7.toM g) ≤ ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) := by
  unfold PsiK
  rw [← Finset.sum_mul, ← mul_assoc]
  gcongr
  refine iSup_le fun k => ?_
  have h := hd g 1 k
  have e1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
  rw [e1, Matrix.one_mul] at h
  have hn : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hn]
  calc ENNReal.ofReal (‖q (S7.toM g * S7.toMK k)‖ ^ 2) ≤ ENNReal.ofReal (Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal Cf * ENNReal.ofReal (∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2) :=
        ENNReal.ofReal_mul' (Finset.sum_nonneg fun _ _ => by positivity)
    _ = ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        simp_rw [hn]

theorem psiK_lint (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ)
    (hd : ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖q (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2)
    (hT : ∀ h ∈ T, LevelF ε h w) (hTc : ∀ h ∈ T, Continuous fun g : S7.UJ ε => h (S7.toM g)) :
    ∫⁻ g : S7.UJ ε, PsiK ε q w (S7.toM g) ∂Measure.haar < ⊤ := by
  calc ∫⁻ g : S7.UJ ε, PsiK ε q w (S7.toM g) ∂Measure.haar
      ≤ ∫⁻ g : S7.UJ ε, ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ∂Measure.haar :=
        lintegral_mono fun g => psiK_le q w T Cf hd g
    _ = ENNReal.ofReal Cf * ∑ h ∈ T, ∫⁻ g : S7.UJ ε, ‖h (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ∂Measure.haar := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro h hh
        exact (((ENNReal.continuous_pow 2).comp (hTc h hh).eNorm).measurable.mul
          (ENNReal.measurable_ofReal.comp ((continuous_hs.comp (S7.continuous_toM ε)).measurable.pow_const w))).aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun h hh => hT h hh)

end CompanionTheory.RgExh.Dec.L.AB
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)} {m : ℕ}
    {A : Fin m → Matrix (Fin n) (Fin n) ℂ} {ν : ∀ j, Measure (PSub ε (A j))} {τ : Fin m → S7.UJ ε → ℝ}
    {r : Fin m → ℝ} {Z : Fin m → Finset ℂ} {M c₁ R₀ C : ℝ}

theorem line_curve (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (x : PSub ε (A j)) :
    ∃ ℓ : ℝ → PSub ε (A j), Continuous (fun t => ((ℓ t : PSub ε (A j)) : S7.UJ ε)) ∧
      ∀ t, S7.toM ((ℓ t : PSub ε (A j)) : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT (A j) t ∧ τ j (ℓ t) = τ j x + t := by
  refine ⟨fun t => Classical.choose (H.lines j x t), ?_, fun t => Classical.choose_spec (H.lines j x t)⟩
  rw [(ReciprocityTheory.ChartRestriction.DS.S7.isClosedEmbedding_toM ε).isInducing.continuous_iff]
  have : (fun g : S7.UJ ε => S7.toM g) ∘ (fun t => ((Classical.choose (H.lines j x t) : PSub ε (A j)) : S7.UJ ε)) =
      fun t => S7.toM (x : S7.UJ ε) * aT (A j) t := by
    funext t
    exact (Classical.choose_spec (H.lines j x t)).1
  rw [this]
  exact continuous_const.matrix_mul (continuous_aT (A j))

theorem line_cont (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (x : PSub ε (A j)) (q : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hq : Continuous fun g : S7.UJ ε => q (S7.toM g)) :
    Continuous fun t : ℝ => q (S7.toM (x : S7.UJ ε) * aT (A j) t) := by
  obtain ⟨ℓ, hℓ, hℓe⟩ := line_curve H j x
  have : (fun t : ℝ => q (S7.toM (x : S7.UJ ε) * aT (A j) t)) = fun t => q (S7.toM ((ℓ t : PSub ε (A j)) : S7.UJ ε)) := by
    funext t; rw [(hℓe t).1]
  rw [this]
  exact hq.comp hℓ

theorem ode_line (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (h : Matrix (Fin n) (Fin n) ℂ → ℂ) {mm : ℕ} (z : Fin mm → ℂ)
    (F : Fin (mm + 1) → Matrix (Fin n) (Fin n) ℂ → ℂ) (hF : ∀ k, F k ∈ S) (hlast : F (Fin.last mm) = h)
    (hder : ∀ (k : Fin mm) (g : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), ReciprocityTheory.ChartRestriction.DS.inUJ ε g →
      HasDerivAt (fun s : ℝ => F k.succ (g * aT (A j) s)) (z k * F k.succ (g * aT (A j) t) + F k.castSucc (g * aT (A j) t)) t)
    (R : ℝ) (hR : R ≤ r j + 1) (hzR : ∀ k, (z k).re ≠ -R) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ x : PSub ε (A j),
      (∀ k, ∫⁻ t in Set.Ioi (0 : ℝ), ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (2 * (r j + 1) * t)) < ⊤) →
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
        ENNReal.ofReal C₀ * (∑ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 +
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t))) := by
  obtain ⟨C₀, hC₀, hC⟩ := hLC mm z R (r j + 1) hR hzR
  refine ⟨C₀, hC₀, fun x hx => ?_⟩
  have hx' : ReciprocityTheory.ChartRestriction.DS.inUJ ε (S7.toM (x : S7.UJ ε)) := (x : S7.UJ ε).2
  have := hC (fun k t => F k (S7.toM (x : S7.UJ ε) * aT (A j) t))
    (fun k t _ => hder k _ t hx') (fun k => line_cont H j x (F k) (H.cont _ (hF k))) hx
  simpa only [hlast] using this

theorem src_line (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hTS : ∀ h ∈ T, h ∈ S)
    (hT : ∀ x : PSub ε (A j), 0 ≤ τ j x → ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖)
    (x : PSub ε (A j)) (hx : 0 ≤ τ j x) (R ρ : ℝ) (hRρ : R - 1 ≤ ρ) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
      (T.card : ℝ≥0∞) * ∑ h ∈ T, ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
  classical
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
      (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    obtain ⟨y, hy, hyt⟩ := H.lines j x t
    have hy0 : 0 ≤ τ j y := by rw [hyt]; linarith
    have hb := hT y hy0
    rw [hy] at hb
    set a : (Matrix (Fin n) (Fin n) ℂ → ℂ) → ℝ := fun h => ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ with ha
    set b := ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ with hbdef
    have hb' : b ≤ Real.exp (-t) * ∑ h ∈ T, a h := by
      refine hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by rw [hyt]; linarith))
        (Finset.sum_nonneg fun h _ => norm_nonneg _))
    have hsq : (∑ h ∈ T, a h) ^ 2 ≤ T.card * ∑ h ∈ T, a h ^ 2 := sq_sum_le_card_mul_sum_sq
    have hb2 : b ^ 2 ≤ Real.exp (-t) ^ 2 * (T.card * ∑ h ∈ T, a h ^ 2) := by
      calc b ^ 2 ≤ (Real.exp (-t) * ∑ h ∈ T, a h) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb' 2
        _ = Real.exp (-t) ^ 2 * (∑ h ∈ T, a h) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
    have hexp : Real.exp (-t) ^ 2 * Real.exp (2 * R * t) ≤ Real.exp (2 * ρ * t) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRρ ht0.le])
    have hS0 : 0 ≤ (T.card : ℝ) * ∑ h ∈ T, a h ^ 2 := by positivity
    have hreal : b ^ 2 * Real.exp (2 * R * t) ≤ (T.card : ℝ) * ∑ h ∈ T, a h ^ 2 * Real.exp (2 * ρ * t) := by
      rw [← Finset.sum_mul, ← mul_assoc]
      calc b ^ 2 * Real.exp (2 * R * t) ≤ Real.exp (-t) ^ 2 * (T.card * ∑ h ∈ T, a h ^ 2) * Real.exp (2 * R * t) :=
            mul_le_mul_of_nonneg_right hb2 (Real.exp_pos _).le
        _ = (T.card * ∑ h ∈ T, a h ^ 2) * (Real.exp (-t) ^ 2 * Real.exp (2 * R * t)) := by ring
        _ ≤ (T.card * ∑ h ∈ T, a h ^ 2) * Real.exp (2 * ρ * t) := mul_le_mul_of_nonneg_left hexp hS0
    have hL : ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) =
        ENNReal.ofReal (b ^ 2 * Real.exp (2 * R * t)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
      simp only [hbdef, ofReal_norm_eq_enorm]
    have hR : (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) =
        ENNReal.ofReal ((T.card : ℝ) * ∑ h ∈ T, a h ^ 2 * Real.exp (2 * ρ * t)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
      simp only [ha, ofReal_norm_eq_enorm]
    rw [hL, hR]
    exact ENNReal.ofReal_le_ofReal hreal
  have hmeas : ∀ h ∈ T, Measurable fun t : ℝ =>
      ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
    intro h hh
    have hc := line_cont H j x h (H.cont h (hTS h hh))
    exact (hc.enorm.measurable.pow_const 2).mul (by fun_prop)
  calc ∫⁻ t in Set.Ioi (0 : ℝ), ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t))
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (2 * ρ * t)) := setLIntegral_mono' measurableSet_Ioi hpt
    _ = (T.card : ℝ≥0∞) * ∫⁻ t in Set.Ioi (0 : ℝ), ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (2 * ρ * t)) := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
    _ = _ := by rw [lintegral_finsetSum T hmeas]

theorem unit_line (u : ℝ → ℂ) (ρ : ℝ) :
    ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * |ρ|)) * ∫⁻ t in Set.Ioi (0 : ℝ), ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
  calc ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2
      ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (2 * |ρ|)) * (‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t))) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        have h1 : (1 : ℝ) ≤ Real.exp (2 * |ρ|) * Real.exp (2 * ρ * t) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have : |ρ * t| ≤ |ρ| := by
            rw [abs_mul]
            have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
            calc |ρ| * |t| ≤ |ρ| * 1 := by gcongr
              _ = |ρ| := mul_one _
          have := neg_abs_le (ρ * t)
          nlinarith
        calc ‖u t‖ₑ ^ 2 = ‖u t‖ₑ ^ 2 * 1 := (mul_one _).symm
          _ ≤ ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * |ρ|) * Real.exp (2 * ρ * t)) := by
            gcongr
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal h1
          _ = _ := by
            rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
            ring
    _ = ENNReal.ofReal (Real.exp (2 * |ρ|)) * ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set Set.Ioc_subset_Ioi_self)

theorem back_line (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (j : Fin m) (x : PSub ε (A j)) (hx : 0 ≤ τ j x)
    (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : ℝ) (hs : s ≤ 0) :
    ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ‖q (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t)) ≤
      ENNReal.ofReal (C ^ (-s)) * ∫⁻ t : ℝ, PsiK ε q s (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
  set X := S7.toM (x : S7.UJ ε) with hX
  have hX1 : 1 ≤ Formalism.REAL.hs X := one_le_hs hn (x : S7.UJ ε)
  have haT0 : aT (A j) 0 = 1 := by
    simp [aT]
  have hC1 : 1 ≤ C := by
    have h0 := (H.hsLine j x 0 hx le_rfl).2
    rw [haT0, Matrix.mul_one] at h0
    simp only [mul_zero, Real.exp_zero, mul_one] at h0
    rw [← hX] at h0
    by_contra hC
    have hC' := not_le.mp hC
    nlinarith
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  calc ENNReal.ofReal (Formalism.REAL.hs X ^ s) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ‖q (X * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t))
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Formalism.REAL.hs X ^ s) *
          (‖q (X * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t))) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (C ^ (-s)) *
          (PsiK ε q s (X * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        obtain ⟨y, hy, -⟩ := H.lines j x t
        have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
        have hup := (H.hsLine j x t hx ht0).2
        rw [← hy] at hup ⊢
        have hy1 : 1 ≤ Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) := one_le_hs hn (y : S7.UJ ε)
        have hge := psiK_ge q s (y : S7.UJ ε)

        have key : Formalism.REAL.hs X ^ s * Real.exp (2 * (r j + s) * t) ≤
            C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t) := by
          have h1 : (C * Real.exp (2 * t) * Formalism.REAL.hs X) ^ s ≤ Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s :=
            Real.rpow_le_rpow_of_nonpos (by linarith) hup hs
          rw [Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow hCpos.le (Real.exp_pos _).le,
            ← Real.exp_mul] at h1
          have hCC : C ^ (-s) * C ^ s = 1 := by
            rw [← Real.rpow_add hCpos]; simp
          have e1 : Real.exp (2 * (r j + s) * t) = Real.exp (2 * r j * t) * Real.exp (2 * t * s) := by
            rw [← Real.exp_add]; ring_nf
          rw [e1]
          have hpos : 0 ≤ C ^ (-s) := Real.rpow_nonneg hCpos.le _
          have hE : 0 ≤ Real.exp (2 * r j * t) := (Real.exp_pos _).le
          calc Formalism.REAL.hs X ^ s * (Real.exp (2 * r j * t) * Real.exp (2 * t * s))
              = C ^ (-s) * (C ^ s * Real.exp (2 * t * s) * Formalism.REAL.hs X ^ s) * Real.exp (2 * r j * t) := by
                rw [← mul_assoc (C ^ (-s)), ← mul_assoc (C ^ (-s)), hCC]; ring
            _ ≤ C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t) := by
                gcongr
        have hn1 : 0 ≤ Formalism.REAL.hs X ^ s := Real.rpow_nonneg (by linarith) _
        have hn2 : 0 ≤ C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s :=
          mul_nonneg (Real.rpow_nonneg hCpos.le _) (Real.rpow_nonneg (by linarith) _)
        calc ENNReal.ofReal (Formalism.REAL.hs X ^ s) *
              (‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t)))
            = ‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs X ^ s * Real.exp (2 * (r j + s) * t)) := by
              rw [ENNReal.ofReal_mul hn1]; ring
          _ ≤ ‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
              ENNReal.ofReal (C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t)) := by
              gcongr
          _ = ENNReal.ofReal (C ^ (-s)) * ((‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s)) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by
              rw [ENNReal.ofReal_mul hn2, ENNReal.ofReal_mul (Real.rpow_nonneg hCpos.le _)]; ring
          _ ≤ ENNReal.ofReal (C ^ (-s)) * (PsiK ε q s (S7.toM (y : S7.UJ ε)) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by
              gcongr
    _ = ENNReal.ofReal (C ^ (-s)) * ∫⁻ t in Set.Ioi (0 : ℝ), PsiK ε q s (X * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

theorem line_est (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (s : ℝ) (hs : s ≤ 0) (hL : ∀ f ∈ S, LevelF ε f s)
    (c'' : ℝ) (hc0 : 0 < c'') (hc1 : c'' ≤ 1) (j : Fin m) (hz : ∀ z ∈ Z j, z.re ≠ -(r j + s + c''))
    (h : Matrix (Fin n) (Fin n) ℂ → ℂ) (hh : h ∈ S) :
    ∃ (Ψ : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (K : ℝ≥0∞), K ≠ ⊤ ∧ Measurable (fun g : S7.UJ ε => Ψ (S7.toM g)) ∧
      (∀ (g : S7.UJ ε) (k : S7.KG ε), Ψ (S7.toM g * S7.toMK k) = Ψ (S7.toM g)) ∧
      ∫⁻ g : S7.UJ ε, Ψ (S7.toM g) ∂Measure.haar < ⊤ ∧
      ∀ᵐ (x : PSub ε (A j)) ∂(ν j), τ j x ∈ Set.Ico 0 1 →
        ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)) ≤
        K * ∫⁻ t : ℝ, Ψ (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
  classical
  obtain ⟨f₀, T, ⟨mm, z, F, hzZ, hFS, hlast, h0, hder⟩, hTS, hsrc⟩ := H.chain h hh j
  have hR : r j + s + c'' ≤ r j + 1 := by linarith
  have hzR : ∀ k, (z k).re ≠ -(r j + s + c'') := fun k => hz (z k) (hzZ k)
  obtain ⟨C₀, hC₀, hode⟩ := ode_line hLC H j h z F hFS hlast hder (r j + s + c'') hR hzR
  set Q : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ) := Finset.univ.image F ∪ T with hQ
  have hQS : ∀ q ∈ Q, q ∈ S := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq
      exact hFS k
    · exact hTS q hq
  have hFQ : ∀ k, F k ∈ Q := fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem F (Finset.mem_univ k))
  have hTQ : ∀ q ∈ T, q ∈ Q := fun q hq => Finset.mem_union_right _ hq
  set Ψ : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := fun X => ∑ q ∈ Q, PsiK ε q s X with hΨ
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * |r j + s|)) with hE
  set Cs : ℝ≥0∞ := ENNReal.ofReal (C ^ (-s)) with hCs
  set cT : ℝ≥0∞ := (T.card : ℝ≥0∞) with hcT
  refine ⟨Ψ, ENNReal.ofReal C₀ * (((mm + 1 : ℕ) : ℝ≥0∞) * (E * Cs + cT * (cT * Cs))), ?_, ?_, ?_, ?_, ?_⟩
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
  · exact Finset.measurable_sum Q (fun q hq => psiK_meas q s (H.cont q (hQS q hq)))
  · intro g k
    exact Finset.sum_congr rfl (fun q _ => psiK_inv q s g k)
  · rw [lintegral_finsetSum Q (fun q hq => psiK_meas q s (H.cont q (hQS q hq)))]
    refine ENNReal.sum_lt_top.2 (fun q hq => ?_)
    obtain ⟨T', Cf, hT'S, hd⟩ := H.dom q (hQS q hq)
    exact psiK_lint q s T' Cf hd (fun h' hh' => hL h' (hT'S h' hh')) (fun h' hh' => H.cont h' (hT'S h' hh'))
  · have hq_ae : ∀ᵐ (x : PSub ε (A j)) ∂(ν j), ∀ k, (∫⁻ t in Set.Ioi (0 : ℝ),
        ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + 1) * t))) < ⊤ :=
      ae_all_iff.2 (fun k => H.qual (F k) (hFS k) j)
    filter_upwards [hq_ae] with x hx hτ
    have hx0 : 0 ≤ τ j x := hτ.1
    set a : ℝ≥0∞ := ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) with ha
    set Pall : ℝ≥0∞ := ∫⁻ t : ℝ, Ψ (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) with hPall
    set L : (Matrix (Fin n) (Fin n) ℂ → ℂ) → ℝ≥0∞ := fun q => ∫⁻ t in Set.Ioi (0 : ℝ),
      ‖q (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t)) with hLdef
    have hback : ∀ q ∈ Q, a * L q ≤ Cs * Pall := by
      intro q hq
      refine (back_line H hn j x hx0 q s hs).trans ?_
      refine mul_le_mul_right (lintegral_mono fun t => ?_) _
      refine mul_le_mul_left ?_ _
      exact Finset.single_le_sum (f := fun q => PsiK ε q s (S7.toM (x : S7.UJ ε) * aT (A j) t))
        (fun _ _ => zero_le) hq
    have hunit : ∀ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 ≤ E * L (F k) :=
      fun k => unit_line (fun t => F k (S7.toM (x : S7.UJ ε) * aT (A j) t)) (r j + s)
    have hsrc' : ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)) ≤ cT * ∑ h' ∈ T, L h' := by
      rw [h0]
      exact src_line H j f₀ T hTS hsrc x hx0 (r j + s + c'') (r j + s) (by linarith)
    calc a * ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t))
        ≤ a * (ENNReal.ofReal C₀ * (∑ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 +
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)))) := mul_le_mul_right (hode x hx) a
      _ ≤ a * (ENNReal.ofReal C₀ * ∑ k : Fin (mm + 1), (E * L (F k) + cT * ∑ h' ∈ T, L h')) := by
          refine mul_le_mul_right (mul_le_mul_right (Finset.sum_le_sum fun k _ => ?_) _) _
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc, sub_zero,
            ENNReal.ofReal_one, mul_one]
          exact add_le_add (hunit k) hsrc'
      _ = ENNReal.ofReal C₀ * ∑ k : Fin (mm + 1), (E * (a * L (F k)) + cT * ∑ h' ∈ T, a * L h') := by
          rw [mul_left_comm, Finset.mul_sum]
          refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
          rw [← Finset.mul_sum]
          ring
      _ ≤ ENNReal.ofReal C₀ * ∑ _k : Fin (mm + 1), (E * (Cs * Pall) + cT * ∑ _h' ∈ T, Cs * Pall) :=
          mul_le_mul_right (Finset.sum_le_sum fun k _ => add_le_add (mul_le_mul_right (hback _ (hFQ k)) _)
            (mul_le_mul_right (Finset.sum_le_sum fun h' hh' => hback _ (hTQ h' hh')) _)) _
      _ = ENNReal.ofReal C₀ * (((mm + 1 : ℕ) : ℝ≥0∞) * (E * Cs + cT * (cT * Cs))) * Pall := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcT]
          ring

end CompanionTheory.RgExh.Dec.L.AB
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)} {m : ℕ}
    {A : Fin m → Matrix (Fin n) (Fin n) ℂ} {ν : ∀ j, Measure (PSub ε (A j))} {τ : Fin m → S7.UJ ε → ℝ}
    {r : Fin m → ℝ} {Z : Fin m → Finset ℂ} {M c₁ R₀ C : ℝ}

theorem far_real (a b C c₁ s w c'' r t τy τx : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hlow : C⁻¹ * Real.exp (2 * t) * b ≤ a) (hup : a ≤ C * Real.exp (2 * t) * b)
    (hlog : c₁ * Real.log a ≤ τy) (hτ : τy = τx + t) (hτx : τx < 1) (hc₁ : 0 < c₁)
    (hs : s ≤ 0) (hw1 : s ≤ w) (hw2 : w ≤ s + 2 * c₁ * c'') (hc0 : 0 < c'') :
    a ^ w * Real.exp (2 * r * t) ≤ (C ^ (-s) * Real.exp (2 * c'')) * b ^ s * Real.exp (2 * (r + s + c'') * t) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hC : 0 < C := by
    by_contra hC'
    have hC : C ≤ 0 := not_lt.mp hC'
    have : C * Real.exp (2 * t) * b ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le) hb0.le
    linarith
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  have hτy0 : 0 ≤ τy := le_trans (mul_nonneg hc₁.le hloga) hlog

  have h1 : a ^ (w - s) ≤ Real.exp (2 * c'' * (1 + t)) := by
    rw [Real.rpow_def_of_pos ha0]
    apply Real.exp_le_exp.mpr
    have hl : Real.log a ≤ τy / c₁ := by rw [le_div_iff₀ hc₁]; linarith
    calc Real.log a * (w - s) ≤ τy / c₁ * (w - s) := mul_le_mul_of_nonneg_right hl (by linarith)
      _ ≤ τy / c₁ * (2 * c₁ * c'') := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hτy0 hc₁.le)
      _ = 2 * c'' * τy := by field_simp
      _ ≤ 2 * c'' * (1 + t) := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith

  have h2 : a ^ s ≤ C ^ (-s) * Real.exp (2 * t * s) * b ^ s := by
    have hpos : 0 < C⁻¹ * Real.exp (2 * t) * b := by positivity
    calc a ^ s ≤ (C⁻¹ * Real.exp (2 * t) * b) ^ s := Real.rpow_le_rpow_of_nonpos hpos hlow hs
      _ = C ^ (-s) * Real.exp (2 * t * s) * b ^ s := by
        rw [Real.mul_rpow (by positivity) hb0.le, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
          Real.inv_rpow hC.le, Real.rpow_neg hC.le, ← Real.exp_mul]
  have hsplit : a ^ w = a ^ s * a ^ (w - s) := by
    rw [← Real.rpow_add ha0]; ring_nf
  rw [hsplit]
  calc a ^ s * a ^ (w - s) * Real.exp (2 * r * t)
      ≤ (C ^ (-s) * Real.exp (2 * t * s) * b ^ s) * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t) := by
        gcongr
    _ = (C ^ (-s) * Real.exp (2 * c'')) * b ^ s * Real.exp (2 * (r + s + c'') * t) := by
        have : Real.exp (2 * t * s) * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t) =
            Real.exp (2 * c'') * Real.exp (2 * (r + s + c'') * t) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
        calc C ^ (-s) * Real.exp (2 * t * s) * b ^ s * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t)
            = C ^ (-s) * b ^ s * (Real.exp (2 * t * s) * Real.exp (2 * c'' * (1 + t)) * Real.exp (2 * r * t)) := by ring
          _ = _ := by rw [this]; ring

theorem far_est (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (s : ℝ) (hs : s ≤ 0) (hL : ∀ f ∈ S, LevelF ε f s)
    (c'' : ℝ) (hc0 : 0 < c'') (hc1 : c'' ≤ 1) (j : Fin m) (hz : ∀ z ∈ Z j, z.re ≠ -(r j + s + c''))
    (U : Set (S7.UJ ε)) (hUm : MeasurableSet U) (hUK : ∀ g (k : S7.KG ε), g ∈ U → g * (k : S7.UJ ε) ∈ U)
    (hUτ : ∀ x : PSub ε (A j), (x : S7.UJ ε) ∈ U → c₁ * Real.log (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) ≤ τ j x)
    (R₂ : ℝ) (hR₂ : 1 ≤ R₂) (hR₂' : 1 ≤ c₁ * Real.log R₂) (w : ℝ) (hw1 : s ≤ w) (hw2 : w ≤ s + 2 * c₁ * c'')
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (hf : f ∈ S) :
    ∫⁻ g : S7.UJ ε, (U ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)}).indicator (fun g => PsiK ε f w (S7.toM g)) g ∂Measure.haar < ⊤ := by
  classical
  set V : Set (S7.UJ ε) := U ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)} with hV
  have hVm : MeasurableSet V :=
    hUm.inter (measurableSet_lt measurable_const ((continuous_hs.comp (S7.continuous_toM ε)).measurable))
  have hinj : Function.Injective (fun g : S7.UJ ε => S7.toM g) := (S7.isClosedEmbedding_toM ε).injective
  set F : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := ((fun g : S7.UJ ε => S7.toM g) '' V).indicator (PsiK ε f w) with hFdef
  have hF : ∀ g : S7.UJ ε, F (S7.toM g) = V.indicator (fun g => PsiK ε f w (S7.toM g)) g := by
    intro g
    by_cases hg : g ∈ V
    · rw [Set.indicator_of_mem hg, hFdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hg)]
    · rw [Set.indicator_of_notMem hg, hFdef, Set.indicator_of_notMem]
      rintro ⟨g', hg', he⟩
      exact hg (hinj he ▸ hg')
  have hFm : Measurable fun g : S7.UJ ε => F (S7.toM g) := by
    rw [show (fun g : S7.UJ ε => F (S7.toM g)) = V.indicator (fun g => PsiK ε f w (S7.toM g)) from funext hF]
    exact (psiK_meas f w (H.cont f hf)).indicator hVm
  have hFK : ∀ (g : S7.UJ ε) (k : S7.KG ε), F (S7.toM g * S7.toMK k) = F (S7.toM g) := by
    intro g k
    have e : S7.toM g * S7.toMK k = S7.toM (g * (k : S7.UJ ε)) := rfl
    have hsk : Formalism.REAL.hs (S7.toM (g * (k : S7.UJ ε))) = Formalism.REAL.hs (S7.toM g) := hs_mul_K _ k
    have hmem : g * (k : S7.UJ ε) ∈ V ↔ g ∈ V := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · have := hUK _ k⁻¹ h1
          simpa [mul_assoc] using this
        · show R₂ < Formalism.REAL.hs (S7.toM g)
          have h2' : R₂ < Formalism.REAL.hs (S7.toM (g * (k : S7.UJ ε))) := h2
          rw [hsk] at h2'
          exact h2'
      · rintro ⟨h1, h2⟩
        refine ⟨hUK g k h1, ?_⟩
        show R₂ < Formalism.REAL.hs (S7.toM (g * (k : S7.UJ ε)))
        rw [hsk]
        exact h2
    rw [e, hF, hF]
    by_cases hg : g ∈ V
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]
      exact psiK_inv f w g k
    · rw [Set.indicator_of_notMem (fun h => hg (hmem.1 h)), Set.indicator_of_notMem hg]
  obtain ⟨T, Cf, hTS, hd⟩ := H.dom f hf
  have hle := fun h (hh : h ∈ T) => line_est hLC H hn s hs hL c'' hc0 hc1 j hz h (hTS h hh)
  choose! Ψ K hKT hΨm hΨK hΨi hΨae using hle
  set Kr : ℝ := C ^ (-s) * Real.exp (2 * c'') with hKr
  set Ψt : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := fun X => ∑ h ∈ T, Ψ h X with hΨt
  have hΨtm : Measurable fun g : S7.UJ ε => Ψt (S7.toM g) := Finset.measurable_sum _ fun h hh => hΨm h hh
  have hΨtK : ∀ (g : S7.UJ ε) (k : S7.KG ε), Ψt (S7.toM g * S7.toMK k) = Ψt (S7.toM g) :=
    fun g k => Finset.sum_congr rfl fun h hh => hΨK h hh g k
  have hΨti : ∫⁻ g : S7.UJ ε, Ψt (S7.toM g) ∂Measure.haar < ⊤ := by
    rw [lintegral_finsetSum _ (fun h hh => hΨm h hh)]
    exact ENNReal.sum_lt_top.2 fun h hh => hΨi h hh
  obtain ⟨κ, hκ0, hκT, hform⟩ := H.formula j
  set slab : Set (PSub ε (A j)) := {x : PSub ε (A j) | τ j x ∈ Set.Ico 0 1} with hslabdef
  have hslab : MeasurableSet slab :=
    ((H.tauCont j).measurable.comp measurable_subtype_coe) measurableSet_Ico
  have hJ : ∫⁻ x in slab,
      (∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) < ⊤ := by
    have e := hform Ψt hΨtm hΨtK
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top hκ0] at e
    rw [e] at hΨti
    exact lt_irrefl _ hΨti
  have inner : ∀ x : PSub ε (A j), τ j x ∈ Set.Ico 0 1 →
      ∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) ≤
        ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
            ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)) := by
    intro x hx
    have hb : 1 ≤ Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) := one_le_hs hn _
    have pt : ∀ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) ≤
        (Set.Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) * (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)))) t := by
      intro t
      obtain ⟨y, hy, hτy⟩ := H.lines j x t
      have hFy : F (S7.toM (x : S7.UJ ε) * aT (A j) t) = V.indicator (fun g => PsiK ε f w (S7.toM g)) (y : S7.UJ ε) := by
        rw [← hy]; exact hF _
      rw [hFy]
      by_cases hyV : (y : S7.UJ ε) ∈ V
      · obtain ⟨hyU, hyR⟩ := hyV
        have hyR' : R₂ < Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) := hyR
        have hlog := hUτ y hyU
        have hτ1 : 1 < τ j y := by
          have hl : Real.log R₂ < Real.log (Formalism.REAL.hs (S7.toM (y : S7.UJ ε))) :=
            Real.log_lt_log (by linarith) hyR'
          have := mul_lt_mul_of_pos_left hl H.c1pos
          linarith
        have ht : 0 < t := by have := hx.2; linarith
        rw [Set.indicator_of_mem (show (y : S7.UJ ε) ∈ V from ⟨hyU, hyR⟩), Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
        have hline := H.hsLine j x t hx.1 ht.le
        rw [← hy] at hline
        have hreal := far_real (Formalism.REAL.hs (S7.toM (y : S7.UJ ε))) (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) C c₁ s w c''
          (r j) t (τ j y) (τ j x) (by linarith) hb hline.1 hline.2 hlog hτy hx.2 H.c1pos hs hw1 hw2 hc0
        calc PsiK ε f w (S7.toM (y : S7.UJ ε)) * ENNReal.ofReal (Real.exp (2 * r j * t))
            ≤ (ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ w)) * ENNReal.ofReal (Real.exp (2 * r j * t)) :=
              mul_le_mul_left (psiK_le f w T Cf hd y) _
          _ = ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ w * Real.exp (2 * r j * t)) := by
              rw [mul_assoc, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun h _ => ?_
              rw [ENNReal.ofReal_mul' (Real.exp_pos _).le, mul_assoc]
          _ ≤ ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Kr * Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s * Real.exp (2 * (r j + s + c'') * t)) :=
              mul_le_mul_right (Finset.sum_le_sum fun h _ => mul_le_mul_right (ENNReal.ofReal_le_ofReal hreal) _) _
          _ = _ := by
              rw [hy]
              simp only [Finset.mul_sum]
              refine Finset.sum_congr rfl fun h _ => ?_
              rw [ENNReal.ofReal_mul' (Real.exp_pos _).le, ENNReal.ofReal_mul' (by positivity)]
              ring
      · rw [Set.indicator_of_notMem hyV, zero_mul]
        exact bot_le
    have hmeas : ∀ h ∈ T, Measurable fun t : ℝ => ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
        (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t))) := by
      intro h hh
      have hc := line_cont H j x h (H.cont h (hTS h hh))
      exact measurable_const.mul ((hc.eNorm.measurable.pow_const 2).mul
        (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable))
    calc ∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))
        ≤ ∫⁻ t : ℝ, (Set.Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) * (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)))) t := lintegral_mono pt
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T,
          ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) * (‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t))) := lintegral_indicator measurableSet_Ioi _
      _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
            lintegral_finsetSum _ hmeas]
          congr 1
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  set Kall : ℝ≥0∞ := ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T, K h with hKall_def
  have hKall : Kall ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.sum_ne_top.2 fun h hh => hKT h hh)
  have hae : ∀ᵐ (x : PSub ε (A j)) ∂((ν j).restrict slab),
      ∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) ≤
        Kall * ∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
    rw [ae_restrict_iff' hslab]
    have hall := (Filter.eventually_all_finset T).2 fun h hh => hΨae h hh
    filter_upwards [hall] with x hx hxs
    calc _ ≤ _ := inner x hxs
      _ ≤ ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T, K h *
            ∫⁻ t : ℝ, Ψ h (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) :=
          mul_le_mul_right (Finset.sum_le_sum fun h hh => hx h hh hxs) _
      _ ≤ ENNReal.ofReal Cf * ENNReal.ofReal Kr * ∑ h ∈ T, K h *
            ∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
          refine mul_le_mul_right (Finset.sum_le_sum fun h hh => mul_le_mul_right (lintegral_mono fun t => ?_) _) _
          exact mul_le_mul_left (Finset.single_le_sum (f := fun h => Ψ h (S7.toM (x : S7.UJ ε) * aT (A j) t))
            (fun _ _ => bot_le) hh) _
      _ = Kall * ∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
          rw [hKall_def, ← Finset.sum_mul]; ring
  have hI : ∫⁻ x in slab,
      (∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) < ⊤ := by
    calc _ ≤ ∫⁻ x in slab,
          Kall * (∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) :=
          lintegral_mono_ae hae
      _ = Kall * ∫⁻ x in slab,
          (∫⁻ t : ℝ, Ψt (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j) :=
          lintegral_const_mul' _ _ hKall
      _ < ⊤ := ENNReal.mul_lt_top hKall.lt_top hJ
  have e1 : (∫⁻ g : S7.UJ ε, V.indicator (fun g => PsiK ε f w (S7.toM g)) g ∂Measure.haar) =
      ∫⁻ g : S7.UJ ε, F (S7.toM g) ∂Measure.haar := by
    congr 1; funext g; exact (hF g).symm
  rw [e1, hform F hFm hFK]
  exact ENNReal.mul_lt_top hκT.lt_top hI

theorem ball_est (hn : 0 < n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (s w R₂ : ℝ) (hw : s ≤ w) (hR₂ : 1 ≤ R₂)
    (hf : LevelF ε f s) :
    ∫⁻ g : S7.UJ ε, {g | Formalism.REAL.hs (S7.toM g) ≤ R₂}.indicator
      (fun g => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w)) g ∂Measure.haar < ⊤ := by
  unfold LevelF at hf
  have key : ∀ g : S7.UJ ε, {g | Formalism.REAL.hs (S7.toM g) ≤ R₂}.indicator
      (fun g => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w)) g ≤
      ENNReal.ofReal (R₂ ^ (w - s)) * (‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s)) := by
    intro g
    by_cases hg : Formalism.REAL.hs (S7.toM g) ≤ R₂
    · rw [Set.indicator_of_mem (show g ∈ {g | Formalism.REAL.hs (S7.toM g) ≤ R₂} from hg)]
      have h1 := one_le_hs hn g
      have hpos : 0 < Formalism.REAL.hs (S7.toM g) := by linarith
      have e : Formalism.REAL.hs (S7.toM g) ^ w = Formalism.REAL.hs (S7.toM g) ^ s * Formalism.REAL.hs (S7.toM g) ^ (w - s) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      have hle : Formalism.REAL.hs (S7.toM g) ^ (w - s) ≤ R₂ ^ (w - s) :=
        Real.rpow_le_rpow hpos.le hg (by linarith)
      rw [e, ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
      calc ‖f (S7.toM g)‖ₑ ^ 2 * (ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (w - s)))
          ≤ ‖f (S7.toM g)‖ₑ ^ 2 * (ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) * ENNReal.ofReal (R₂ ^ (w - s))) := by
            gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (show g ∉ {g | Formalism.REAL.hs (S7.toM g) ≤ R₂} from hg)]
      exact bot_le
  refine lt_of_le_of_lt (lintegral_mono key) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

theorem step (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (s : ℝ) (hs : s ≤ 0) (hL : ∀ f ∈ S, LevelF ε f s)
    (c'' : ℝ) (hc0 : 0 < c'') (hc1 : c'' ≤ 1) (hz : ∀ j, ∀ z ∈ Z j, z.re ≠ -(r j + s + c''))
    (w : ℝ) (hw1 : s ≤ w) (hw2 : w ≤ s + 2 * c₁ * c'') : ∀ f ∈ S, LevelF ε f w := by
  obtain ⟨U, hUm, hUK, hUcov, hUτ⟩ := H.cover
  set R₂ : ℝ := max (max R₀ 1) (Real.exp (1 / c₁)) with hR₂def
  have hR₂1 : 1 ≤ R₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR₂0 : R₀ ≤ R₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR₂' : 1 ≤ c₁ * Real.log R₂ := by
    have h1 : 1 / c₁ ≤ Real.log R₂ := by
      rw [← Real.log_exp (1 / c₁)]
      exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    have hc := H.c1pos
    calc (1:ℝ) = c₁ * (1 / c₁) := by field_simp
      _ ≤ c₁ * Real.log R₂ := by gcongr
  intro f hf
  have hcont := H.cont f hf
  have hmhs : Measurable fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) :=
    (continuous_hs.comp (S7.continuous_toM ε)).measurable
  set ball : S7.UJ ε → ℝ≥0∞ := {g | Formalism.REAL.hs (S7.toM g) ≤ R₂}.indicator
      (fun g => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w)) with hball
  set far : Fin m → S7.UJ ε → ℝ≥0∞ := fun j => (U j ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)}).indicator
      (fun g => PsiK ε f w (S7.toM g)) with hfar
  have hmball : Measurable ball := by
    refine Measurable.indicator ?_ (measurableSet_le hmhs measurable_const)
    exact (hcont.eNorm.measurable.pow_const 2).mul ((hmhs.pow_const w).ennreal_ofReal)
  have hmfar : ∀ j ∈ (Finset.univ : Finset (Fin m)), Measurable (far j) := fun j _ =>
    (psiK_meas f w hcont).indicator ((hUm j).inter (measurableSet_lt measurable_const hmhs))
  have hpt : ∀ g, ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ≤ ball g + ∑ j, far j g := by
    intro g
    by_cases hg : Formalism.REAL.hs (S7.toM g) ≤ R₂
    · have e : ball g = ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) :=
        Set.indicator_of_mem (show g ∈ {g | Formalism.REAL.hs (S7.toM g) ≤ R₂} from hg) _
      rw [e]; exact le_self_add
    · have hg' := lt_of_not_ge hg
      obtain ⟨j, hj⟩ := hUcov g (lt_of_le_of_lt hR₂0 hg')
      have hfj : far j g = PsiK ε f w (S7.toM g) :=
        Set.indicator_of_mem (show g ∈ U j ∩ {g | R₂ < Formalism.REAL.hs (S7.toM g)} from ⟨hj, hg'⟩) _
      calc _ ≤ PsiK ε f w (S7.toM g) := psiK_ge f w g
        _ = far j g := hfj.symm
        _ ≤ ∑ j, far j g := Finset.single_le_sum (f := fun j => far j g) (fun _ _ => bot_le) (Finset.mem_univ j)
        _ ≤ _ := le_add_self
  unfold LevelF
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_add_left hmball, lintegral_finsetSum _ hmfar]
  refine ENNReal.add_lt_top.2 ⟨ball_est hn f s w R₂ hw1 hR₂1 (hL f hf), ?_⟩
  exact ENNReal.sum_lt_top.2 fun j _ => far_est hLC H hn s hs hL c'' hc0 hc1 j (hz j) (U j) (hUm j)
    (fun g k hg => hUK j g k hg) (hUτ j) R₂ hR₂1 hR₂' w hw1 hw2 f hf

theorem exists_good (Z : Fin m → Finset ℂ) (r : Fin m → ℝ) (s : ℝ) :
    ∃ c'' : ℝ, 1 / 2 ≤ c'' ∧ c'' ≤ 1 ∧ ∀ j, ∀ z ∈ Z j, z.re ≠ -(r j + s + c'') := by
  classical
  set B : Finset ℝ := Finset.univ.biUnion (fun j => (Z j).image (fun z => -(r j + s) - z.re))
  obtain ⟨c, hc, hcB⟩ := (Set.Icc_infinite (show (1 / 2 : ℝ) < 1 by norm_num)).exists_notMem_finset B
  refine ⟨c, hc.1, hc.2, fun j z hz he => hcB ?_⟩
  simp only [B, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  exact ⟨j, z, hz, by linarith⟩

theorem level_mono (hn : 0 < n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) {s s' : ℝ} (h : s' ≤ s) (hf : LevelF ε f s) :
    LevelF ε f s' := by
  unfold LevelF at *
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hf
  gcongr
  exact one_le_hs hn g

theorem level_zero_dim (ε : Fin 0 → Bool) (f : Matrix (Fin 0) (Fin 0) ℂ → ℂ) (s : ℝ) : LevelF ε f s := by
  unfold LevelF
  haveI : Subsingleton (S7.UJ ε) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  haveI : CompactSpace (S7.UJ ε) := Finite.compactSpace
  set c : ℝ≥0∞ := ‖f (S7.toM (1 : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM (1 : S7.UJ ε)) ^ s)
  have : ∀ g : S7.UJ ε, ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) = c := by
    intro g; rw [Subsingleton.elim g 1]
  simp_rw [this]
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top) (measure_lt_top _ _)

theorem absolute_l2_of_line_chain (hLC : LineChain) : AbsoluteL2Bound := by
  intro n ε S m A ν τ r Z M c₁ R₀ C hc1 hform htc htinv hlines hcover hhs hcont hdom hchain hqual hlev
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact fun f _ => level_zero_dim ε f 0
  have H : Hyp ε S m A ν τ r Z M c₁ R₀ C :=
    ⟨hc1, hform, htc, htinv, hlines, hcover, hhs, hcont, hdom, hchain, hqual, hlev⟩
  have key : ∀ N : ℕ, ∀ f ∈ S, LevelF ε f (min (-M + N * c₁) 0) := by
    intro N
    induction N with
    | zero =>
      intro f hf
      exact level_mono hn f (by simp) (hlev f hf)
    | succ N ih =>
      obtain ⟨c'', h1, h2, hz⟩ := exists_good Z r (min (-M + N * c₁) 0)
      refine step hLC H hn _ (min_le_right _ _) ih c'' (by linarith) h2 hz _ ?_ ?_
      · apply min_le_min_right; push_cast; nlinarith [hc1]
      · have hcc : c₁ ≤ 2 * c₁ * c'' := by nlinarith
        rcases le_total (-M + N * c₁) 0 with h | h
        · rw [min_eq_left h]; push_cast
          have := min_le_left (-M + ((N : ℝ) + 1) * c₁) 0; nlinarith
        · rw [min_eq_right h]
          have := min_le_right (-M + ((N + 1 : ℕ) : ℝ) * c₁) 0; nlinarith
  intro f hf
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M ≤ N * c₁ := ⟨⌈M / c₁⌉₊, by
    have := Nat.le_ceil (M / c₁); rwa [div_le_iff₀ hc1] at this⟩
  have := key N f hf
  rwa [min_eq_right (by linarith)] at this

end CompanionTheory.RgExh.Dec.L.AB
end
end

namespace CompanionTheory.RgExh.Dec.L.AB

theorem absolute_l2_bound : CompanionTheory.RgExh.Dec.L.AbsoluteL2Bound := absolute_l2_of_line_chain GlobalTheory.CompanionTheory.LineChainProof.lineChain

end CompanionTheory.RgExh.Dec.L.AB
