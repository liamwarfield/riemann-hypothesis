module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydisc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPos
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPos
open Complex MeasureTheory

namespace GlobalTheory

theorem periodic_strip_shift_nonneg (c : ℝ) (f : ℂ → ℂ) (m : ℤ)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < c})
    (hper : ∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m)
    (hpos : ∀ s : ℂ, s.re < c → 0 < (f s).im) : 0 ≤ m := by
  have hcont : ContinuousOn f {s : ℂ | s.re < c} := hf.continuousOn
  have hvert : ∀ x : ℝ, x < c → IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume 0 (2 * Real.pi) := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro y _
    simp [hx]
  have hhor : ∀ (x₁ x₂ : ℝ), x₁ ≤ x₂ → x₂ < c → IntervalIntegrable (fun x : ℝ => f (x : ℂ)) volume x₁ x₂ := by
    intro x₁ x₂ h12 h2
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le h12] at hx
    simp only [Set.mem_setOf_eq, ofReal_re]
    linarith [hx.2]
  have hVim : ∀ x : ℝ, x < c → 0 ≤ (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x + y * I)).im := by
    intro x hx
    have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
    have hc := Complex.imCLM.intervalIntegral_comp_comm (hvert x hx)
    simp only [Complex.imCLM_apply] at hc
    rw [← hc]
    apply intervalIntegral.integral_nonneg h2pi
    intro y _
    exact (hpos _ (by simp [hx])).le
  have key : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → x₂ < c →
      (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₁ + y * I)).im
        = (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₂ + y * I)).im + m * (x₂ - x₁) := by
    intro x₁ x₂ h12 h2c
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x₁ : ℂ)
      ((x₂ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * I) ?_
    · simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, ofReal_zero] at hrect
      have htop : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
          = (∫ x : ℝ in x₁..x₂, f (x : ℂ)) + (m : ℂ) * ((x₂ - x₁ : ℝ) : ℂ) := by
        have hc : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
            = ∫ x : ℝ in x₁..x₂, (f (x : ℂ) + m) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le h12] at hx
          have hxc : (x : ℂ).re < c := by simp; linarith [hx.2]
          simp only
          rw [← hper _ hxc]
          congr 1
          push_cast
          ring
        rw [hc, intervalIntegral.integral_add (hhor x₁ x₂ h12 h2c) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp [mul_comm]
      rw [htop] at hrect
      have hre := congrArg Complex.re hrect
      simp at hre
      linarith
    · apply hf.mono
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      simp only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hz
      rw [Set.uIcc_of_le h12] at hz
      show z.re < c
      linarith [hz.1.2]
  by_contra hm
  push_neg at hm
  have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
  set a := (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f ((c - 1 : ℝ) + y * I)).im with ha
  have ha0 : 0 ≤ a := hVim (c - 1) (by linarith)
  have h1 := key (c - 1 - (a + 1)) (c - 1) (by linarith) (by linarith)
  have h2 := hVim (c - 1 - (a + 1)) (by linarith)
  rw [h1] at h2
  nlinarith [mul_le_mul_of_nonneg_right hm1 (by linarith : (0:ℝ) ≤ a + 1)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPosStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos : ∀ (c : ℝ) (f : ℂ → ℂ) (m : ℤ), DifferentiableOn ℂ f {s : ℂ | s.re < c} → (∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m) → (∀ s : ℂ, s.re < c → 0 < (f s).im) → 0 ≤ m := by
  first | exact @GlobalTheory.periodic_strip_shift_nonneg | exact GlobalTheory.periodic_strip_shift_nonneg | (intros; apply GlobalTheory.periodic_strip_shift_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegral
open GlobalTheory.ShFam.Hor
open scoped Matrix

namespace GlobalTheory

theorem monodromy_dotProduct_nonneg : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  intro n a g ha ρ₁ τ B hρ0 hρ1 hdiff hpos hmon k v
  by_cases hv : v = 0
  · subst hv; simp
  set j : Fin n := Fin.castLE ha k with hj
  have hjlt : (j : ℕ) < a := by simp [hj]
  let s₀ : Fin n → ℂ := fun i => if (i : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0
  let u : ℂ → Fin n → ℂ := fun t => Function.update s₀ j t
  let D := {s : Fin n → ℂ | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}
  have hlog2 : Real.log (ρ₁ / 2) < 0 := Real.log_neg (by positivity) (by linarith)
  have hlogle : Real.log ρ₁ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hexp2 : Real.exp (Real.log (ρ₁ / 2)) = ρ₁ / 2 := Real.exp_log (by positivity)
  have hmem : ∀ t : ℂ, t.re < Real.log ρ₁ → u t ∈ D := by
    intro t ht
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        simp only [u, Function.update_self, hjlt, if_true]
        linarith
      · simp only [u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · simpa using hlog2
        · simp
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ0]
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [logExp, u, Function.update_self, hjlt, if_true, Complex.norm_exp]
        calc Real.exp t.re < Real.exp (Real.log ρ₁) := Real.exp_lt_exp.2 ht
          _ = ρ₁ := Real.exp_log hρ0
      · simp only [logExp, u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · rw [Complex.norm_exp, Complex.ofReal_re, hexp2]; linarith
        · simpa using hρ0
  let v' : Fin g → ℂ := fun i => (v i : ℂ)
  let f : ℂ → ℂ := fun t => v' ⬝ᵥ (τ (u t) *ᵥ v')
  have hshift : ∀ t : ℂ, u (t + 2 * Real.pi * Complex.I) = u t + Pi.single j (2 * Real.pi * Complex.I) := by
    intro t
    ext i
    by_cases hi : i = j
    · subst hi; simp [u]
    · simp [u, hi, Function.update_of_ne hi, Pi.single_apply]
  have hcast : v' ⬝ᵥ ((B k).map (Int.cast : ℤ → ℂ) *ᵥ v') = ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    simp [v', dotProduct, Matrix.mulVec, Matrix.map_apply]
  have hper : ∀ t : ℂ, t.re < Real.log ρ₁ → f (t + 2 * Real.pi * Complex.I) = f t + ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    intro t ht
    have h1 := hmon (u t) (hmem t ht).1 (hmem t ht).2 k
    simp only [f]
    rw [hshift t, h1, Matrix.add_mulVec, dotProduct_add, hcast]
  let v'' : Fin g → ℝ := fun i => (v i : ℝ)
  have hv'' : v'' ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa [v''] using this
  have him : ∀ t : ℂ, t.re < Real.log ρ₁ → 0 < (f t).im := by
    intro t ht
    have hp := ((hpos (u t) (hmem t ht).1 (hmem t ht).2).2).dotProduct_mulVec_pos hv''
    have heq : (f t).im = star v'' ⬝ᵥ (((τ (u t)).map Complex.im) *ᵥ v'') := by
      simp [f, v', v'', dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum]
    rw [heq]; exact hp
  have hu : Differentiable ℂ u := fun t => (hasFDerivAt_update s₀ t).differentiableAt
  have hent : ∀ i l, DifferentiableOn ℂ (fun t => τ (u t) i l) {t : ℂ | t.re < Real.log ρ₁} :=
    fun i l => (hdiff i l).comp hu.differentiableOn (fun t ht => hmem t ht)
  have hdf : DifferentiableOn ℂ f {t : ℂ | t.re < Real.log ρ₁} := by
    simp only [f, dotProduct, Matrix.mulVec]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro l _
    exact (hent i l).mul_const _
  exact_mod_cast GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos (Real.log ρ₁) f (v ⬝ᵥ (B k *ᵥ v)) hdf hper him

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegralStatement
open GlobalTheory.ShFam.Hor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  first | exact @GlobalTheory.monodromy_dotProduct_nonneg | exact GlobalTheory.monodromy_dotProduct_nonneg | (intros; apply GlobalTheory.monodromy_dotProduct_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonneg
namespace GlobalTheory

open Matrix

theorem intSymm_posSemidef_real :
    ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm →
      (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) →
      (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  intro g B hB hQ
  set M : Matrix (Fin g) (Fin g) ℝ := B.map (Int.cast : ℤ → ℝ) with hM

  set f : (Fin g → ℝ) → ℝ := fun x => dotProduct x (M.mulVec x) with hf
  have hcont : Continuous f := by
    simp only [hf, dotProduct, mulVec]
    fun_prop
  have hscale : ∀ (c : ℝ) (x : Fin g → ℝ), f (c • x) = c ^ 2 * f x := by
    intro c x
    simp only [hf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hint : ∀ v : Fin g → ℤ, f (fun i => (v i : ℝ)) = ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by
    intro v
    simp only [hf, hM, dotProduct, mulVec, Matrix.map_apply]
    push_cast
    rfl
  have hrat : ∀ q : Fin g → ℚ, 0 ≤ f (fun i => (q i : ℝ)) := by
    intro q
    set N : ℕ := ∏ i, (q i).den with hN
    have hNpos : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
    have hdvd : ∀ i, (q i).den ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    let v : Fin g → ℤ := fun i => (q i).num * ((N / (q i).den : ℕ) : ℤ)
    have hv : (N : ℝ) • (fun i => (q i : ℝ)) = fun i => (v i : ℝ) := by
      funext i
      have hd : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
      simp only [Pi.smul_apply, smul_eq_mul, v, Int.cast_mul, Int.cast_natCast]
      rw [Nat.cast_div (hdvd i) hd, Rat.cast_def]
      field_simp
    have h1 := hscale (N : ℝ) (fun i => (q i : ℝ))
    rw [hv, hint] at h1
    have h2 : (0 : ℝ) ≤ ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by exact_mod_cast hQ v
    have h3 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    nlinarith
  have hdense : DenseRange (fun q : Fin g → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hall : ∀ x : Fin g → ℝ, 0 ≤ f x := by
    intro x
    have hclosed : IsClosed {x : Fin g → ℝ | 0 ≤ f x} := isClosed_le continuous_const hcont
    have hsub : Set.range (fun q : Fin g → ℚ => fun i => (q i : ℝ)) ⊆ {x | 0 ≤ f x} := by
      rintro _ ⟨q, rfl⟩
      exact hrat q
    have := hdense.closure_range ▸ (closure_minimal hsub hclosed)
    exact this (Set.mem_univ x)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [hM, conjTranspose_apply, hB.apply i j]
  · simpa [hf] using hall x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonnegStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg : ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm → (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) → (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  first | exact @GlobalTheory.intSymm_posSemidef_real | exact GlobalTheory.intSymm_posSemidef_real | (intros; apply GlobalTheory.intSymm_posSemidef_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidef
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerExt

theorem logExp_add_single {n a : ℕ} (s : Fin n → ℂ) (j : Fin n) (hj : (j : ℕ) < a) :
    logExp a (s + Pi.single j (2 * Real.pi * Complex.I)) = logExp a s := by
  funext k
  simp only [logExp, Pi.add_apply]
  by_cases hk : k = j
  · subst hk
    simp [hj, Complex.exp_add]
  · simp [Pi.single_apply, hk]

theorem mem_logDom_add_single {n a : ℕ} {s : Fin n → ℂ} (hs : s ∈ logDom n a) (j : Fin n) (hj : (j : ℕ) < a) :
    s + Pi.single j (2 * Real.pi * Complex.I) ∈ logDom n a := by
  intro k
  have := hs k
  by_cases hk : k = j
  · subst hk
    simp only [if_pos hj] at this ⊢
    simpa using this
  · simpa [Pi.single_apply, hk] using this

theorem quad_single {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i : Fin g) :
    dotProduct (Pi.single i 1) (M.mulVec (Pi.single i 1)) = M i i := by
  simp [Matrix.mulVec_single, single_dotProduct]

theorem quad_add {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i j : Fin g) :
    dotProduct (Pi.single i 1 + Pi.single j 1) (M.mulVec (Pi.single i 1 + Pi.single j 1)) =
      M i i + M i j + M j i + M j j := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single, single_dotProduct]
  simp
  ring

theorem cast_single {g : ℕ} (i : Fin g) : (fun l => ((Pi.single i (1 : ℤ) : Fin g → ℤ) l : ℂ)) = Pi.single i 1 := by
  funext l
  by_cases h : l = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem cast_single_add {g : ℕ} (i j : Fin g) :
    (fun l => (((Pi.single i (1 : ℤ) + Pi.single j 1 : Fin g → ℤ)) l : ℂ)) = Pi.single i 1 + Pi.single j 1 := by
  funext l
  by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [Pi.single_apply, h1, h2]

theorem periodMatrix_extension : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (τ₀ z).IsSymm) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → τ s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ) := by
  intro n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon

  have hs₀ : ∃ s₀, s₀ ∈ logDom n a ∧ logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by
    refine ⟨fun k => if (k : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0, ?_, ?_⟩
    · intro k
      by_cases hk : (k : ℕ) < a
      · simp only [if_pos hk, Complex.ofReal_re]
        exact Real.log_neg (by positivity) (by linarith)
      · simp [hk]
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ]
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [logExp, if_pos hk]
        rw [← Complex.ofReal_exp, Real.exp_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      · simp [logExp, hk, hρ]
  obtain ⟨s₀, hs₀D, hs₀B⟩ := hs₀

  have hBsym : ∀ k, (B k).IsSymm := by
    intro k
    have hj : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
    have h1 := hmon s₀ hs₀D hs₀B k
    have h2 := (hsym _ (mem_logDom_add_single hs₀D _ hj) (by rw [logExp_add_single _ _ hj]; exact hs₀B)).1
    have h3 := (hsym s₀ hs₀D hs₀B).1
    rw [h1] at h2
    refine Matrix.IsSymm.ext fun i j => ?_
    have e1 := congrFun (congrFun h2 i) j
    have e2 := congrFun (congrFun h3 i) j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.map_apply] at e1 e2
    have : ((B k j i : ℤ) : ℂ) = B k i j := by rw [e2] at e1; exact add_left_cancel e1
    exact_mod_cast this
  have hnn := GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon
  refine ⟨fun k => GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg g (B k) (hBsym k) (hnn k), ?_⟩
  have hF : ∀ v : Fin g → ℤ, ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
        dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) -
          ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) =
            F (logExp a s) :=
    fun v => GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc n a g ha ρ₁ τ B v hρ hρ1 hdiff hsym hmon (fun k => hnn k v)
  choose F hFd hFe using hF
  let e : Fin g → Fin g → ℤ := fun i => Pi.single i 1
  refine ⟨fun z => Matrix.of fun i j => if i = j then F (e i) z else (F (e i + e j) z - F (e i) z - F (e j) z) / 2,
    fun i j => ?_, fun z _ => ?_, fun s hs hsB => ?_⟩
  · simp only [Matrix.of_apply]
    by_cases hij : i = j
    · simp only [if_pos hij]; exact hFd _
    · simp only [if_neg hij]
      have h1 := hFd (e i + e j)
      have h2 := hFd (e i)
      have h3 := hFd (e j)
      fun_prop
  · refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.of_apply]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg (Ne.symm hij), if_neg hij, add_comm (e j)]
      ring
  · refine Matrix.ext fun i j => ?_
    beta_reduce
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]
    have hsm : ∀ k, ((s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) i j =
        s (Fin.castLE ha k) / (2 * Real.pi * Complex.I) * ((B k i j : ℤ) : ℂ) := fun k => rfl
    rw [Finset.sum_congr rfl fun k _ => hsm k]
    set c : ℂ := 2 * Real.pi * Complex.I
    have hi := hFe (e i) s hs hsB
    have hj := hFe (e j) s hs hsB
    simp only [e, cast_single, quad_single] at hi hj
    have hsum1 : ∀ l, ∑ k, s (Fin.castLE ha k) * ((B k l l : ℤ) : ℂ) / c = ∑ k, s (Fin.castLE ha k) / c * ((B k l l : ℤ) : ℂ) :=
      fun l => Finset.sum_congr rfl fun k _ => by ring
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hee : F (e i) (logExp a s) = F (Pi.single i 1) (logExp a s) := rfl
      rw [hee, ← hi, hsum1 i]
      ring
    · simp only [if_neg hij]
      have hp := hFe (e i + e j) s hs hsB
      simp only [e, cast_single_add, quad_add] at hp
      have hsi : (τ s) j i = (τ s) i j := ((hsym s hs hsB).1.apply i j)
      have hbi : ∀ k, B k j i = B k i j := fun k => (hBsym k).apply i j
      have hsum2 : ∑ k, s (Fin.castLE ha k) * ((B k i i + B k i j + B k j i + B k j j : ℤ) : ℂ) / c =
          ∑ k, s (Fin.castLE ha k) * ((B k i i : ℤ) : ℂ) / c + 2 * ∑ k, s (Fin.castLE ha k) / c * ((B k i j : ℤ) : ℂ) +
            ∑ k, s (Fin.castLE ha k) * ((B k j j : ℤ) : ℂ) / c := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hbi k]; push_cast; ring
      rw [hsum2] at hp
      rw [← hp, ← hi, ← hj, hsi]
      ring

end GlobalTheory.ShFam.Hor.LogCh.PerExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidefStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (τ₀ z).IsSymm) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → τ s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension | exact GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension <;> assumption)
end
