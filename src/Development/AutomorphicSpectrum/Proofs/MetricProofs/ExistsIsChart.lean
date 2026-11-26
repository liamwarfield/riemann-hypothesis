module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

def tauAt (ha : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (w : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  T0 (expCover a w) + ∑ j, (w (Fin.castLE ha j) / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))

structure IsChart (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ)
    (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) : Prop where
  form : ∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
    L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0
  A_cont : ContinuousOn A (Metric.ball 0 1)
  A_det : (A 0).det ≠ 0
  T_cont : ContinuousOn T0 (Metric.ball 0 1)
  B_psd : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef
  c_pos : 0 < c
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ 1
  im_lower : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : Fin a → ℂ,
    (∀ j, Complex.exp (l j) = z (Fin.castLE L.a_le j)) →
    ((T0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
      Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  sym : ∀ w ∈ logCover L.a_le, (tauAt L.a_le T0 B w)ᵀ = tauAt L.a_le T0 B w
  im_pos : ∀ w ∈ logCover L.a_le, ((tauAt L.a_le T0 B w).map Complex.im).PosDef
  per : ∀ w ∈ logCover L.a_le, ∀ x, L.P w x =
    (A (expCover a w))ᵀ *ᵥ (cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x))

theorem exists_isChart (L : Flat.LogPeriods n a g Λ) : ∃ bas A T0 B c ρ, IsChart L bas A T0 B c ρ := by
  obtain ⟨bas, Q, A, T0, hE, hAd, hA0, hT0, hBpsd, hPa, hPb⟩ := GlobalTheory.T.symplectic_polydisc_period_basis n a g Λ L
  obtain ⟨ρ₁, c, C₁, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousOn A (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hTc : ContinuousOn T0 (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hT0.1 i j).continuousOn
  have hQa : Q.a_le = L.a_le := rfl
  have hτ : ∀ w ∈ logCover L.a_le, Q.τ w = tauAt L.a_le T0 Q.B w := by
    intro w hw
    have h := hT0.2 w hw
    simp only [PeriodPolydisc.tau0] at h
    simp only [tauAt]
    rw [← h]
    exact (sub_add_cancel _ _).symm
  refine ⟨bas, A, T0, Q.B, c, ρ₁, hE, hAc, hA0, hTc, hBpsd, hc, hρ₁, hρ₁1.le, ?_, ?_, ?_, ?_⟩
  · intro z hz l hl
    have hz1 : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k)
        (lt_trans (by simpa [dist_zero_right] using hz) hρ₁1)
    let w : Fin n → ℂ := fun k => if h : k.val < a then l ⟨k.val, h⟩ else z k
    have hwj : ∀ j : Fin a, w (Fin.castLE L.a_le j) = l j := by
      intro j
      have hj : (Fin.castLE L.a_le j).val < a := j.2
      simp [w, hj]
    have hexp : expCover a w = z := by
      funext k
      by_cases hk : k.val < a
      · have := hl ⟨k.val, hk⟩
        simp only [expCover, hk, if_true, w, dif_pos]
        rw [this]
        rfl
      · simp [expCover, hk, w]
    have hw : w ∈ logCover L.a_le := by
      refine ⟨fun i => ?_, fun k hk => ?_⟩
      · rw [hwj]
        have h1 : ‖Complex.exp (l i)‖ < 1 := by rw [hl i]; exact hz1 _
        rw [Complex.norm_exp] at h1
        exact Real.exp_lt_one_iff.1 h1
      · have hk' : ¬ k.val < a := not_lt.2 hk
        simp only [w, hk', dif_neg, not_false_eq_true]
        exact hz1 k
    have h1 := (hb w hw (by rw [hexp]; exact Metric.ball_subset_closedBall hz)).1
    rw [hτ w hw] at h1
    simp only [tauAt, hexp, hwj] at h1
    exact h1
  · intro w hw
    rw [← hτ w hw]
    exact Q.symm w hw
  · intro w hw
    rw [← hτ w hw]
    exact Q.im_posDef w hw
  · intro w hw x
    rw [← hτ w hw]
    exact per_coords bas (L.P w) (Q.τ w) (A (expCover a w)) (Q.symm w hw) (hPa w hw) (hPb w hw) x

def chartS (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (x : Λ)
    (z : Fin n → ℂ) : Fin g → ℂ :=
  (A z)ᵀ *ᵥ (cst (uCo bas x) + T0 z *ᵥ cst (vCo bas x))

def chartW (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Submodule ℤ Λ :=
  LinearMap.ker ((∑ j, B j).mulVecLin ∘ₗ vCo bas)

def chartPer (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : chartW bas B →+ (Fin g → ℂ) :=
  AddMonoidHom.mk' (fun x => chartS bas A T0 (x : Λ) 0) (fun x y => by
    simp only [chartS, Submodule.coe_add, map_add (f := _), cst_add, mulVec_add]
    abel_nf)

def IsKerProj (S : Matrix (Fin g) (Fin g) ℤ) (Pr : Matrix (Fin g) (Fin g) ℝ) : Prop :=
  Pr * Pr = Pr ∧ Prᵀ = Pr ∧ ∀ v : Fin g → ℝ, S.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 ↔ Pr *ᵥ v = v

def compInv (Pr Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℝ :=
  Pr * (Pr * Y * Pr + (1 - Pr))⁻¹ * Pr

def chartQ (Pr : Matrix (Fin g) (Fin g) ℝ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (A z)⁻¹ * (compInv Pr ((T0 z).map Complex.im)).map (fun x : ℝ => (x : ℂ)) * ((A z)ᴴ)⁻¹

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV

theorem isStepRows_stepCols {N j : ℕ} (i : Fin N) : IsStepRows N j i (stepCols N j i) := by
  refine ⟨rfl, ?_⟩
  intro a ha
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  split_ifs at ha ⊢ with h
  · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha.1
  · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minorIJ_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  unfold minorIJ
  split_ifs with e
  · obtain ⟨a, ha, hb⟩ : ∃ a ∈ I, a ∉ J := by
      by_contra hc
      push_neg at hc
      exact h (Finset.eq_of_subset_of_card_le hc e.ge)
    obtain ⟨r, hr⟩ : ∃ r, I.orderEmbOfFin e r = a := by
      have h2 : a ∈ Set.range (I.orderEmbOfFin e) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      exact h2
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, hr]
    exact Matrix.one_apply_ne fun q => hb (q ▸ Finset.orderEmbOfFin_mem _ _ _)
  · rfl

theorem minorIJ_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem sum_minor_one {N : ℕ} (a : Finset (Fin N) → ℂ) (C : Finset (Fin N)) :
    ∑ I, a I * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I C = a C := by
  rw [Finset.sum_eq_single C (fun I _ h => by rw [minorIJ_one_ne h, mul_zero])
    (fun h => absurd (Finset.mem_univ C) h), minorIJ_one_same, mul_one]

theorem sum_minor_mul {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (S : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h) (m : μ) :
    ∑ I, a₁ m I * minorIJ (S * h) I (stepCols N j i) = c * ∑ I, a₂ m I * minorIJ h I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj
  have off' : ∀ I', ¬ IsStepRows N j i I' → minorIJ h I' (stepCols N j i) = 0 := fun I' hI =>
    (off h I' hh hI).resolve_right (stepCols_ne_empty i)
  simp only [cb, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j i I'
  · rw [← mul_assoc, ← hS m I' hI, Finset.sum_mul]
    exact Finset.sum_congr rfl fun I _ => by ring
  · simp [off' I' hI]

theorem coef_ne_zero {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} [Fintype μ] (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (b : μ → ℂ) (S S' : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (hd : IsBlockDiag j S') (hSS : S * S' = 1) (hb : ∑ m, b m * a₁ m (stepCols N j i) = 1) : c ≠ 0 := by
  intro hc
  have h0 : ∀ m, a₁ m (stepCols N j i) = 0 := fun m => by
    have e1 := sum_minor_mul hj i a₁ a₂ S c hS S' hd m
    rw [hSS, hc, zero_mul, sum_minor_one (a₁ m)] at e1
    exact e1
  simp [h0] at hb

theorem map_inv_eq {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} (T : Matrix (Fin N) (Fin N) Ω)
    (hd : T.det ≠ 0) : T⁻¹.map φ = (T.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero φ) (map_one φ)

theorem map_rel {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} {μ : Type}
    (u₁ u₂ : μ → Finset (Fin N) → Ω) (T₁ T₂ : Matrix (Fin N) (Fin N) Ω) (h₁ : T₁.det ≠ 0) (ρ : Ω)
    (P : Finset (Fin N) → Prop)
    (h : ∀ m I', P I' → ∑ I, u₁ m I * minorIJ (T₁⁻¹ * T₂) I I' = ρ * u₂ m I') :
    ∀ m I', P I' → ∑ I, φ (u₁ m I) * minorIJ ((T₁.map φ)⁻¹ * T₂.map φ) I I' = φ ρ * φ (u₂ m I') :=
  fun m I' hI' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_inv_eq φ T₁ h₁, ← Matrix.map_mul, ← map_mul, ← h m I' hI', map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul, minorIJ_map]

section Values

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₂ : Type} [Field Ω₂]
  {x₂ : (Σ k, ι₂ k) → Ω₂} {zb : (Σ k, ι₂ k) → ℂ}

theorem reg_values (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} (i : Fin N) {μ : Type} [Fintype μ]
    (U₁ U₂ : μ → Finset (Fin N) → Ω₂) (V : μ → Ω₂) (A : Matrix (Fin N) (Fin N) Ω₂) (r : Ω₂)
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j i I₀)
    (hU₁ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₁ m I)) (hU₂ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₂ m I))
    (hV : ∀ m, RegAt x₂ (mCoordIdeal zb) (V m)) (hA : ∀ a b, RegAt x₂ (mCoordIdeal zb) (A a b))
    (hrel : ∀ m I', IsStepRows N j i I' → ∑ I, U₁ m I * minorIJ A I I' = r * U₂ m I')
    (hinv : ∑ m, V m * U₂ m I₀ = 1) :
    RegAt x₂ (mCoordIdeal zb) r ∧ ∀ m I', IsStepRows N j i I' →
      ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' = valAt x₂ r zb * valAt x₂ (U₂ m I') zb := by
  have hsum : ∀ m I', RegAt x₂ (mCoordIdeal zb) (∑ I, U₁ m I * minorIJ A I I') ∧
      valAt x₂ (∑ I, U₁ m I * minorIJ A I I') zb =
        ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' := fun m I' => by
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun I => U₁ m I * minorIJ A I I') fun I _ =>
      ValRing.regAt_mul (hU₁ m I) (reg_minor hz hA I I').1
    refine ⟨h1, h2.trans (Finset.sum_congr rfl fun I _ => ?_)⟩
    rw [(reg_mul hz (hU₁ m I) (reg_minor hz hA I I').1).2, (reg_minor hz hA I I').2]
  have hr : RegAt x₂ (mCoordIdeal zb) r := by
    have e : r = ∑ m, V m * ∑ I, U₁ m I * minorIJ A I I₀ := by
      simp only [hrel _ I₀ hI₀]
      calc r = r * ∑ m, V m * U₂ m I₀ := by rw [hinv, mul_one]
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [e]
    exact (reg_sum hz _ _ fun m _ => ValRing.regAt_mul (hV m) (hsum m I₀).1).1
  refine ⟨hr, fun m I' hI' => ?_⟩
  rw [← (hsum m I').2, hrel m I' hI']
  exact (reg_mul hz hr (hU₂ m I')).2

theorem valAt_one' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (1 : Ω₂) zb = 1 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.2.1

theorem valAt_zero' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (0 : Ω₂) zb = 0 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.1

theorem valMat_one (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N : ℕ} :
    valMat x₂ zb (1 : Matrix (Fin N) (Fin N) Ω₂) = 1 := by
  ext a b
  show valAt x₂ ((1 : Matrix (Fin N) (Fin N) Ω₂) a b) zb = _
  by_cases e : a = b
  · subst e
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, valAt_one' hz]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, valAt_zero' hz]

theorem valMat_blockDiag (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} {A : Matrix (Fin N) (Fin N) Ω₂}
    (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x₂ zb A) := fun a b h => by
  show valAt x₂ (A a b) zb = 0
  rw [hA a b h, valAt_zero' hz]

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K₂ _ ι₂ _ Ω₂ _ x₂ φ zb F₁ F₂ hz hF₁ hF₂ hc₁ hc₂ p k hp hu hS
  obtain ⟨ρ, -, hρ⟩ := GlobalTheory.T.frame_change_scalar_factor K ι Φ y Ψ N j M F₁ F₂ hF₁ hF₂ hc₁ hc₂ p k hp
  have hd₁ := (hF₁.1 p.1).2
  have hd₂ := (hF₂.1 p.1).2
  have hstep : IsStepRows N j p.2 (stepCols N j p.2) := isStepRows_stepCols p.2
  have hinv : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F →
      ∑ m : ι k, φ (F.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F.u ⟨k, m⟩ (stepCols N j p.2)) = 1 := fun F hF => by
    have e := hF.2.2.1 p k hp _ _ hstep hstep
    rw [if_pos rfl] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one φ, ← e, map_sum]
    exact Finset.sum_congr rfl fun m _ => (map_mul φ _ _).symm
  have hrel := map_rel φ (fun (m : ι k) I => F₁.u ⟨k, m⟩ I) (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) _ _ hd₁ ρ
    (IsStepRows N j p.2) hρ
  obtain ⟨hr, hval⟩ := reg_values hz p.2 (fun (m : ι k) I => φ (F₁.u ⟨k, m⟩ I))
    (fun (m : ι k) I => φ (F₂.u ⟨k, m⟩ I)) (fun m : ι k => φ (F₂.u' (stepCols N j p.2) ⟨k, m⟩)) _ (φ ρ) _ hstep
    (fun m I => (hu m I).1) (fun m I => (hu m I).2.1) (fun m => (hu m _).2.2.2) (fun a b => (hS a b).1) hrel
    (hinv F₂ hF₂)
  refine ⟨valAt x₂ (φ ρ) zb, ?_, fun h hh m => sum_minor_mul M.j_le p.2 _ _ _ _ hval h hh m⟩
  have hu₂ : IsUnit (F₂.T p.1).det := isUnit_iff_ne_zero.2 hd₂
  have hu₁ : IsUnit (F₁.T p.1).det := isUnit_iff_ne_zero.2 hd₁
  have e21 : ((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ = ((F₂.T p.1)⁻¹ * F₁.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₂]
  have e12 : ((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ = ((F₁.T p.1)⁻¹ * F₂.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₁]
  have hprod : (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) = 1 := by
    rw [e12, e21, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₂,
      Matrix.nonsing_inv_mul _ hu₁]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hbd : IsBlockDiag j (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) := by
    rw [e21]
    exact ((((hF₂.1 p.1).1.inv hu₂).mul (hF₁.1 p.1).1).map φ)
  have hSS := (regMat_mul hz (fun a b => (hS a b).1) (fun a b => (hS a b).2)).2
  rw [hprod, valMat_one hz] at hSS
  refine coef_ne_zero M.j_le p.2 _ _ (fun m : ι k => valAt x₂ (φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩)) zb) _ _ _ hval
    (valMat_blockDiag hz hbd) hSS.symm ?_
  have e := (reg_sum hz Finset.univ
    (fun m : ι k => φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F₁.u ⟨k, m⟩ (stepCols N j p.2)))
    fun m _ => ValRing.regAt_mul (hu m _).2.2.1 (hu m _).1).2
  rw [hinv F₁ hF₁, valAt_one' hz] at e
  rw [e]
  exact Finset.sum_congr rfl fun m _ => (reg_mul hz (hu m _).2.2.1 (hu m _).1).2.symm

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMapStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_under_field_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An

section Loc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}

def LocAn (S : Set E) (z : E) (φ : E → ℂ) : Prop :=
  ∃ f : E → ℂ, AnalyticAt ℂ f z ∧ ∀ᶠ w in 𝓝[S] z, φ w = f w

theorem LocAn.of_analyticAt {φ : E → ℂ} (h : AnalyticAt ℂ φ z) : LocAn S z φ :=
  ⟨φ, h, Eventually.of_forall fun _ => rfl⟩

theorem LocAn.const (c : ℂ) : LocAn S z fun _ => c := .of_analyticAt analyticAt_const

theorem LocAn.add {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w + ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w + g w, hf.add hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.mul {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w * ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w * g w, hf.mul hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.sum {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∑ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.prod {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∏ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.det {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b) :
    LocAn S z fun w => (A w).det := by
  simp only [Matrix.det_apply']
  exact LocAn.sum _ fun σ _ => (LocAn.const _).mul (LocAn.prod _ fun i _ => h _ _)

theorem LocAn.minor {N : ℕ} {A : E → Matrix (Fin N) (Fin N) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b)
    (I J : Finset (Fin N)) : LocAn S z fun w => minorIJ (A w) I J := by
  unfold minorIJ
  split_ifs with e
  · exact LocAn.det fun a b => h _ _
  · exact LocAn.const 0

end Loc

section Val

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem eval_eq_zero_of_mem {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal b) :
    eval b (map (Int.castRingHom ℂ) f) = 0 := by
  have h0 : mConeMap b f = 0 := hf
  have e : ∀ f : MRing ι, eval (fun _ => (1 : ℂ)) (mConeMap b f) = eval b (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      have e1 : eval (fun _ => (1 : ℂ)) (mConeMap b (X q)) = b q := by simp [mConeMap]
      rw [map_mul, map_mul, hp, e1, map_mul, map_mul, map_X, eval_X]
  rw [← e, h0, map_zero]

theorem notMem_of_eval_ne_zero {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : eval b (map (Int.castRingHom ℂ) f) ≠ 0) :
    f ∉ mCoordIdeal b := fun h => hf (eval_eq_zero_of_mem h)

theorem coord_ne_zero_of_notMem {b : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal b) :
    b q ≠ 0 := fun e => h (by
  show mConeMap b (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

theorem analyticAt_eval {σ : Type} {b : E → σ → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (p : MvPolynomial σ ℤ) : AnalyticAt ℂ (fun w => eval (b w) (map (Int.castRingHom ℂ) p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p + q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) + eval (b w) (map (Int.castRingHom ℂ) q) := by
      funext w; rw [map_add (f := _), map_add (f := _)]
    rw [e]; exact hp.add hq
  | mul_X p q hp =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p * X q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) * b w q := by
      funext w; rw [map_mul, map_mul, map_X, eval_X]
    rw [e]; exact hp.mul (hb q)

theorem regAt_eventually {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) : ∀ᶠ w in 𝓝 z, RegAt x (mCoordIdeal (b w)) s := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  filter_upwards [(analyticAt_eval hb h).continuousAt.eventually_ne (ValRing.eval_ne_zero_of_notMem hh hn)] with w hw
  exact ⟨d, g, h, hg, hh, notMem_of_eval_ne_zero hw, heq⟩

theorem locAn_valAt {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hpt : ∀ w ∈ S, b w ∈ mcPts (mCoordIdeal x)) (hz : z ∈ S) {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) :
    LocAn S z fun w => valAt x s (b w) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have hx := ValRing.aeval_ne_zero_of_notMem (hpt z hz) hh hn
  refine ⟨fun w => eval (b w) (map (Int.castRingHom ℂ) g) / eval (b w) (map (Int.castRingHom ℂ) h),
    (analyticAt_eval hb g).div (analyticAt_eval hb h) h0, ?_⟩
  filter_upwards [nhdsWithin_le_nhds ((analyticAt_eval hb h).continuousAt.eventually_ne h0), self_mem_nhdsWithin]
    with w hw hwS
  exact valAt_eq (hpt w hwS) ⟨d, g, h, hg, hh, hx, heq, hw, rfl⟩

end Val

section Good

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Finite Ψ] {N j : ℕ}

theorem goodAt_eventually (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hg : M.GoodAt F (mCoordIdeal (b z))) : ∀ᶠ w in 𝓝 z, M.GoodAt F (mCoordIdeal (b w)) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have A : ∀ᶠ w in 𝓝 z, ∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∉ mCoordIdeal (b w) := by
    refine eventually_all.2 fun k => ?_
    filter_upwards [(hb ⟨k, F.c k⟩).continuousAt.eventually_ne (coord_ne_zero_of_notMem (h1 k))] with w hw
    refine notMem_of_eval_ne_zero ?_
    simpa using hw
  have B : ∀ᶠ w in 𝓝 z, ∀ q I, RegAt M.x (mCoordIdeal (b w)) (F.u q I) ∧ RegAt M.x (mCoordIdeal (b w)) (F.u' I q) :=
    eventually_all.2 fun q => eventually_all.2 fun I =>
      (regAt_eventually hb (h2 q I).1).and (regAt_eventually hb (h2 q I).2)
  have C : ∀ᶠ w in 𝓝 z, ∀ p, M.blk p = none → F.υ p ≠ 0 ∧ RegAt M.x (mCoordIdeal (b w)) (F.υ p) ∧
      RegAt M.x (mCoordIdeal (b w)) (F.υ p)⁻¹ := by
    refine eventually_all.2 fun p => ?_
    by_cases hp : M.blk p = none
    · filter_upwards [regAt_eventually hb (h3 p hp).2.1, regAt_eventually hb (h3 p hp).2.2] with w a c
      exact fun _ => ⟨(h3 p hp).1, a, c⟩
    · exact Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [A, B, C] with w a c d
  exact ⟨a, c, d⟩

end Good

section Img

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

theorem analyticAt_coord (z : (Σ k, ι' k) → ℂ) (q : Σ k, ι' k) :
    AnalyticAt ℂ (fun w : (Σ k, ι' k) → ℂ => w q) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι' k) => ℂ) q).analyticAt z

theorem locAn_img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    {z : (Σ k, ι' k) → ℂ} {F' : FrameData ι' Ψ N M'.Ω M'.blk} {F : FrameData ι Ψ N M.Ω M.blk}
    (hz : z ∈ mcPts (mCoordIdeal y'))
    (hp1 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∈ mcPts (mCoordIdeal M'.x))
    (hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x))
    (hF' : M'.IsFrame F') (hF : M.IsFrame F)
    (hg' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) (q : Σ k, ι k) :
    LocAn (mcPts (mCoordIdeal y')) z fun w => img Cv F' F w q := by
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  obtain ⟨k, m⟩ := q
  by_cases hk : ∀ p, M.blk p ≠ some k
  · refine .of_analyticAt ?_
    have e : (fun w => img Cv F' F w ⟨k, m⟩) = fun w => basePart M'.blk w (Cv.v ⟨⟨k, hk⟩, m⟩) := by
      funext w
      exact congrFun (img_base Cv F' F w) ⟨⟨k, hk⟩, m⟩
    rw [e]
    exact hb _
  · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
    obtain ⟨k', hp'⟩ := exists_blk_cover M' hp
    simp only [img_step Cv F' F _ hp hp' m]
    unfold stepCoord
    refine LocAn.sum _ fun I _ => (locAn_valAt hbv hp2 hz (hg.2.1 _ I).1).mul (LocAn.sum _ fun I' _ => ?_)
    by_cases hI : IsStepRows N j p.2 I'
    · simp only [if_pos hI]
      refine (LocAn.minor (fun a c => ?_) I I').mul
        (LocAn.sum _ fun m' _ => (locAn_valAt hb hp1 hz (hg'.2.1 _ I').2).mul (.of_analyticAt (analyticAt_coord z _)))
      exact locAn_valAt hb hp1 hz (Cv.agree _ (hp1 z hz) F' F hF' hF hg' hg p.1 a c).1
    · simp only [if_neg hI]
      exact LocAn.const 0

end Img

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), z ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), M'.GoodAt F' (mCoordIdeal (basePart M'.blk z')) ∧ M.GoodAt F (mCoordIdeal (basePart M'.blk z' ∘ Cv.v)) ∧ f z' = CovMap.LocImg.img Cv F' F z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F hz hF' hF hg' hg
  have hp1 := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1
  have hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := fun w hw =>
    (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (hp1 w hw)).1
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  choose f hf hev using locAn_img Cv hz hp1 hp2 hF' hF hg' hg
  have e1 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (fun w q => f q w) w :=
    (analyticAt_pi_iff.2 hf).eventually_analyticAt
  have e2 : ∀ᶠ w in 𝓝 z, w ∈ mcPts (mCoordIdeal y') → ∀ q, img Cv F' F w q = f q w :=
    eventually_nhdsWithin_iff.1 (eventually_all.2 hev)
  obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.1
    (e1.and (e2.and ((goodAt_eventually M' F' hb hg').and (goodAt_eventually M F hbv hg))))
  refine ⟨V, fun w q => f q w, hVo, hzV, fun w hw => (hV w hw).1, fun w hw => ?_⟩
  obtain ⟨-, a, c, d⟩ := hV w hw.1
  exact ⟨c, d, funext fun q => (a hw.2 q).symm⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), z ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), M'.GoodAt F' (mCoordIdeal (basePart M'.blk z')) ∧ M.GoodAt F (mCoordIdeal (basePart M'.blk z' ∘ Cv.v)) ∧ f z' = CovMap.LocImg.img Cv F' F z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSup
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSup
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.MinHom

open MvPolynomial ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_of_mem_minimalPrimes_sup :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      IsMultiHomogIdeal P → IsMultiHomogIdeal D →
        ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  intro K _ ι _ P D hP hD Q hQ
  classical
  have toGeo : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), IsMultiHomogIdeal I →
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) I := fun I h => h
  have hQ' : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) Q :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_isHomogeneous fun k =>
      ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes _
        ((ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo P hP) k).sup
          (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo D hD) k)) hQ
  exact hQ'

end GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSupStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_primes_of_multihomog_sup : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | exact GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomial
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomial
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem coord_image (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact renPt_zero (chartIdeal P p) (affCoord p (rep x))
      ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))
  · intro ht
    obtain ⟨w, hwd⟩ : ∃ w, w = t ∘ Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
    have hren : renPt w = t := by
      subst hwd
      funext l
      simp [renPt]
    have hw : ∀ h ∈ chartIdeal P p, eval w h = 0 := by
      intro h hh
      rw [← eval_renC w h, hren]
      exact ht _ (Ideal.mem_map_of_mem _ hh)
    obtain ⟨hc, h1, ha⟩ := conePts_of_chartIdeal hP p w hw
    let x : Pts P := ⟨proj w, w, hc, rfl⟩
    have ho : SameOrbit (rep x) w := sameOrbit_of_proj_eq (rep_mem x).1 hc.1 (proj_rep x)
    refine ⟨x, fun k => ?_, ?_⟩
    · obtain ⟨c, hcn, hcz⟩ := ho
      have hk : rep x ⟨k, p k⟩ = c k * w ⟨k, p k⟩ := congrFun hcz ⟨k, p k⟩
      rw [hk, h1 k, mul_one]
      exact hcn k
    · show renPt (affCoord p (rep x)) = t
      rw [affCoord_eq_of_sameOrbit p ho, ha, hren]

theorem coord_trans (p p' : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p ∩ src P p') :
    ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
      (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
      eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
        ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
  have hev : ∀ (y : Pts P) (q : Σ k, ι k), eval (coord P p y) (X (e q)) = affCoord p (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  have hev' : ∀ (y : Pts P) (q : Σ k, ι k), coord P p' y (e q) = affCoord p' (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  refine ⟨∏ k, X (e ⟨k, p' k⟩),
    fun l => X l * ∏ k ∈ Finset.univ.erase (e.symm l).1, X (e ⟨k, p' k⟩), ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [hev]
    exact div_ne_zero (hx.2 k) (hx.1 k)
  · intro y hy _ l
    obtain ⟨r, rfl⟩ := e.surjective l
    have hprod := Finset.mul_prod_erase Finset.univ
      (fun k => affCoord p (rep y) ⟨k, p' k⟩) (Finset.mem_univ r.1)
    have hA : affCoord p' (rep y) r * affCoord p (rep y) ⟨r.1, p' r.1⟩ = affCoord p (rep y) r := by
      have h1 := hy.1 r.1
      have h2 := hy.2 r.1
      simp only [affCoord]
      field_simp
    simp only [map_prod, map_mul, hev, hev', Equiv.symm_apply_apply]
    rw [← hprod, ← mul_assoc, hA]

theorem chart_image_and_trans (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (∀ p : (k : K) → ι k, coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0}) ∧
    ∀ p p' : (k : K) → ι k, ∀ x ∈ src P p ∩ src P p',
      ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
        (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
        eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
          ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) :=
  ⟨coord_image hP, fun p p' x hx => coord_trans p p' x hx⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomialStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_resolution_transition_polynomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → (∀ p : (k : K) → ι k, SncRes.coord P p '' SncRes.src P p = {t | ∀ h ∈ SncRes.ideal P p, eval t h = 0}) ∧ ∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), eval (SncRes.coord P p x) q ≠ 0 ∧ ∀ y ∈ SncRes.src P p ∩ SncRes.src P p', eval (SncRes.coord P p y) q ≠ 0 → ∀ l, SncRes.coord P p' y l * eval (SncRes.coord P p y) q = eval (SncRes.coord P p y) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalFrameOfTwistGeneration
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalFrameOfTwistGeneration
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem frames_at_point : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] {κ : Type} (x : κ → Ω) (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) (m n r : ℕ) (V : Submodule Ω E)
    (φ : Fin n → Module.Dual Ω E) (cc : Fin r → E) (hV : L.IsVB r V) (hli : LinearIndependent Ω cc)
    (hsp : Submodule.span Ω (Set.range cc) = V) (hG : IsTwistGen ξ x L m φ) (P : Cpt ξ) (c₁ : κ)
    (hc : InChart ξ x c₁ P),
    ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin n) (Fin r) Ω) (B : Matrix (Fin r) (Fin n) Ω),
      T.det ≠ 0 ∧ Matrix.of (fun j a => φ j (cc a)) * T = (x c₁ ^ m) • C ∧ B * C = 1 ∧
        (∀ j a, C j a ∈ regAt ξ P) ∧ ∀ a j, B a j ∈ regAt ξ P := by
  intro X Ω _ ξ E _ _ κ x L m n r V φ cc hV hli hsp hG P c₁ hc
  obtain ⟨U, hPU, b, hbV, hfr⟩ := (show L.IsVBOn Set.univ r V from hV) P (Set.mem_univ _)
  have hbP : L.IsFrameAt b P := hfr P (Set.mem_univ _) hPU
  obtain ⟨B, hBreg, hCreg, hBC⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hG P c₁ hc b hbP
  have hmem : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • cc l = b a := by
    intro a
    have hba : b a ∈ Submodule.span Ω (Set.range cc) := by
      rw [hsp, ← hbV]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 hba
  choose t ht using hmem
  refine ⟨Matrix.of fun l a => t a l, Matrix.of (fun j a => φ j (b a) / x c₁ ^ m), B, ?_, ?_, hBC, ?_, hBreg⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hli_b := hbP.1
    rw [Fintype.linearIndependent_iff] at hli_b
    have hcol : ∀ l, ∑ a, t a l * v a = 0 := fun l => by
      simpa [Matrix.mulVec, dotProduct] using congrFun hv l
    have hsum : ∑ a, v a • b a = 0 := by
      calc ∑ a, v a • b a = ∑ a, v a • ∑ l, t a l • cc l := by simp only [ht]
        _ = ∑ l, (∑ a, t a l * v a) • cc l := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]
        _ = 0 := by simp [hcol]
    exact hv0 (funext fun a => hli_b v hsum a)
  · ext j a
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : ∑ l, φ j (cc l) * t a l = φ j (b a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← ht a, map_sum]
      simp only [map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [h1]
    by_cases hx : x c₁ ^ m = 0
    · exfalso
      have h2 := congrFun (congrFun hBC a) a
      simp [Matrix.mul_apply, hx, Matrix.one_apply] at h2
    · field_simp
  · intro j a
    exact hCreg j a

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalFrameOfTwistGenerationStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_frame_of_twist_generation : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] {κ : Type} (x : κ → Ω) (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) (m n r : ℕ) (V : Submodule Ω E)
    (φ : Fin n → Module.Dual Ω E) (cc : Fin r → E) (hV : L.IsVB r V) (hli : LinearIndependent Ω cc)
    (hsp : Submodule.span Ω (Set.range cc) = V) (hG : IsTwistGen ξ x L m φ) (P : Cpt ξ) (c₁ : κ)
    (hc : InChart ξ x c₁ P),
    ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin n) (Fin r) Ω) (B : Matrix (Fin r) (Fin n) Ω),
      T.det ≠ 0 ∧ Matrix.of (fun j a => φ j (cc a)) * T = (x c₁ ^ m) • C ∧ B * C = 1 ∧
        (∀ j a, C j a ∈ regAt ξ P) ∧ ∀ a j, B a j ∈ regAt ξ P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_at_point | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_at_point <;> assumption)
end
end
