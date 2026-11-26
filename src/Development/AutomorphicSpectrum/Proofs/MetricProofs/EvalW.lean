module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def nS (a : ℂ) (i : Fin 3) : ℝ := (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def wS (a : ℂ) : ℝ := ((1 + ‖a‖ ^ 2) ^ 2)⁻¹

def blk {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of fun p q : Fin (d + 1) =>
    Fin.cases (Fin.cases e (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => B p' q') q) p

def lin3 (n : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ := ∑ i, X i * C (n i)

def lin4 (n : Fin 3 → ℝ) : MvPolynomial (Option (Fin 3)) ℝ := rename some (lin3 n)

def rowW (u : Fin 2 → ℝ) (v : ℝ) : MvPolynomial (Option (Fin 2)) ℝ :=
  C (u 0) * X (some 0) + C (u 1) * X (some 1) + C v * X none

def evalW (n₀ n₁ : Fin 3 → ℝ) : MvPolynomial (Option (Fin 2)) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ :=
  aeval fun j => Option.elim j (X none) ![lin4 n₀, lin4 n₁]

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelOfRiemann
open Matrix Complex

namespace GlobalTheory.CompanionTheory.Ar.Flat

private lemma sr_entry {g : ℕ} (A B Hm : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    (A * Hm * Bᴴ) i j = A i ⬝ᵥ Hm *ᵥ star (B j) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private lemma sr_im_left {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (T : Matrix (Fin g) (Fin g) ℂ) :
    (S.map ofReal * T).map im = S * T.map im := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum]

private lemma sr_re_left {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (T : Matrix (Fin g) (Fin g) ℂ) :
    (S.map ofReal * T).map re = S * T.map re := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum]

private lemma sr_im_mul {g : ℕ} (U T : Matrix (Fin g) (Fin g) ℂ) :
    (U * T).map im = U.map re * T.map im + U.map im * T.map re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib]

theorem siegel_of_riemann : ∀ (g : ℕ) (A Bm Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → (∀ i j, (A i ⬝ᵥ Hm *ᵥ star (A j)).im = 0 ∧ (Bm i ⬝ᵥ Hm *ᵥ star (Bm j)).im = 0 ∧ (A i ⬝ᵥ Hm *ᵥ star (Bm j)).im = if i = j then -1 else 0) → A.det ≠ 0 ∧ (Bm * A⁻¹)ᵀ = Bm * A⁻¹ ∧ ((Bm * A⁻¹).map im).PosDef ∧ A * Hm * Aᴴ = (((Bm * A⁻¹).map im)⁻¹).map ofReal := by
  intro g A Bm Hm hH hpos hrel
  have hPij : ∀ i j, ((A * Hm * Aᴴ) i j).im = 0 := fun i j => by
    rw [sr_entry]
    exact (hrel i j).1
  have hAA : ∀ u v : Fin g → ℝ,
      (((fun i => (u i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (v i : ℂ)) ᵥ* A)).im = 0 := by
    intro u v
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc]
    simp [dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, hPij]
  have hAAre : ∀ u v : Fin g → ℝ,
      (((fun i => (u i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (v i : ℂ)) ᵥ* A)).re =
        u ⬝ᵥ ((A * Hm * Aᴴ).map re) *ᵥ v := by
    intro u v
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc]
    simp [dotProduct, Matrix.mulVec, Complex.re_sum, Complex.mul_re, hPij, Finset.mul_sum]
  have hAB : ∀ (a : Fin g → ℝ) (j : Fin g),
      (((fun i => (a i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star (Bm j)).im = -a j := by
    intro a j
    rw [← Matrix.dotProduct_mulVec]
    have e : ∀ i, (A *ᵥ Hm *ᵥ star (Bm j)) i = A i ⬝ᵥ Hm *ᵥ star (Bm j) := fun i => rfl
    rw [dotProduct, Complex.im_sum]
    simp only [Complex.im_ofReal_mul, e, (hrel _ j).2.2]
    simp
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, ∀ i, a i = (c i).re := ⟨fun i => (c i).re, fun i => rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin g → ℝ, ∀ i, b i = (c i).im := ⟨fun i => (c i).im, fun i => rfl⟩
    have hcab : c = (fun i => (a i : ℂ)) + Complex.I • (fun i => (b i : ℂ)) := by
      funext i
      apply Complex.ext <;> simp [ha, hb]
    have hxa : (fun i => (a i : ℂ)) ᵥ* A = 0 := by
      by_contra hne
      have hp := hpos _ hne
      have hsplit : (fun i => (a i : ℂ)) ᵥ* A = -(Complex.I • ((fun i => (b i : ℂ)) ᵥ* A)) := by
        have h := hc
        rw [hcab, Matrix.add_vecMul, Matrix.smul_vecMul] at h
        exact eq_neg_of_add_eq_zero_left h
      have him := hAA b a
      have e : ((fun i => (a i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (a i : ℂ)) ᵥ* A) =
          -(Complex.I * (((fun i => (b i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (a i : ℂ)) ᵥ* A))) := by
        nth_rewrite 1 [hsplit]
        rw [neg_dotProduct, smul_dotProduct, smul_eq_mul]
      rw [e] at hp
      simp [Complex.mul_re, him] at hp
    have hxb : (fun i => (b i : ℂ)) ᵥ* A = 0 := by
      have h := hc
      rw [hcab, Matrix.add_vecMul, Matrix.smul_vecMul, hxa, zero_add] at h
      exact (smul_eq_zero.1 h).resolve_left Complex.I_ne_zero
    have ha0 : ∀ j, a j = 0 := fun j => by
      have h := hAB a j
      rw [hxa, zero_dotProduct] at h
      simpa using h
    have hb0 : ∀ j, b j = 0 := fun j => by
      have h := hAB b j
      rw [hxb, zero_dotProduct] at h
      simpa using h
    apply hc0
    funext i
    apply Complex.ext
    · rw [← ha i, ha0 i]
      simp
    · rw [← hb i, hb0 i]
      simp
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  set Z := Bm * A⁻¹ with hZ
  have hB : Bm = Z * A := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
  have hR : A * Hm * Bmᴴ = A * Hm * Aᴴ * Zᴴ := by
    rw [hB, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hPc : A * Hm * Aᴴ = ((A * Hm * Aᴴ).map re).map ofReal := by
    ext i j
    apply Complex.ext
    · simp
    · simp [hPij i j]
  have hPH : (A * Hm * Aᴴ)ᴴ = A * Hm * Aᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq,
      Matrix.mul_assoc]
  have hPrT : ((A * Hm * Aᴴ).map re)ᵀ = (A * Hm * Aᴴ).map re := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    have h := congrFun (congrFun hPH j) i
    rw [Matrix.conjTranspose_apply] at h
    rw [← h]
    simp [Complex.star_def]
  have hRim : (A * Hm * Bmᴴ).map im = -1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
    rw [sr_entry, (hrel i j).2.2]
    split_ifs <;> simp
  have hZH : (Zᴴ).map im = -(Z.map im)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Complex.star_def]
  have hZHre : (Zᴴ).map re = (Z.map re)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Complex.star_def]
  have hPY : (A * Hm * Aᴴ).map re * (Z.map im)ᵀ = 1 := by
    have h := hRim
    rw [hR, hPc, sr_im_left, hZH, Matrix.mul_neg] at h
    exact neg_inj.1 h
  have hPu : IsUnit ((A * Hm * Aᴴ).map re).det := Matrix.isUnit_det_of_right_inverse hPY
  have hYT : (Z.map im)ᵀ = ((A * Hm * Aᴴ).map re)⁻¹ := (Matrix.inv_eq_right_inv hPY).symm
  have hY : Z.map im = ((A * Hm * Aᴴ).map re)⁻¹ := by
    rw [← Matrix.transpose_transpose (Z.map im), hYT, Matrix.transpose_nonsing_inv, hPrT]
  have hPrpos : ((A * Hm * Aᴴ).map re).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hPrT
    · have hne : (fun i => (x i : ℂ)) ᵥ* A ≠ 0 := by
        intro h0
        apply hx
        have h1 : (fun i => (x i : ℂ)) = 0 := by
          have h2 := congrArg (fun v => v ᵥ* A⁻¹) h0
          simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hAu, Matrix.vecMul_one,
            Matrix.zero_vecMul] at h2
          exact h2
        funext i
        have h3 := congrFun h1 i
        simpa using h3
      have h := hpos _ hne
      rw [hAAre] at h
      simpa using h
  have hPinv : ((A * Hm * Aᴴ).map re)⁻¹ * (A * Hm * Aᴴ).map re = 1 :=
    Matrix.nonsing_inv_mul _ hPu
  have hQ : Bm * Hm * Bmᴴ = Z * (A * Hm * Bmᴴ) := by
    calc Bm * Hm * Bmᴴ = Z * A * Hm * Bmᴴ := by rw [← hB]
      _ = Z * (A * Hm * Bmᴴ) := by simp only [Matrix.mul_assoc]
  have hQim : (Bm * Hm * Bmᴴ).map im = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [sr_entry]
    exact (hrel i j).2.1
  have hX : (Z.map re)ᵀ = Z.map re := by
    have h := hQim
    rw [hQ, sr_im_mul, hRim, hR, hPc, sr_re_left, hZHre, hY, ← Matrix.mul_assoc, hPinv, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one] at h
    exact (neg_add_eq_zero.1 h).symm
  have hYsym : (Z.map im)ᵀ = Z.map im := by rw [hYT, hY]
  have hZT : Zᵀ = Z := by
    ext i j
    apply Complex.ext
    · have h := congrFun (congrFun hX i) j
      simpa using h
    · have h := congrFun (congrFun hYsym i) j
      simpa using h
  refine ⟨hdet, hZT, ?_, ?_⟩
  · rw [hY]
    exact hPrpos.inv
  · rw [hY, Matrix.nonsing_inv_nonsing_inv _ hPu]
    exact hPc

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

open MeasureTheory Real

def punct {n : ℕ} (R : ℝ) : Set (Fin n → ℂ) := {z | ∀ i, z i ≠ 0 ∧ ‖z i‖ < R}

def pker (ρ : ℝ) (w : ℂ) (t : ℝ) : ℝ := poissonKernel 0 w (circleMap 0 ρ t)

def angMeas : Measure ℝ := ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Set.Ioc 0 (2 * π))

instance : IsProbabilityMeasure angMeas := ⟨by
  have h : (0 : ℝ) < 2 * π := by positivity
  simp only [angMeas, Measure.smul_apply, Measure.restrict_apply, MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h.ne', ENNReal.ofReal_one]⟩

theorem integral_angMeas (F : ℂ → ℝ) (ρ : ℝ) :
    ∫ t, F (circleMap 0 ρ t) ∂angMeas = Real.circleAverage F 0 ρ := by
  have h : (0 : ℝ) < 2 * π := by positivity
  rw [angMeas, integral_smul_measure, Real.circleAverage_def,
    intervalIntegral.integral_of_le h.le, ENNReal.toReal_ofReal (by positivity)]

def torusPt {n : ℕ} (ρ : ℝ) (θ : Fin n → ℝ) : Fin n → ℂ := fun i => circleMap 0 ρ (θ i)

def polyPoisson {n : ℕ} (ρ : ℝ) (h : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  ∫ θ, (∏ i, pker ρ (z i) (θ i)) * h (torusPt ρ θ) ∂(Measure.pi fun _ : Fin n => angMeas)

def SepHarm {n : ℕ} (R : ℝ) (f : (Fin n → ℂ) → ℝ) : Prop :=
  ∀ z ∈ punct R, ∀ i, InnerProductSpace.HarmonicAt (fun t : ℂ => f (Function.update z i t)) (z i)

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactSphere
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.GramCompact

private theorem exists_sum_norm_sq_eq_one_and_eq_sqrt_smul {m : Type} [Fintype m] (w : m → ℂ)
    (hw : 0 < ∑ k, ‖w k‖ ^ 2) :
    ∃ v : m → ℂ, ∑ k, ‖v k‖ ^ 2 = 1 ∧
      w = ((Real.sqrt (∑ k, ‖w k‖ ^ 2) : ℝ) : ℂ) • v := by
  have ht : 0 < Real.sqrt (∑ k, ‖w k‖ ^ 2) := Real.sqrt_pos.mpr hw
  have ht2 : Real.sqrt (∑ k, ‖w k‖ ^ 2) ^ 2 = ∑ k, ‖w k‖ ^ 2 := Real.sq_sqrt hw.le
  refine ⟨(((Real.sqrt (∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) • w, ?_, ?_⟩
  · have h : ∀ k, ‖((((Real.sqrt (∑ j, ‖w j‖ ^ 2))⁻¹ : ℝ) : ℂ) • w) k‖ ^ 2 =
        (Real.sqrt (∑ j, ‖w j‖ ^ 2) ^ 2)⁻¹ * ‖w k‖ ^ 2 := by
      intro k
      rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    simp only [h]
    rw [← Finset.mul_sum, ht2, inv_mul_cancel₀ hw.ne']
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]

private theorem continuousOn_re_star_dotProduct_mulVec {X : Type} [TopologicalSpace X] {K : Set X}
    {m : Type} [Fintype m] {H : X → Matrix m m ℂ} (hH : ContinuousOn H K) (T : Set (m → ℂ)) :
    ContinuousOn (fun p : X × (m → ℂ) => (star p.2 ⬝ᵥ (H p.1 *ᵥ p.2)).re) (K ×ˢ T) := by
  have hd : Continuous (fun q : Matrix m m ℂ × (m → ℂ) => star q.2 ⬝ᵥ (q.1 *ᵥ q.2)) := by
    apply Continuous.dotProduct
    · exact continuous_snd.star
    · exact Continuous.matrix_mulVec continuous_fst continuous_snd
  have hfst : ContinuousOn (H ∘ Prod.fst) (K ×ˢ T) :=
    ContinuousOn.comp hH continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  have h2 : ContinuousOn (fun p : X × (m → ℂ) => ((H ∘ Prod.fst) p, p.2)) (K ×ˢ T) :=
    ContinuousOn.prodMk hfst continuousOn_snd
  have h3 := Continuous.comp_continuousOn (Continuous.comp Complex.continuous_re hd) h2
  exact h3

theorem isCompact_sphere (m : Type) [Fintype m] :
    IsCompact {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : m → ℂ)) (r := 1)).subset ?_
    intro w hw
    have hw' : ∑ k, ‖w k‖ ^ 2 = 1 := hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have h1 : ‖w k‖ ^ 2 ≤ 1 := by
      calc ‖w k‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
              (Finset.mem_univ k)
        _ = 1 := hw'
    nlinarith [norm_nonneg (w k)]

theorem form_smul {m : Type} [Fintype m] (A : Matrix m m ℂ) (r : ℝ) (w : m → ℂ) :
    (star ((r : ℂ) • w) ⬝ᵥ (A *ᵥ ((r : ℂ) • w))).re = r ^ 2 * (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hs : star ((r : ℂ) • w) = (r : ℂ) • star w := by
    ext k
    simp
  rw [hs, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem exists_bounds (X : Type) [TopologicalSpace X] (K : Set X) (m : Type) [Fintype m]
    [DecidableEq m] (H : X → Matrix m m ℂ) (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ∀ w : m → ℂ,
      C⁻¹ * ∑ k, ‖w k‖ ^ 2 ≤ (star w ⬝ᵥ (H x *ᵥ w)).re ∧
        (star w ⬝ᵥ (H x *ᵥ w)).re ≤ C * ∑ k, ‖w k‖ ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T : Set (m → ℂ), T = {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := ⟨_, rfl⟩
  have hKS : IsCompact (K ×ˢ T) := hT ▸ hK.prod (GlobalTheory.CompanionTheory.GramCompact.isCompact_sphere m)
  have hfc := continuousOn_re_star_dotProduct_mulVec hH T
  have hfpos : ∀ x ∈ K, ∀ w ∈ T, 0 < (star w ⬝ᵥ (H x *ᵥ w)).re := by
    intro x hx w hw
    rw [hT, Set.mem_setOf_eq] at hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    exact (Complex.pos_iff.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp (hpos x hx)).2 hw0)).1
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ w ∈ T,
      c ≤ (star w ⬝ᵥ (H x *ᵥ w)).re := by
    rcases (K ×ˢ T).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun x hx w hw => ?_⟩
      have hm : (x, w) ∈ K ×ˢ T := Set.mk_mem_prod hx hw
      rw [h] at hm
      exact absurd hm (Set.notMem_empty _)
    · obtain ⟨p₀, hp₀, hmin⟩ := hKS.exists_isMinOn h hfc
      refine ⟨_, hfpos p₀.1 (Set.mem_prod.mp hp₀).1 p₀.2 (Set.mem_prod.mp hp₀).2,
        fun x hx w hw => ?_⟩
      exact hmin (Set.mk_mem_prod hx hw)
  obtain ⟨M, hM⟩ := hKS.exists_bound_of_continuousOn hfc
  have hC1 : c⁻¹ ≤ max 1 (max c⁻¹ M) := (le_max_left _ _).trans (le_max_right _ _)
  have hCM : M ≤ max 1 (max c⁻¹ M) := (le_max_right _ _).trans (le_max_right _ _)
  have hCc : (max 1 (max c⁻¹ M))⁻¹ ≤ c := inv_le_of_inv_le₀ hc0 hC1
  refine ⟨max 1 (max c⁻¹ M), le_max_left _ _, ?_⟩
  intro x hx w
  have hs0 : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun k _ => by positivity)
  rcases hs0.eq_or_lt with hs | hspos
  · have hw : w = 0 := by
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hs.symm k
        (Finset.mem_univ k)
      simpa using this
    subst hw
    simp
  · obtain ⟨v, hv1, hwv⟩ := exists_sum_norm_sq_eq_one_and_eq_sqrt_smul w hspos
    have hvT : v ∈ T := by
      rw [hT]
      exact hv1
    have hq : (star w ⬝ᵥ (H x *ᵥ w)).re =
        (∑ k, ‖w k‖ ^ 2) * (star v ⬝ᵥ (H x *ᵥ v)).re := by
      conv_lhs => rw [hwv]
      rw [GlobalTheory.CompanionTheory.GramCompact.form_smul, Real.sq_sqrt hs0]
    have h1 : c ≤ (star v ⬝ᵥ (H x *ᵥ v)).re := hc x hx v hvT
    have h2 : (star v ⬝ᵥ (H x *ᵥ v)).re ≤ M := by
      have h3 : ‖(star v ⬝ᵥ (H x *ᵥ v)).re‖ ≤ M := hM (x, v) (Set.mk_mem_prod hx hvT)
      rw [Real.norm_eq_abs] at h3
      exact (le_abs_self _).trans h3
    rw [hq]
    have h4 := mul_le_mul_of_nonneg_right hCc hspos.le
    have h5 := mul_le_mul_of_nonneg_right h1 hspos.le
    have h6 := mul_le_mul_of_nonneg_right (h2.trans hCM) hspos.le
    constructor
    · linarith
    · linarith

end GlobalTheory.CompanionTheory.GramCompact
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MulVecEqZeroOfPair
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.PeriodLimit

theorem sq_mul_sum_sq_le {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (h : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (v : Fin g → ℝ) :
    c ^ 2 * ∑ k, v k ^ 2 ≤ ∑ k, (Y *ᵥ v) k ^ 2 := by
  have h1 := h.dotProduct_mulVec_nonneg v
  rw [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul] at h1
  have h2 : 0 ≤ ∑ k, (c * v k - (Y *ᵥ v) k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h3 : ∑ k, (c * v k - (Y *ᵥ v) k) ^ 2
      = c ^ 2 * ∑ k, v k ^ 2 - 2 * c * (v ⬝ᵥ (Y *ᵥ v)) + ∑ k, (Y *ᵥ v) k ^ 2 := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : v ⬝ᵥ v = ∑ k, v k ^ 2 := by simp [dotProduct, sq]
  rw [h4, smul_eq_mul] at h1
  nlinarith [mul_nonneg hc.le h1]

theorem coord_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (l : Fin a → ℂ) (v : Fin g → ℤ) (k : Fin g) :
    2 * Real.pi * Complex.I * (((T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k)
      = 2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k
        + ∑ j, (((B j *ᵥ v) k : ℤ) : ℂ) * l j := by
  have h : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [add_mulVec, sum_mulVec, Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have : (((B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k
      = (((B j *ᵥ v) k : ℤ) : ℂ) := by
    simp [mulVec, dotProduct]
  rw [this]
  field_simp

theorem exp_coord_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (l : Fin a → ℂ) (u v : Fin g → ℤ) (k : Fin g) :
    Complex.exp (2 * Real.pi * Complex.I * (((fun k => (u k : ℂ)) +
        (T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k))
      = Complex.exp (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k)
        * ∏ j, Complex.exp (l j) ^ ((B j *ᵥ v) k) := by
  rw [Pi.add_apply, mul_add, coord_eq, Complex.exp_add, Complex.exp_add, mul_comm _ (u k : ℂ),
    Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_sum]
  simp only [Complex.exp_int_mul]

theorem exp_pair_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (l : Fin a → ℂ) (u v : Fin g → ℤ) :
    Complex.exp (∑ k, (v k : ℂ) * (2 * Real.pi * Complex.I * (((fun k => (u k : ℂ)) +
        (T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k)))
      = Complex.exp (∑ k, (v k : ℂ) *
          (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k))
        * ∏ j, Complex.exp (l j) ^ (v ⬝ᵥ (B j *ᵥ v)) := by
  simp only [Complex.exp_sum, Complex.exp_int_mul, exp_coord_eq, mul_zpow,
    Finset.prod_mul_distrib]
  congr 1
  simp only [← Finset.prod_zpow, ← _root_.zpow_mul, ← Complex.exp_int_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_sum]
  congr 1
  simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cast_pair {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    star (fun k => (v k : ℝ)) ⬝ᵥ ((B.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun k => (v k : ℝ)))
      = ((v ⬝ᵥ (B *ᵥ v) : ℤ) : ℝ) := by
  simp [mulVec, dotProduct]

theorem pair_nonneg {g : ℕ} {B : Matrix (Fin g) (Fin g) ℤ}
    (h : (B.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) : 0 ≤ v ⬝ᵥ (B *ᵥ v) := by
  have := h.dotProduct_mulVec_nonneg (fun k => (v k : ℝ))
  rw [cast_pair] at this
  exact_mod_cast this

theorem mulVec_eq_zero_of_pair {g : ℕ} {B : Matrix (Fin g) (Fin g) ℤ}
    (h : (B.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) (h0 : v ⬝ᵥ (B *ᵥ v) = 0) :
    B *ᵥ v = 0 := by
  have := (h.dotProduct_mulVec_zero_iff (x := fun k => (v k : ℝ))).1
    (by rw [cast_pair, h0]; simp)
  ext k
  have h1 := congrFun this k
  have h2 : ((B.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun k => (v k : ℝ))) k
      = (((B *ᵥ v) k : ℤ) : ℝ) := by
    simp [mulVec, dotProduct]
  rw [h2, Pi.zero_apply] at h1
  exact_mod_cast h1

theorem finite_sum_sq_le {g : ℕ} (M : ℝ) :
    {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin g => Set.finite_Icc (-⌈M⌉) ⌈M⌉)).subset ?_
  intro v hv k
  have h1 : (v k : ℝ) ^ 2 ≤ M :=
    (Finset.single_le_sum (f := fun k => (v k : ℝ) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ k)).trans hv
  have h2 : v k ^ 2 ≤ ⌈M⌉ := by
    have := h1.trans (Int.le_ceil M)
    exact_mod_cast this
  constructor <;> nlinarith [sq_nonneg (v k), sq_nonneg (2 * v k - 1), sq_nonneg (2 * v k + 1), Int.le_self_sq (v k), Int.le_self_sq (-v k)]

theorem im_period {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℤ) (k : Fin g) :
    ((A.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k
      = ((((fun k => (u k : ℂ)) + A *ᵥ (fun k => (v k : ℂ)) : Fin g → ℂ)) k).im := by
  simp [mulVec, dotProduct]

theorem limit_period : ∀ (n a g : ℕ) (ha : a ≤ n) (U : Set (Fin n → ℂ)) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c : ℝ), IsOpen U → ContinuousOn τ0 U → (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → 0 < c → (∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, Complex.exp (l j) = z (Fin.castLE ha j)) → ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → ∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, z (Fin.castLE ha j) ≠ 0 → Complex.exp (l j) = z (Fin.castLE ha j)) → (∀ j, z (Fin.castLE ha j) = 0 → l j = 0) → ∀ w : Fin g → ℂ, (z, w) ∈ closure {p : (Fin n → ℂ) × (Fin g → ℂ) | p.1 ∈ U ∧ ∃ (l' : Fin a → ℂ) (u v : Fin g → ℤ), (∀ j, Complex.exp (l' j) = p.1 (Fin.castLE ha j)) ∧ p.2 = (fun k => (u k : ℂ)) + (τ0 p.1 + ∑ j, (l' j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))} → ∃ u v : Fin g → ℤ, (∀ j, z (Fin.castLE ha j) = 0 → B j *ᵥ v = 0) ∧ w = (fun k => (u k : ℂ)) + (τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ)) := by
  intro n a g ha U τ0 B c hU hτ hB hc hY z hz l hl hl0 w hw
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.1 hw
  choose hpU l' u v hl' hpw using hp
  have hz' : Tendsto (fun m => (p m).1) atTop (𝓝 z) := (continuous_fst.tendsto _).comp hlim
  have hw' : Tendsto (fun m => (p m).2) atTop (𝓝 w) := (continuous_snd.tendsto _).comp hlim
  have hτ' : Tendsto (fun m => τ0 (p m).1) atTop (𝓝 (τ0 z)) :=
    ((hτ.continuousAt (hU.mem_nhds hz)).tendsto).comp hz'

  have hbd : ∀ m, c ^ 2 * ∑ k, (v m k : ℝ) ^ 2 ≤ ∑ k, ((p m).2 k).im ^ 2 := by
    intro m
    have := sq_mul_sum_sq_le _ hc (hY _ (hpU m) (l' m) (hl' m)) (fun k => (v m k : ℝ))
    simp only [im_period _ (u m)] at this
    rw [← hpw m] at this
    exact this
  have hcont : Continuous fun x : Fin g → ℂ => ∑ k, (x k).im ^ 2 := by fun_prop
  obtain ⟨M, hM⟩ := ((hcont.tendsto w).comp hw').bddAbove_range
  have hfin : ∀ m, v m ∈ {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M / c ^ 2} := by
    intro m
    rw [Set.mem_setOf_eq, le_div_iff₀ (by positivity), mul_comm]
    exact (hbd m).trans (hM ⟨m, rfl⟩)
  obtain ⟨v0, hv0⟩ : ∃ v0, ∃ᶠ m in atTop, v m = v0 := by
    have h1 : ∃ᶠ m in atTop, ∃ v0 ∈ {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M / c ^ 2}, v m = v0 :=
      Frequently.of_forall fun m => ⟨v m, hfin m, rfl⟩
    obtain ⟨v0, -, h⟩ := (frequently_exists_finite (finite_sum_sq_le _)).1 h1
    exact ⟨v0, h⟩
  obtain ⟨φ, hφ, hφv⟩ := extraction_of_frequently_atTop hv0
  have hz2 := hz'.comp hφ.tendsto_atTop
  have hw2 := hw'.comp hφ.tendsto_atTop
  have hτ2 := hτ'.comp hφ.tendsto_atTop
  have hzj : ∀ j : Fin a, Tendsto (fun m => (p (φ m)).1 (Fin.castLE ha j)) atTop
      (𝓝 (z (Fin.castLE ha j))) := fun j => ((continuous_apply _).tendsto _).comp hz2

  have hpair : Complex.exp (∑ k, (v0 k : ℂ) * (2 * Real.pi * Complex.I * w k))
      = Complex.exp (∑ k, (v0 k : ℂ) *
          (2 * Real.pi * Complex.I * (τ0 z *ᵥ (fun k => (v0 k : ℂ))) k))
        * ∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)) := by
    have c1 : Continuous fun x : Fin g → ℂ =>
        Complex.exp (∑ k, (v0 k : ℂ) * (2 * Real.pi * Complex.I * x k)) := by fun_prop
    have c2 : Continuous fun T : Matrix (Fin g) (Fin g) ℂ => Complex.exp (∑ k, (v0 k : ℂ) *
          (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v0 k : ℂ))) k)) := by
      simp only [mulVec, dotProduct]; fun_prop
    have t3 : Tendsto (fun m => ∏ j, (p (φ m)).1 (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0))) atTop
        (𝓝 (∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)))) := by
      refine tendsto_finsetProd _ fun j _ => ?_
      obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (pair_nonneg (hB j) v0)
      simp only [hb, zpow_natCast]
      exact (hzj j).pow b
    refine tendsto_nhds_unique ((c1.tendsto w).comp hw2)
      ((((c2.tendsto _).comp hτ2).mul t3).congr fun m => ?_)
    simp only [Function.comp]
    rw [hpw (φ m), hφv m, exp_pair_eq]
    simp only [hl']
  have hker : ∀ j, z (Fin.castLE ha j) = 0 → B j *ᵥ v0 = 0 := by
    intro j hj
    refine mulVec_eq_zero_of_pair (hB j) v0 ?_
    by_contra hne
    have : ∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, _root_.zero_zpow _ hne])
    rw [this, mul_zero] at hpair
    exact Complex.exp_ne_zero _ hpair

  have hcoord : ∀ k, Complex.exp (2 * Real.pi * Complex.I * w k)
      = Complex.exp (2 * Real.pi * Complex.I * (τ0 z *ᵥ (fun k => (v0 k : ℂ))) k)
        * ∏ j, Complex.exp (l j) ^ ((B j *ᵥ v0) k) := by
    intro k
    have c1 : Continuous fun x : Fin g → ℂ =>
        Complex.exp (2 * Real.pi * Complex.I * x k) := by fun_prop
    have c2 : Continuous fun T : Matrix (Fin g) (Fin g) ℂ =>
        Complex.exp (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v0 k : ℂ))) k) := by
      simp only [mulVec, dotProduct]; fun_prop
    have t3 : Tendsto (fun m => ∏ j, (p (φ m)).1 (Fin.castLE ha j) ^ ((B j *ᵥ v0) k)) atTop
        (𝓝 (∏ j, Complex.exp (l j) ^ ((B j *ᵥ v0) k))) := by
      refine tendsto_finsetProd _ fun j _ => ?_
      by_cases hj : z (Fin.castLE ha j) = 0
      · simp [hker j hj]
      · rw [hl j hj]
        exact (hzj j).zpow₀ _ (Or.inl hj)
    refine tendsto_nhds_unique ((c1.tendsto w).comp hw2)
      ((((c2.tendsto _).comp hτ2).mul t3).congr fun m => ?_)
    simp only [Function.comp]
    rw [hpw (φ m), hφv m, exp_coord_eq]
    simp only [hl']
  have hint : ∀ k, ∃ N : ℤ, w k = N + ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
      (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v0 k : ℂ))) k := by
    intro k
    have h1 := hcoord k
    rw [← exp_coord_eq _ _ _ 0, Complex.exp_eq_exp_iff_exists_int] at h1
    obtain ⟨N, hN⟩ := h1
    refine ⟨N, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
    rw [hN]
    simp only [Pi.add_apply, Pi.zero_apply, Int.cast_zero, zero_add]
    ring
  choose u0 hu0 using hint
  exact ⟨u0, v0, hker, funext hu0⟩

end GlobalTheory.CompanionTheory.PeriodLimit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalNormOutsideFiniteSet
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.LogLin

theorem exists_log_affine_le : ∀ C n K : ℝ, 0 ≤ C → 0 ≤ n → 0 ≤ K → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ K ≤ C₁ ∧ ∀ x y : ℝ, -K ≤ x → y ≤ n * x + C → C * Real.log (2 + C + max y 0) + C ≤ C₁ * Real.log (2 + C₁ + x) := by
  intro C n K hC hn hK
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 + 2 * C + n := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; linarith
  have hCA : 0 ≤ C * A := mul_nonneg hC hA0.le
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 + K + C + 2 * (C * A + C) := ⟨_, rfl⟩
  refine ⟨D, by rw [hD]; linarith, by rw [hD]; linarith, ?_⟩
  intro x y hx hy
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 + D + x := ⟨_, rfl⟩
  rw [← hu]
  have ht : 0 ≤ x + K := by linarith
  have hut : 2 + (x + K) ≤ u := by rw [hu, hD]; linarith
  have hu2 : 2 ≤ u := by linarith
  have hnK : 0 ≤ n * K := mul_nonneg hn hK
  have hnt : 0 ≤ n * (x + K) := mul_nonneg hn ht
  have hmax : max y 0 ≤ n * (x + K) + C := max_le (by nlinarith) (by linarith)
  have hm0 : 0 ≤ max y 0 := le_max_right _ _
  have h1 : n * (x + K) ≤ n * u := mul_le_mul_of_nonneg_left (by linarith) hn
  have h2 : C * 1 ≤ C * u := mul_le_mul_of_nonneg_left (by linarith) hC
  have hle : 2 + C + max y 0 ≤ A * u := by rw [hA]; nlinarith
  have hlog : Real.log (2 + C + max y 0) ≤ Real.log A + Real.log u := by
    rw [← Real.log_mul hA0.ne' (by linarith)]
    exact Real.log_le_log (by linarith) hle
  have hlA : Real.log A ≤ A := (Real.log_le_sub_one_of_pos hA0).trans (by linarith)
  have hlu : 1 / 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) hu2
    have h' := Real.log_two_gt_d9
    linarith
  have h3 : C * Real.log (2 + C + max y 0) ≤ C * (A + Real.log u) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have h4 : 2 * (C * A + C) * (1 / 2) ≤ 2 * (C * A + C) * Real.log u :=
    mul_le_mul_of_nonneg_left hlu (by linarith)
  have h5 : 0 ≤ (1 + K) * Real.log u := mul_nonneg (by linarith) (by linarith)
  rw [hD]
  nlinarith

end GlobalTheory.CompanionTheory.LogLin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ImLowerOnKernel
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ChartBlockLower

private theorem dotProduct_sum' {g a : ℕ} (v : Fin g → ℝ) (w : Fin a → Fin g → ℝ) :
    v ⬝ᵥ (∑ j, w j) = ∑ j, v ⬝ᵥ w j := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem quad_im_add_sum {a g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (s : Fin a → ℂ) (v : Fin g → ℝ) :
    v ⬝ᵥ (((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v)
      = v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)
        + ∑ j, (s j).im * (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
  have h : ((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im)
      = τ.map Complex.im + ∑ j, (s j).im • (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext i k
    simp [Matrix.sum_apply, Complex.im_sum]
  rw [h, Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum']
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem im_lower_on_kernel : ∀ (n a g : ℕ) (ha : a ≤ n) (U : Set (Fin n → ℂ)) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c : ℝ), IsOpen U → ContinuousOn τ0 U → (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → 0 < c → (∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, Complex.exp (l j) = z (Fin.castLE ha j)) → ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → ∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, z (Fin.castLE ha j) ≠ 0 → Complex.exp (l j) = z (Fin.castLE ha j)) → (∀ j, z (Fin.castLE ha j) = 0 → l j = 0) → ∀ v : Fin g → ℝ, (∀ j, z (Fin.castLE ha j) = 0 → (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v) := by
  intro n a g ha U τ0 B c hU hτ _ _ H z hz l hl _ v hv
  classical
  let l' : ℝ → Fin a → ℂ := fun t j => if z (Fin.castLE ha j) = 0 then -(t : ℂ) else l j
  let z' : ℝ → Fin n → ℂ := fun t i => if z i = 0 then Complex.exp (-(t : ℂ)) else z i
  have hT : Filter.Tendsto z' Filter.atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hzi : z i = 0
    · have h1 : Filter.Tendsto (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) Filter.atTop
          (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      have h2 : (fun t : ℝ => z' t i) = fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) := by
        funext t
        simp [z', hzi, Complex.ofReal_exp]
      rw [h2, hzi]
      simpa using h1
    · have h2 : (fun t : ℝ => z' t i) = fun _ : ℝ => z i := by
        funext t
        simp [z', hzi]
      rw [h2]
      exact tendsto_const_nhds
  have hτc : ContinuousAt τ0 z := hτ.continuousAt (hU.mem_nhds hz)
  let φ : Matrix (Fin g) (Fin g) ℂ → ℝ := fun M => v ⬝ᵥ ((M.map Complex.im) *ᵥ v)
  have hφ : Continuous φ :=
    continuous_const.dotProduct
      ((continuous_id.matrix_map Complex.continuous_im).matrix_mulVec continuous_const)
  have hsplit : ∀ (w : Fin n → ℂ) (m : Fin a → ℂ),
      v ⬝ᵥ (((τ0 w + ∑ j, (m j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
          Complex.im) *ᵥ v)
        = φ (τ0 w) + ∑ j, (m j / (2 * Real.pi * Complex.I)).im *
            (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) :=
    fun w m => quad_im_add_sum (τ0 w) B (fun j => m j / (2 * Real.pi * Complex.I)) v
  have hsum : ∀ t : ℝ, ∑ j, (l' t j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))
      = ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    intro t
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hzj : z (Fin.castLE ha j) = 0
    · rw [hv j hzj]
      simp
    · simp [l', hzj]
  have hev : ∀ᶠ t in Filter.atTop, c * (v ⬝ᵥ v) ≤ φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    filter_upwards [hT.eventually_mem (hU.mem_nhds hz)] with t ht
    have hexp : ∀ j, Complex.exp (l' t j) = z' t (Fin.castLE ha j) := by
      intro j
      by_cases hzj : z (Fin.castLE ha j) = 0
      · simp [l', z', hzj]
      · simp [l', z', hzj, hl j hzj]
    have h0 := (H (z' t) ht (l' t) hexp).dotProduct_mulVec_nonneg v
    have hstar : star v = v := by
      funext i
      exact TrivialStar.star_trivial _
    rw [hstar, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hsplit, hsum] at h0
    linarith
  have hlim : Filter.Tendsto (fun t => φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))) Filter.atTop
      (𝓝 (φ (τ0 z) + ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)))) :=
    ((hφ.tendsto _).comp (hτc.tendsto.comp hT)).add tendsto_const_nhds
  rw [hsplit]
  exact ge_of_tendsto hlim hev

end GlobalTheory.CompanionTheory.ChartBlockLower
end
