module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module

noncomputable section

theorem card_le_of_separated_of_norm_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (s : Finset W) {lam r : ℝ} (hlam : 0 < lam) (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → lam ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 * r / lam) ^ finrank ℝ W := by
  classical
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set μ : Measure W := (Module.finBasis ℝ W).addHaar with hμ
  have hl2 : 0 < lam / 2 := half_pos hlam
  have hdisj : Set.PairwiseDisjoint (s : Set W) fun w => ball w (lam / 2) := by
    intro w hw w' hw' hne
    apply ball_disjoint_ball
    rw [add_halves, dist_eq_norm]
    exact hsep w hw w' hw' hne
  have hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : W) (r + lam / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hxw
    calc ‖x‖ = ‖w + (x - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
      _ < r + lam / 2 := by linarith [hs w hw]
  have hmeas := measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball
  have hle := measure_mono (μ := μ) hsubset
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)] at hle
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle' := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hle
  rw [show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)] at hle'
  have hpos : 0 < (lam / 2) ^ finrank ℝ W := by positivity
  have key : (1 + 2 * r / lam) ^ finrank ℝ W = ((r + lam / 2) / (lam / 2)) ^ finrank ℝ W := by
    congr 1
    field_simp
    ring
  rw [key, div_pow, le_div_iff₀ hpos]
  exact hle'

theorem finrank_span_le_finrank_int {V : Type*} [AddCommGroup V] [Module ℝ V]
    (La : Submodule ℤ V) [Module.Finite ℤ La] :
    (La : Set V) ⊆ Submodule.span ℝ (La : Set V) ∧
      FiniteDimensional ℝ (Submodule.span ℝ (La : Set V)) ∧
      finrank ℝ (Submodule.span ℝ (La : Set V)) ≤ finrank ℤ La := by
  classical
  have : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree ℝ V
  have : IsAddTorsionFree V := inferInstance
  have : Module.IsTorsionFree ℤ La := inferInstance
  have : Module.Free ℤ La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ La
  let f : Module.Free.ChooseBasisIndex ℤ La → V := fun i => (B i : V)
  have hspan : Submodule.span ℝ (La : Set V) = Submodule.span ℝ (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      have hx'' : x = ∑ i, B.repr ⟨x, hx⟩ i • f i := by
        conv_lhs => rw [show x = ((⟨x, hx⟩ : La) : V) from rfl, ← B.sum_repr ⟨x, hx⟩]
        simp only [Submodule.coe_sum, Submodule.coe_smul, f]
      rw [SetLike.mem_coe, hx'']
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (B i).2
  refine ⟨Submodule.subset_span, ?_, ?_⟩
  · rw [hspan]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  · rw [hspan, finrank_eq_card_basis B]
    exact finrank_range_le_card f

theorem Packing.proof : Packing.Statement := by
  classical
  intro V _ _ La _ S b hb hmem hnorm hsep
  obtain ⟨hsub, hfd, hdim⟩ := finrank_span_le_finrank_int La
  set W := Submodule.span ℝ (La : Set V) with hW
  have hR0 : (0 : ℝ) ≤ Module.finrank ℤ La * (b + Real.log 3) := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact hR0
  let T : Finset W := S.subtype (· ∈ W)
  have hTcard : T.card = S.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    exact fun s hs => hsub (hmem s hs)
  have hδ : 0 < Real.exp (-b) := Real.exp_pos _
  have hbound := card_le_of_separated_of_norm_le T hδ zero_le_one
    (fun x hx => by
      rw [Finset.mem_subtype] at hx
      rw [Submodule.coe_norm]; exact hnorm _ hx)
    (fun x hx y hy hxy => by
      rw [Finset.mem_subtype] at hx hy
      rw [Submodule.coe_norm, Submodule.coe_sub]
      exact hsep _ hx _ hy (fun h => hxy (Subtype.ext h)))
  rw [hTcard] at hbound
  have hq : 1 + 2 * 1 / Real.exp (-b) ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    rw [Real.exp_neg, mul_one, div_inv_eq_mul]
    linarith
  have h3 : 1 ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    linarith
  have hcard : (S.card : ℝ) ≤ (3 * Real.exp b) ^ Module.finrank ℤ La :=
    hbound.trans ((pow_le_pow_left₀ (by positivity) hq _).trans (pow_le_pow_right₀ h3 hdim))
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hpos
  calc Real.log S.card ≤ Real.log ((3 * Real.exp b) ^ Module.finrank ℤ La) :=
        Real.log_le_log hSpos hcard
    _ = Module.finrank ℤ La * (b + Real.log 3) := by
        rw [Real.log_pow, Real.log_mul (by norm_num) (Real.exp_pos b).ne', Real.log_exp]
        ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HasDerivAtDet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix Equiv
open scoped ComplexOrder

noncomputable section

theorem LogDetDerivative.hasDerivAt_det {m : ℕ} {G : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {G' : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : ∀ i j, HasDerivAt (fun s ↦ G s i j) (G' i j) t) :
    HasDerivAt (fun s ↦ (G s).det) (∑ i, (G t).cramer (fun k ↦ G' k i) i) t := by
  have key : ∀ σ : Perm (Fin m), HasDerivAt (fun s ↦ ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i)
      (((Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) * G' (σ i) i) t := by
    intro σ
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s ↦ G s (σ i) i)
      (f' := fun i ↦ G' (σ i) i) (x := t) (fun i _ ↦ h (σ i) i)
    simpa [smul_eq_mul] using this.const_mul ((Perm.sign σ : ℤ) : ℂ)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ key σ)
  have hfun : (fun s ↦ (G s).det) =
      fun s ↦ ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i := by
    ext s
    exact det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl fun i _ ↦ cramer_apply (G t) (fun k ↦ G' k i) i]
  simp only [det_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (G t).updateCol i (fun k ↦ G' k i) (σ j) j =
      ∏ j ∈ Finset.univ.erase i, G t (σ j) j := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, updateCol_self]
  ring

theorem LogDetDerivative.sum_cramer_eq {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) :
    ∑ i, A.cramer (fun k ↦ B k i) i = A.det * (A⁻¹ * B).trace := by
  simp only [← det_smul_inv_mulVec_eq_cramer A _ hA, Pi.smul_apply, smul_eq_mul, trace,
    diag_apply, Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum]

theorem LogDetDerivative.intersectionNumber_baseChange : LogDetDerivative.Statement := by
  intro m G G' hpos hG t
  have hdet := LogDetDerivative.hasDerivAt_det (hG t)
  rw [LogDetDerivative.sum_cramer_eq _ _ (hpos t).det_pos.ne'.isUnit] at hdet
  have hre : HasDerivAt (fun s ↦ (G s).det.re)
      ((G t).det * ((G t)⁻¹ * G' t).trace).re t := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdet
  have hp := (hpos t).det_pos
  rw [Complex.lt_def] at hp
  obtain ⟨hre0, him0⟩ := hp
  simp only [Complex.zero_re, Complex.zero_im] at hre0 him0
  have hlog := (hre.log hre0.ne').const_mul (-(1 / 2) : ℝ)
  refine hlog.congr_deriv ?_
  rw [Complex.mul_re, ← him0, zero_mul, sub_zero]
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]

theorem segreMap_monomial_isMultiHomog (d : ((_ : Unit) × ((k : K) → ι k)) →₀ ℕ) (a : F) :
    IsMultiHomog (segreMap F (monomial d a))
      (fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) := by
  unfold IsMultiHomog
  rw [segreMap, aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine IsWeightedHomogeneous.C_mul ?_ a
  have hX : ∀ v : (_ : Unit) × ((k : K) → ι k),
      IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
    intro v
    have := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => Pi.single k 1)
      (fun k _ => isWeightedHomogeneous_X F _ _)
    convert this using 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := IsWeightedHomogeneous.prod d.support
    (fun v => (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) ^ d v) (fun v => d v • (fun _ : K => (1 : ℕ)))
    (fun v _ => (hX v).pow _)
  have e : (fun _ : K => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) =
      ∑ v ∈ d.support, d v • (fun _ : K => (1 : ℕ)) := by
    ext j
    simp [Finsupp.weight_apply, Finsupp.sum, blockWeight, Finset.sum_apply]
  rw [e]
  exact this

theorem segreMap_weightedHomogeneousComponent [Nonempty K] (b : Unit → ℕ)
    (g : MRing (fun _ : Unit => ∀ k, ι k) F) :
    segreMap F (weightedHomogeneousComponent (blockWeight (fun _ : Unit => ∀ k, ι k)) b g) =
      weightedHomogeneousComponent (blockWeight ι) (fun _ => b ()) (segreMap F g) := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := isWeightedHomogeneous_monomial (blockWeight (fun _ : Unit => ∀ k, ι k)) d a rfl
    rw [weightedHomogeneousComponent_of_mem h1,
      weightedHomogeneousComponent_of_mem (segreMap_monomial_isMultiHomog F d a)]
    have key : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ↔
        (fun _ : K => b ()) = fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d () := by
      constructor
      · rintro rfl; rfl
      · intro h; funext u; cases u; exact congr_fun h (Classical.arbitrary K)
    by_cases h : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d
    · rw [if_pos h, if_pos (key.mp h)]
    · rw [if_neg h, if_neg (mt key.mpr h), map_zero]
  | add p p' hp hp' => simp only [map_add (f := _), hp, hp']

theorem SegrePrime.proof : SegrePrime.Statement := by
  intro F _ K _ _ _ ι _ q hq
  have := hq.isPrime
  refine ⟨segrePrime.isPrime F q, ?_, ?_⟩
  · intro g hg b
    rw [segrePrime, Ideal.mem_comap] at hg ⊢
    rw [segreMap_weightedHomogeneousComponent]
    exact hq.multiHomog _ hg _
  · intro u
    cases u
    choose i hi using hq.relevant
    refine ⟨i, ?_⟩
    rw [segrePrime, Ideal.mem_comap, segreMap_X, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, _, hk⟩
    exact hi k hk

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallBallVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Real Module
open scoped Nat

noncomputable section

theorem pi_pow_div_factorial_le_six (k : ℕ) : π ^ k / (k ! : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 3 ≤ k → π ^ (k + 1) / ((k + 1) ! : ℝ) ≤ π ^ k / (k ! : ℝ) := by
    intro k hk
    have hk' : (4 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k := pow_pos hπ0 k
    nlinarith [mul_pos hp hf]
  have h3 : π ^ 3 / ((3 : ℕ) ! : ℝ) ≤ 6 := by
    norm_num [Nat.factorial]
    nlinarith [sq_nonneg π, mul_pos hπ0 hπ0]
  rcases lt_or_ge k 3 with hk | hk
  · interval_cases k
    · norm_num
    · norm_num; linarith
    · norm_num [Nat.factorial]; nlinarith
  · induction k, hk using Nat.le_induction with
    | base => exact h3
    | succ n hn ih => exact (step n hn).trans ih

theorem pi_pow_mul_two_pow_div_doubleFactorial_le_six (k : ℕ) :
    π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 2 ≤ k → π ^ (k + 1) * 2 ^ (k + 1 + 1) / ((2 * (k + 1) + 1)‼ : ℝ) ≤
      π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) := by
    intro k hk
    have hk' : (7 : ℝ) ≤ 2 * (k : ℝ) + 3 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [he, Nat.doubleFactorial_add_two, Nat.cast_mul, pow_succ, pow_succ (2 : ℝ) (k + 1)]
    have hf : (0 : ℝ) < ((2 * k + 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k * 2 ^ (k + 1) := by positivity
    nlinarith [mul_pos hp hf]
  have h2 : π ^ 2 * 2 ^ (2 + 1) / ((2 * 2 + 1)‼ : ℝ) ≤ 6 := by
    norm_num [Nat.doubleFactorial]
    nlinarith
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · norm_num [Nat.doubleFactorial]
    · norm_num [Nat.doubleFactorial]; linarith
  · induction k, hk using Nat.le_induction with
    | base => exact h2
    | succ n hn ih => exact (step n hn).trans ih

theorem SmallBallVolume.proof : SmallBallVolume.Statement := by
  intro R
  unfold unitBallVolume
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin R)) = R := finrank_euclideanSpace_fin
  rcases Nat.even_or_odd' R with ⟨k, hk | hk⟩
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp only [mul_zero] at hk
      subst hk
      have : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal ≤ 1 := by
        have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1) ≤ 1 := by
          calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)
              ≤ volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := measure_mono (Set.subset_univ _)
            _ = 1 := by
              rw [← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage
                MeasurableSet.univ.nullMeasurableSet, Set.preimage_univ, MeasureTheory.volume_pi,
                Measure.pi_univ]
              simp
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
      linarith
    · have : Nontrivial (EuclideanSpace ℝ (Fin R)) :=
        Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
      rw [InnerProductSpace.volume_ball_of_dim_even (hfin.trans hk), ENNReal.ofReal_one, one_pow,
        one_mul, ENNReal.toReal_ofReal (by positivity)]
      exact pi_pow_div_factorial_le_six k
  · rw [InnerProductSpace.volume_ball_of_dim_odd (hfin.trans hk), ENNReal.ofReal_one, one_pow,
      one_mul, ENNReal.toReal_ofReal (by positivity), hfin, hk]
    exact pi_pow_mul_two_pow_div_doubleFactorial_le_six k

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Cardinal

noncomputable section

theorem SegreDimGe.proof : SegreDimGe.Statement := by
  intro F _ K _ _ _ ι _ q e hq hdim
  have := hq.isPrime
  let π : MRing ι F →ₐ[F] MRing ι F ⧸ q := Ideal.Quotient.mkₐ F q
  let φ : MRing (fun _ : Unit => ∀ k, ι k) F →ₐ[F] MRing ι F ⧸ q := π.comp (segreMap F)
  let R' : Subalgebra F (MRing ι F ⧸ q) := φ.range
  choose i hi using hq.relevant
  let x : K → MRing ι F ⧸ q := fun k => π (X ⟨k, i k⟩)
  have hx0 : ∀ k, x k ≠ 0 := fun k h =>
    hi k (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [x, π, Ideal.Quotient.mkₐ_eq_mk] using h))

  have hkey : ∀ k (j : ι k), (∏ l ∈ Finset.univ.erase k, x l) * π (X ⟨k, j⟩) =
      φ (X ⟨(), Function.update i k j⟩) := by
    intro k j
    rw [AlgHom.comp_apply, segreMap_X, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  let k0 : K := Classical.arbitrary K
  let s : Set (MRing ι F ⧸ q) := x '' ↑(Finset.univ.erase k0)
  let B : Subalgebra R' (MRing ι F ⧸ q) := Algebra.adjoin R' s
  have hR'B : ∀ a ∈ R', IsAlgebraic B a := fun a ha =>
    isAlgebraic_algebraMap (⟨a, Subalgebra.algebraMap_mem B (⟨a, ha⟩ : R')⟩ : B)
  have hsB : ∀ l, l ≠ k0 → IsAlgebraic B (x l) := fun l hl =>
    isAlgebraic_algebraMap (⟨x l, Algebra.subset_adjoin
      ⟨l, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩), rfl⟩⟩ : B)
  have hgen : ∀ k, (∀ l, l ≠ k → IsAlgebraic B (x l)) → ∀ j : ι k, IsAlgebraic B (π (X ⟨k, j⟩)) := by
    intro k hk j
    have hy : IsAlgebraic B (∏ l ∈ Finset.univ.erase k, x l) :=
      Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isAlgebraic_one
        fun l hl => hk l (Finset.ne_of_mem_erase hl)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ?_) hy ?_
    · exact Finset.prod_ne_zero_iff.mpr fun l _ => hx0 l
    · rw [hkey]
      exact hR'B _ ⟨_, rfl⟩
  have hall : ∀ l, IsAlgebraic B (x l) := by
    intro l
    by_cases hl : l = k0
    · subst hl
      exact hgen _ hsB (i _)
    · exact hsB l hl
  have hA : ∀ a : MRing ι F ⧸ q, IsAlgebraic B a := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective F q a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.algHom_C]
      exact hR'B _ (R'.algebraMap_mem c)
    | add p r hp hr => rw [map_add (f := _)]; exact hp.add hr
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hgen v.1 (fun l _ => hall l) v.2)
  have : Algebra.IsAlgebraic B (MRing ι F ⧸ q) := ⟨hA⟩
  have htop : Algebra.trdeg R' (MRing ι F ⧸ q) ≤ #s := Algebra.IsAlgebraic.trdeg_le_cardinalMk R' s
  have hs : #s ≤ (Fintype.card K - 1 : ℕ) := by
    refine Cardinal.mk_image_le.trans ?_
    simp
  have : FaithfulSMul F R' :=
    (faithfulSMul_iff_algebraMap_injective F R').mpr (algebraMap F R').injective
  have : FaithfulSMul R' (MRing ι F ⧸ q) :=
    ⟨fun {r₁ r₂} h => Subtype.ext (by simpa [Subalgebra.smul_def] using h 1)⟩
  have htower := trdeg_add_eq (A := MRing ι F ⧸ q) F R'

  let g : (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) →ₐ[F] R' :=
    Ideal.Quotient.liftₐ (segrePrime F q) φ.rangeRestrict fun p hp => by
      apply Subtype.ext
      simpa [φ, π, segrePrime, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hp
  have hg : Function.Surjective g := by
    rintro ⟨y, p, rfl⟩
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hR'le := trdeg_le_of_surjective g hg
  obtain ⟨n, hn, htn⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing ι F ⧸ q)
  obtain ⟨m, hm, htm⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q)
  have hne : n = e + Fintype.card K := by
    rw [hn] at hdim
    exact_mod_cast hdim
  have hcard : (n : Cardinal) ≤ (m + (Fintype.card K - 1) : ℕ) := by
    rw [← htn, ← htower, Nat.cast_add, ← htm]
    exact add_le_add hR'le (htop.trans hs)
  have hK : 0 < Fintype.card K := Fintype.card_pos
  have hnm : n ≤ m + (Fintype.card K - 1) := by exact_mod_cast hcard
  rw [hm]
  exact_mod_cast (show e + 1 ≤ m by omega)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMinkowskiCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Module Metric
open scoped ENNReal

noncomputable section

namespace MinkowskiCount

section Count

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


omit [MeasurableSpace V] [BorelSpace V] in
theorem finite_latticePoints (La : Submodule ℤ V) [DiscreteTopology La] (ρ : ℝ) :
    {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.Finite := by
  have h : {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} = closedBall 0 ρ ∩ (La : Set V) := by
    ext x; simp [and_comm]
  rw [h]
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

theorem unitBallVolume_pos (R : ℕ) : 0 < unitBallVolume R :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem volume_ball_one :
    volume (ball (0 : V) 1) = ENNReal.ofReal (unitBallVolume (finrank ℝ V)) := by
  rw [unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    ← (stdOrthonormalBasis ℝ V).measurePreserving_repr.measure_preimage
      measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem volume_ball_half_le (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ) {F : Set V}
    (fund : IsAddFundamentalDomain La F volume) :
    volume (ball (0 : V) (ρ / 2)) ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ≥0∞) * volume F := by
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  have : Countable La := inferInstance
  set S := ball (0 : V) (ρ / 2) with hSdef
  set A := {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} with hAdef
  have hS : MeasurableSet S := measurableSet_ball
  have key : ∀ y : V, ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) ≤ (A.ncard : ℝ≥0∞) := by
    intro y
    set T : Set La := {g | (g : V) + y ∈ S} with hTdef
    have h1 : ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, T.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hA : (A.ncard : ℝ≥0∞) = ((A.encard : ℕ∞) : ℝ≥0∞) := by
      rw [← (finite_latticePoints La ρ).cast_ncard_eq]; rfl
    rw [hA]
    refine ENat.toENNReal_le.mpr ?_
    rcases T.eq_empty_or_nonempty with hT | ⟨g₀, hg₀⟩
    · simp [hT]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : V) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hg' : ‖(g : V) + y‖ < ρ / 2 := by simpa [T, S] using hg
      have hg₀' : ‖(g₀ : V) + y‖ < ρ / 2 := by simpa [T, S] using hg₀
      have : (g : V) - g₀ = ((g : V) + y) - ((g₀ : V) + y) := by abel
      show ‖(g : V) - g₀‖ ≤ ρ
      rw [this]
      linarith [norm_sub_le ((g : V) + y) ((g₀ : V) + y)]
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc volume S = ∫⁻ z, S.indicator 1 z := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, (A.ncard : ℝ≥0∞) := lintegral_mono fun z => key z
    _ = A.ncard * volume F := setLIntegral_const _ _

theorem log_count (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ)
    (hρ : 0 < ρ) :
    Real.log (unitBallVolume (finrank ℝ V)) + (finrank ℝ V : ℝ) * Real.log (ρ / 2) -
        Real.log (ZLattice.covolume La) ≤
      Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La volume fund
  have hFtop : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hle := volume_ball_half_le La ρ fund
  rw [Measure.addHaar_ball_of_pos volume 0 (half_pos hρ), volume_ball_one] at hle
  have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFtop) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (unitBallVolume_pos _).le, ENNReal.toReal_natCast, ← measureReal_def,
    ← hcov] at hle'
  have hcpos := ZLattice.covolume_pos La volume
  have hN : 0 < ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
    have : 0 < {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard :=
      (Set.ncard_pos (finite_latticePoints La ρ)).mpr ⟨0, La.zero_mem, by simp [hρ.le]⟩
    exact_mod_cast this
  have hdiv : (ρ / 2) ^ finrank ℝ V * unitBallVolume (finrank ℝ V) / ZLattice.covolume La ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := (div_le_iff₀ hcpos).mpr hle'
  have hlog := Real.log_le_log (by have := unitBallVolume_pos (finrank ℝ V); positivity) hdiv
  rw [Real.log_div (by have := unitBallVolume_pos (finrank ℝ V); positivity) hcpos.ne',
    Real.log_mul (by positivity) (unitBallVolume_pos _).ne', Real.log_pow] at hlog
  linarith

end Count

theorem cube_le_unitBallVolume (R : ℕ) : (2 / Real.sqrt R) ^ R ≤ unitBallVolume R := by
  set a := 1 / Real.sqrt R with ha_def
  have ha : 0 ≤ a := by positivity
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin R) → Fin R → ℝ) ⁻¹'
      (Set.univ.pi fun _ => Set.Ioo (-a) a) ⊆ ball 0 1 := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin R, a ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hR⟩, Finset.mem_univ _⟩ fun i _ => by
              rw [Real.norm_eq_abs, sq_abs]
              exact sq_lt_sq' (hx i).1 (hx i).2
        _ = 1 := by
          have hR' : (0 : ℝ) < R := by exact_mod_cast hR
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha_def,
            div_pow, one_pow, Real.sq_sqrt hR'.le]
          field_simp
  have hvol := measure_mono (μ := volume) hsub
  rw [(PiLp.volume_preserving_ofLp (Fin R)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    at hvol
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hvol
  have h := ENNReal.toReal_mono measure_ball_lt_top.ne hvol
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h
  have h2 : 2 / Real.sqrt R = a + a := by rw [ha_def]; ring
  rw [h2]
  exact h

theorem proof : MinkowskiCount.Statement :=
  ⟨fun _ _ _ _ _ _ La _ _ ρ hρ => log_count La ρ hρ, cube_le_unitBallVolume⟩

end MinkowskiCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (F : Type) [Field F]

theorem weight_blockWeight_apply (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) e k = ∑ i, e ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem blockWeight_unit (v : Σ _ : Unit, ∀ k, ι k) :
    blockWeight (fun _ : Unit => ∀ k, ι k) v = fun _ => 1 := by
  funext u
  simp [blockWeight]


omit [∀ k, Fintype (ι k)] in
theorem segreMap_isMultiHomog {m : ℕ} {p : MRing (fun _ : Unit => ∀ k, ι k) F}
    (hp : IsWeightedHomogeneous (blockWeight (fun _ : Unit => ∀ k, ι k)) p (fun _ => m)) :
    IsWeightedHomogeneous (blockWeight ι) (segreMap F p) (fun _ => m) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q _ _ hp hq => rw [map_add (f := _)]; exact hp.add hq
  | monomial d r hr =>
    have hX : ∀ v : Σ _ : Unit, ∀ k, ι k,
        IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
      intro v
      have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
        (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, v.2 k⟩)
        (fun k _ => isWeightedHomogeneous_X _ _ _)
      convert h using 1
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have hsum : ∑ v ∈ d.support, d v = m := by
      have h := congrFun hr ()
      rw [Finsupp.weight_apply, Finsupp.sum] at h
      simpa [blockWeight_unit, Finset.sum_apply] using h
    have hdeg : (∑ v ∈ d.support, d v • (fun _ : K => 1) : K → ℕ) = fun _ => m := by
      funext k
      simp [Finset.sum_apply, hsum]
    unfold segreMap
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ r
    rw [← hdeg]
    exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hX v).pow _


omit [DecidableEq K] in
theorem monomial_mem_map_segreMap (m : ℕ) :
    ∀ e : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = m) →
      monomial e (1 : F) ∈ (weightedHomogeneousSubmodule F
        (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map (segreMap F).toLinearMap := by
  classical
  induction m with
  | zero =>
    intro e he
    have he0 : e = 0 := by
      ext ⟨k, i⟩
      exact (Finset.sum_eq_zero_iff.mp (he k)) i (Finset.mem_univ _)
    subst he0
    refine ⟨1, ?_, ?_⟩
    · exact isWeightedHomogeneous_one _ _
    · simp
  | succ m ih =>
    intro e he
    have hne : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => e ⟨k, i⟩) (by rw [he k]; omega)
      exact ⟨i, hi⟩
    choose f hf using hne
    set s : (Σ k, ι k) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun v => if v.2 = f v.1 then 1 else 0) with hs_def
    have hs : ∀ k i, s ⟨k, i⟩ = if i = f k then 1 else 0 := fun k i => by simp [hs_def]
    have hse : s ≤ e := by
      rw [Finsupp.le_def]
      rintro ⟨k, i⟩
      rw [hs]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (hf k)
      · exact Nat.zero_le _
    have hadd : e - s + s = e := tsub_add_cancel_of_le hse
    have he' : ∀ k, ∑ i, (e - s) ⟨k, i⟩ = m := fun k => by
      have h1 : ∑ i, (e - s) ⟨k, i⟩ + ∑ i, s ⟨k, i⟩ = m + 1 := by
        rw [← Finset.sum_add_distrib, ← he k]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.add_apply, hadd]
      have h2 : ∑ i, s ⟨k, i⟩ = 1 := by simp [hs]
      omega
    obtain ⟨g, hg, hge⟩ := ih (e - s) he'
    have hsX : monomial s (1 : F) = ∏ k, (X ⟨k, f k⟩ : MRing ι F) := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [hs]
    refine ⟨g * X ⟨(), f⟩, ?_, ?_⟩
    · have h := (show IsWeightedHomogeneous _ g _ from hg).mul
        (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ∀ k, ι k)) ⟨(), f⟩)
      rw [blockWeight_unit] at h
      exact h
    · simp only [AlgHom.toLinearMap_apply, map_mul] at hge ⊢
      rw [hge, segreMap_X, ← hsX, monomial_mul, one_mul, hadd]

theorem map_segreMap_weightedHomogeneousSubmodule (m : ℕ) :
    (weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map
        (segreMap F).toLinearMap =
      weightedHomogeneousSubmodule F (blockWeight ι) (fun _ => m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact segreMap_isMultiHomog F hp
  · intro p hp
    have hp' : IsWeightedHomogeneous (blockWeight ι) p (fun _ => m) := hp
    clear hp
    induction hp' using IsWeightedHomogeneous.induction_on with
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | monomial d r hr =>
      have hd : ∀ k, ∑ i, d ⟨k, i⟩ = m := fun k => by
        rw [← weight_blockWeight_apply, hr]
      have h := Submodule.smul_mem _ r (monomial_mem_map_segreMap F m d hd)
      rwa [smul_monomial, smul_eq_mul, mul_one] at h

def segreQuotMap (q : Ideal (MRing ι F)) :
    MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q →ₐ[F] MRing ι F ⧸ q :=
  Ideal.quotientMapₐ (I := segrePrime F q) q (segreMap F) fun _ h => h


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segreQuotMap_injective (q : Ideal (MRing ι F)) : Function.Injective (segreQuotMap F q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk q (segreMap F x) = 0 at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp ha))

def segreGradedPieceEquiv (q : Ideal (MRing ι F)) (m : ℕ) :
    gradedPiece (segrePrime F q) (fun _ : Unit => m) ≃ₗ[F] gradedPiece q (fun _ : K => m) :=
  have hinj : Function.Injective (segreQuotMap F q).toLinearMap := segreQuotMap_injective F q
  have hmap : (gradedPiece (segrePrime F q) (fun _ : Unit => m)).map (segreQuotMap F q).toLinearMap =
      gradedPiece q (fun _ : K => m) := by
    have hc : (segreQuotMap F q).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (segrePrime F q)).toLinearMap =
        (Ideal.Quotient.mkₐ F q).toLinearMap ∘ₗ (segreMap F).toLinearMap :=
      LinearMap.ext fun _ => rfl
    unfold gradedPiece
    rw [← Submodule.map_comp, hc, Submodule.map_comp, map_segreMap_weightedHomogeneousSubmodule]
  (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ hmap)

theorem SegreHilb.proof : SegreHilb.Statement := by
  intro F _ K _ _ _ ι _ q n
  unfold hilbFn
  by_cases hn : 0 ≤ n
  · rw [if_pos (fun _ => hn), if_pos (fun _ => hn)]
    exact congrArg (fun x : ℕ => (x : ℤ)) (segreGradedPieceEquiv F q n.toNat).finrank_eq
  · rw [if_neg (fun h => hn (h ())), if_neg (fun h => hn (h (Classical.arbitrary K)))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
